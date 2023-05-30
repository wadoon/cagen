package cagen

import cagen.parser.SystemDefBaseVisitor
import cagen.parser.SystemDefLexer
import cagen.parser.SystemDefParser
import cagen.parser.SystemDefParser.ConnectionContext
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.atn.ATNConfigSet
import org.antlr.v4.runtime.dfa.DFA
import java.io.File
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*


private val ParserRuleContext.position: String
    get() = "${this.start.tokenSource.sourceName}:${this.start.line}@${this.start.charPositionInLine}"


object ParserFacade {
    private fun lexer(stream: CharStream): SystemDefLexer =
        SystemDefLexer(stream).also { it.addErrorListener(ExceptionalErrorListener()) }

    private fun parser(lexer: Lexer) = SystemDefParser(CommonTokenStream(lexer)).also {
        it.addErrorListener(ExceptionalErrorListener())
    }

    private fun interpret(parser: SystemDefParser): Pair<ArrayList<System>, ArrayList<Contract>> {
        val ctx = parser.model()
        val t = Translator()
        ctx.accept(t)
        return t.systems to t._contracts
    }

    fun loadFile(file: File) = interpret(parser(lexer(CharStreams.fromPath(file.toPath()))))

    private class ExceptionalErrorListener : ANTLRErrorListener {
        override fun syntaxError(
            recognizer: Recognizer<*, *>?,
            offendingSymbol: Any?,
            line: Int,
            charPositionInLine: Int,
            msg: String?,
            e: RecognitionException?
        ) {
            val filename = File((offendingSymbol as Token).tokenSource.sourceName).absolutePath
            throw RuntimeException("Parsing error: in file:/$filename $line:$charPositionInLine at $offendingSymbol, $msg")
        }

        override fun reportAmbiguity(
            recognizer: Parser?,
            dfa: DFA?,
            startIndex: Int,
            stopIndex: Int,
            exact: Boolean,
            ambigAlts: BitSet?,
            configs: ATNConfigSet?
        ) = Unit

        override fun reportAttemptingFullContext(
            recognizer: Parser?,
            dfa: DFA?,
            startIndex: Int,
            stopIndex: Int,
            conflictingAlts: BitSet?,
            configs: ATNConfigSet?
        ) = Unit

        override fun reportContextSensitivity(
            recognizer: Parser?,
            dfa: DFA?,
            startIndex: Int,
            stopIndex: Int,
            prediction: Int,
            configs: ATNConfigSet?
        ) = Unit
    }
}

data class IOPort(val variable: Variable, val portName: String)

private val self = Variable("self", BuiltInType("self"), "")

class Translator : SystemDefBaseVisitor<Unit>() {
    val systems = arrayListOf<System>()
    val _contracts = arrayListOf<Contract>()

    override fun visitModel(ctx: SystemDefParser.ModelContext) {
        ctx.contract().forEach { it.accept(this) }
        ctx.system().forEach { it.accept(this) }
    }


    override fun visitSystem(ctx: SystemDefParser.SystemContext) {
        val signature = parseIo(ctx.io())
        val connections = parseConnections(ctx.connection(), signature, self)
        val contracts = ctx.use_contracts().flatMap {
            it.use_contract().map { uc ->
                UseContract(
                    _contracts.find { c -> c.name == uc.Ident().text }
                        ?: error("Could not find contract ${uc.Ident().text}"),
                    parseSubst(uc.subst(), signature, self))
            }
        }
        systems.add(
            System(
                ctx.Ident().text,
                signature,
                connections,
                cleanCode(ctx.reaction()?.text),
                contracts.toMutableList()
            )
        )
    }

    private fun parseSubst(
        subst: List<SystemDefParser.SubstContext>,
        signature: Signature,
        self: Variable
    ): MutableList<Pair<String, IOPort>> =
        subst.map {
            val local = it.local.text
            val outer = port(it.from, signature, self)
            local to outer
        }.toMutableList()

    private fun parseConnections(
        ctx: List<ConnectionContext>,
        signature: Signature,
        self: Variable
    ) = ctx.flatMap { cc ->
        val from = port(cc.from, signature, self)
        cc.to.map { from to port(it, signature, self) }
    }.toMutableList()

    private fun port(ioportContext: SystemDefParser.IoportContext, signature: Signature, self: Variable) =
        IOPort(
            ioportContext.inst?.let { inst ->
                (signature.all).find { it.name == inst.text }
                    ?: error("Could not find '${inst.text}' in signature $signature")
            } ?: self,
            ioportContext.port.text)

    private fun cleanCode(text: String?): String? =
        text?.substring(2, text.length - 2)

    private fun parseIo(io: List<SystemDefParser.IoContext>): Signature {
        val sig = Signature()
        for (context in io) {
            val list = when {
                context.INPUT() != null -> sig.inputs
                context.OUTPUT() != null -> sig.outputs
                else -> sig.internals
            }
            for (varctx in context.variable()) {
                val typename = varctx.t.text
                val type =
                    if (typename in KNOWN_BUILT_IN_TYPES) BuiltInType(typename)
                    else SystemType(systems.find { it.name == typename }
                        ?: error("Could not find a system with $typename ${varctx.position}"))
                val init = varctx.init?.text ?: "0"
                for (token in varctx.n) list.add(Variable(token.text, type, init))
            }
        }
        return sig
    }

    override fun visitInvariant(ctx: SystemDefParser.InvariantContext) {
        /*contracts.add(
            AGContract(
                ctx.name.text,
                parseIo(ctx.io()),
                parseHistory(ctx.history()),
                ctx.pre.text.trim('"'), ctx.post.text.trim('"')
            ).setParent(ctx.use_contracts())
        )*/
    }

    private fun Contract.setParent(inherit: MutableList<SystemDefParser.Use_contractsContext>): Contract {
        val contracts = inherit.flatMap { seq ->
            seq.use_contract().map { uc ->
                val contract: Contract = (_contracts.find { c -> c.name == uc.Ident().text }
                    ?: error("Could not find contract ${uc.Ident().text}"))
                UseContract(contract, parseSubst(uc.subst(), signature, self))
            }
        }
        parent.addAll(contracts)
        return this
    }

    override fun visitAutomata(ctx: SystemDefParser.AutomataContext) {
        val localcontracts = ctx.prepost().associate {
            it.name.text to PrePost(it.pre.text.trim('"'), it.post.text.trim('"'), it.name.text)
        }

        val transitions = ctx.transition().map {
            val contract =
                if (it.contr != null) localcontracts[it.contr.text]
                else PrePost(
                    it.pre.text.trim('"'), it.post.text.trim('"'),
                    "contract_trans_${it.from.text}_${it.to.text}_${counter.getAndIncrement()}"
                )
            contract ?: error("Could not find contract ${it.contr.text}")
            CATransition("t_${it.start.line}", it.from.text, it.to.text, contract)
        }
        println(transitions)
        _contracts.add(
            Contract(ctx.name.text, parseIo(ctx.io()), parseHistory(ctx.history()), transitions)
                .setParent(ctx.use_contracts())
        )
    }

    private fun parseHistory(history: List<SystemDefParser.HistoryContext>): List<Pair<String, Int>> =
        history.map { it.n.text to it.INT().text.toInt() }


    object ExpressionParser : SystemDefBaseVisitor<SMVExpr>() {
        override fun visitStateExpr(ctx: SystemDefParser.StateExprContext): SMVExpr {
            if (ctx.unaryop != null) {
                return SUnaryExpression(
                    if (ctx.unaryop.getText().equals("!"))
                        SUnaryOperator.NEGATE
                    else
                        SUnaryOperator.MINUS,
                    ctx.stateExpr(0).accept(this) as SMVExpr
                )
            }

            return if (ctx.terminalAtom() != null) {
                ctx.terminalAtom().accept(this) as SMVExpr
            } else SBinaryExpression(
                ctx.stateExpr(0).accept(this) as SMVExpr,
                SBinaryOperator.findBySymbol(ctx.op.getText())!!,
                ctx.stateExpr(1).accept(this) as SMVExpr
            )
        }


        override fun visitParen(ctx: SystemDefParser.ParenContext): SMVExpr {
            return ctx.stateExpr().accept(this) as SMVExpr
        }

        override fun visitSetExpr(ctx: SystemDefParser.SetExprContext): SMVExpr {
            throw IllegalStateException("not supported")
            //        return super.visitSetExpr(ctx);
        }

        override fun visitWordValue(ctx: SystemDefParser.WordValueContext): SMVExpr {
            val p = ctx.text.split("_")
            val gdt = p[0][1] == 's'

            val bits = Integer.parseInt(p[0].substring(3))
            return SWordLiteral(BigInteger(p[1]), SMVWordType(gdt, bits))
        }

        override fun visitCasesExpr(ctx: SystemDefParser.CasesExprContext): SMVExpr {
            val e = SCaseExpression()
            for (a in ctx.caseBranch()) {
                val cond = a.cond.accept(this) as SMVExpr
                val `val` = a.`val`.accept(this) as SMVExpr
                e.add(cond, `val`)
            }
            return e
        }

        override fun visitTrueExpr(ctx: SystemDefParser.TrueExprContext): SLiteral {
            return SLiteral.TRUE
        }

        override fun visitFalseExpr(ctx: SystemDefParser.FalseExprContext): SLiteral {
            return SLiteral.FALSE
        }


        override fun visitFunctionExpr(ctx: SystemDefParser.FunctionExprContext): SMVExpr {
            val exprs = getSMVExprs(ctx)
            return SFunction(ctx.name.text, exprs)
        }

        private fun getSMVExprs(ctx: SystemDefParser.FunctionExprContext): List<SMVExpr> {
            return ctx.stateExpr().map { it.accept(this) as SMVExpr }
        }

        override fun visitCasesExprAtom(ctx: SystemDefParser.CasesExprAtomContext): SMVExpr {
            return super.visitCasesExprAtom(ctx)
        }


        override fun visitArrayAccess(ctx: SystemDefParser.ArrayAccessContext): SMVExpr {
            throw IllegalStateException("not supported")
        }

        override fun visitVariableDotted(ctx: SystemDefParser.VariableDottedContext): SMVExpr {
            throw IllegalStateException("not supported")
        }

        override fun visitIntegerLiteral(ctx: SystemDefParser.IntegerLiteralContext): SMVExpr {
            return SIntegerLiteral(BigInteger(ctx.value.getText()))
        }

        override fun visitFloatLiteral(ctx: SystemDefParser.FloatLiteralContext): SMVExpr {
            return SFloatLiteral(BigDecimal(ctx.value.getText()))
        }

        override fun visitCaseBranch(ctx: SystemDefParser.CaseBranchContext): SMVExpr {
            return super.visitCaseBranch(ctx)
        }
    }
}

/*
object Peg {
val model = Symbol.rule("model") {
    seq {
        val sign = +char('+', '-').orDefault('+')
        val digits = +DIGIT.oneOrMore().joinToString()
        value { (sign.get + digits.get).toInt() }
    }
    include * (contract|system)* EOF;
}
include: 'include' STRING;

contract : automata | invariant;

automata: CONTRACT name=Ident LBRACE
io*
history*
prepost*
transition*
use_contracts*
RBRACE;

prepost: CONTRACT name=Ident ':=' pre=STRING '==>' post=STRING;
transition: from=Ident ARROW to=Ident '::' (contr=Ident| pre=STRING '==>' post=STRING);

invariant: CONTRACT name=Ident LBRACE
io*
history*
pre=STRING '==>' post=STRING
use_contracts*
RBRACE;

system: REACTOR Ident LBRACE
io*
use_contracts*
connection*
reaction?
RBRACE;

connection: from=ioport ARROW
(LPAREN (to+=ioport)+ RPAREN
| to+=ioport)
;
val ioport = rule("ioport") {
    seq {
        val prefix = +(seq {
            val inst = +ident
            +char('.')
            value { inst.get }
        }.optional())
        val port = +ident;
        value { prefix.get.orNull() to port.get }
    }
}


val use_contracts = rule("use_contracts") {
    seq {
        +literal("contract")
        val uc = +use_contract.list()
    }
}

val use_contract = rule("use_contract") {
    seq {
        val n = +ident
        val s = +(seq<Map<String, IOPort>> {
            +literal("[")
            val s = +subst.list(COMMA)
            +literal("]")
            value { s.get }
        }.optional())

        value {
            val contractName = n.get
            val contract: Contract = components.find { it.name == contractName } as? Contract
                ?: error("Could not find a contract with name $contractName")
            val m = s.get.getOrElse {
                val map = mutableMapOf<String, IOPort>()
                //TODO traverse all pairs
                map
            }
            UseContract(contract, m.toList().toMutableList())
        }
    }
}

val components = arrayListOf<Component>()
lateinit var current: Component

val subst = rule("subst") {
    seq {
        val local = +ident
        +literal("<-")
        val from = +ioport
        value {
            val (v, n) = from.get
            val variable = v?.let { current.signature.get(it) } ?: self
            local.get to IOPort(variable, n)
        }
    }
}


val io = Symbol.rule("io") {
    seq {
        val modifier = +(choice(
            literal("input"),
            literal("output"),
            literal("state")
        ))
        val vars = +variable.list()
        value {
            modifier.get to vars.get.flatten()
        }
    }
}

val history = Symbol.rule("history") {
    seq {
        +literal("history")
        val n = +ident
        +char('(')
        val depth = +int
        +char(')')
        value { n.get to depth.get }
    }
}

val variable = Symbol.rule<List<Variable>>("variable") {
    seq {
        val name = +ident.list(separator = char(','), min = 1u)
        +COLON
        val type = ident
        val init = +(seq<String> {
            +literal(":=")
            val s = +StringSym
        })

        value {
            val t = Type()
            val initValue = ""
            name.get.map {
                Variable(it, t, initValue)
            }
        }
    }
}

val COMMA = char(',')
val COLON = char(':')

private val StringSym = Symbol.rule(name = "String", ignoreWS = false) {
    not(char('"'))
        .list(prefix = char('"'), postfix = char('"'))
        .joinToString()
}

private val int = Symbol.rule(name = "int", ignoreWS = false) {
    DIGIT.list(prefix = char('"'), postfix = char('"'))
        .joinToString()
        .mapPe { it.toInt() }
}


val reaction = Symbol.rule("reaction", ignoreWS = false) {
    val start = literal("{=")
    val end = literal("=}")
    not(literal("=}"))
        .list(prefix = start, postfix = end)
        .joinToString()
}


private val ident = Symbol.rule(name = "ident", ignoreWS = true) {
    char('0'..'z')
        .oneOrMore()
        .joinToString()
}
}

 */




