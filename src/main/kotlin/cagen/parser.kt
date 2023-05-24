package cagen

import cagen.parser.SystemDefBaseVisitor
import cagen.parser.SystemDefLexer
import cagen.parser.SystemDefParser
import cagen.parser.SystemDefParser.ConnectionContext
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.atn.ATNConfigSet
import org.antlr.v4.runtime.dfa.DFA
import java.io.File
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
        return t.systems to t.contracts
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


class Translator : SystemDefBaseVisitor<Unit>() {
    val systems = arrayListOf<System>()
    val contracts = arrayListOf<Contract>()

    override fun visitModel(ctx: SystemDefParser.ModelContext) {
        ctx.contract().forEach { it.accept(this) }
        ctx.system().forEach { it.accept(this) }
    }

    private val self = Variable("self", BuiltInType("self"), "")

    override fun visitSystem(ctx: SystemDefParser.SystemContext) {
        val signature = parseIo(ctx.io())
        val connections = parseConnections(ctx.connection(), signature, self)
        val contracts = ctx.use_contracts().flatMap {
            it.use_contract().map { uc ->
                UseContract(
                    contracts.find { c -> c.name == uc.Ident().text }
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
        contracts.add(
            AGContract(
                ctx.name.text,
                parseIo(ctx.io()), ctx.pre.text.trim('"'), ctx.post.text.trim('"')
            ).setParent(ctx.use_contracts())
        )
    }

    private fun Contract.setParent(inherit: MutableList<SystemDefParser.Use_contractsContext>): Contract {
        val contracts = inherit.flatMap { seq ->
            seq.use_contract().map { uc ->
                UseContract(
                    contracts.find { c -> c.name == uc.Ident().text }
                        ?: error("Could not find contract ${uc.Ident().text}"),
                    parseSubst(uc.subst(), signature, self))
            }
        }
        parent.addAll(contracts)
        return this
    }

    override fun visitAutomata(ctx: SystemDefParser.AutomataContext) {
        val localcontracts = ctx.prepost().associate {
            it.name.text to PrePost(it.pre.text.trim('"'), it.post.text.trim('"'))
                .apply { name = it.name.text }
        }

        val transitions = ctx.transition().map {
            val contract = if (it.contr != null) localcontracts[it.contr.text]
            else PrePost(it.pre.text.trim('"'), it.post.text.trim('"'))
            contract ?: error("Could not find contract ${it.contr.text}")
            CATransition("t_${it.start.line}", it.from.text, it.to.text, contract)
        }

        contracts.add(
            ContractAutomata(ctx.name.text, parseIo(ctx.io()), transitions)
                .setParent(ctx.use_contracts())
        )
    }
}





