/* *****************************************************************
 * This file belongs to cagen (https://github.com/wadoon/cagen).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
@file:Suppress("MemberVisibilityCanBePrivate")

package cagen

import cagen.expr.*
import cagen.parser.SystemDefBaseVisitor
import cagen.parser.SystemDefLexer
import cagen.parser.SystemDefParser
import cagen.parser.SystemDefParser.*
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

    private fun interpret(parser: SystemDefParser): Model {
        val ctx = parser.model()
        val t = Translator()
        ctx.accept(t)
        return t.model
    }

    fun loadFile(file: File) = loadFile(CharStreams.fromPath(file.toPath()))
    fun loadFile(stream: CharStream): Model = interpret(parser(lexer(stream)))

    fun parseExpr(content: String): SMVExpr = parseExpr(CharStreams.fromString(content))

    fun parseExpr(content: CharStream): SMVExpr = interpretExpr(parser(lexer(content)))

    private fun interpretExpr(parser: SystemDefParser): SMVExpr {
        val expr = parser.expr()
        return expr.accept(Translator.ExpressionParser)
    }

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
            throw RuntimeException(
                "Parsing error: in file:/$filename $line:$charPositionInLine at $offendingSymbol, $msg"
            )
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
    val model = Model()
    private var vvGuard: VVGuard = VVGuard.DEFAULT

    override fun visitModel(ctx: ModelContext) {
        model.globalCode = ctx.globalCode?.text?.let { cleanCode(it) }
        ctx.defines()?.variable()?.forEach { varctx ->
            val typename = varctx.t.text
            val type =
                if (typename in KNOWN_BUILT_IN_TYPES) {
                    BuiltInType(typename)
                } else {
                    SystemType(
                        model.systems.find { it.name == typename }
                            ?: error("Could not find a system with $typename ${varctx.position}")
                    )
                }
            val init = varctx.init?.asExpr()
            for (token in varctx.n) model.globalDefines.add(Variable(token.text, type, init))
        }
        ctx.variants().forEach { it.accept(this) }
        ctx.contract().forEach { it.accept(this) }
        ctx.system().forEach { it.accept(this) }
    }

    //region version and variants
    override fun visitVariants(ctx: VariantsContext) {
        val vf = VariantFamily()
        ctx.ident().forEach { vf.add(it.text) }
        model.variants.add(vf)
    }

    fun version(ctx: VersionContext): Version = Version(ctx.text)

    override fun visitVvguard(ctx: VvguardContext) {
        vvGuard =
            if (ctx.vvexpr().isEmpty()) {
                VVGuard.DEFAULT
            } else {
                VVGuard(ctx.vvexpr().map { vvexpr(it) })
            }
    }

    fun vvexpr(ctx: VvexprContext): VVRange {
        val a = versionOrVariant(ctx.vv(0)) ?: error("Could not find variant ${ctx.vv(0).text}")
        return if (ctx.vv().size == 1) {
            VVRange(a)
        } else {
            val b = versionOrVariant(ctx.vv(1)) ?: error("Could not find variant ${ctx.vv(1).text}")
            VVRange(a, b)
        }
    }

    fun versionOrVariant(vv: VvContext) = if (vv.version() != null) {
        version(vv.version())
    } else {
        model.findVariant(vv.text)
    }
    // end region

    override fun visitSystem(ctx: SystemContext) {
        val signature = parseIo(ctx.io())
        val connections = parseConnections(ctx.connection(), signature, self)
        val contracts = ctx.use_contracts().flatMap {
            it.use_contract().map { uc ->
                UseContract(
                    model.contracts.find { c -> c.name == uc.ident().text }
                        ?: error("Could not find contract ${uc.ident().text}"),
                    parseSubst(uc.subst(), signature, self)
                )
            }
        }
        model.systems.add(
            System(
                ctx.ident().text,
                signature,
                connections,
                cleanCode(ctx.reaction()?.text),
                contracts.toMutableList()
            )
        )
    }

    private fun parseSubst(
        subst: List<SubstContext>,
        signature: Signature,
        self: Variable
    ): MutableList<Pair<String, IOPort>> = if (subst.isNotEmpty()) {
        subst.map {
            val local = it.local.text
            val outer = port(it.from, signature, self)
            local to outer
        }.toMutableList()
    } else {
        (signature.inputs + signature.outputs).map {
            it.name to IOPort(self, it.name)
        }.toMutableList()
    }

    private fun parseConnections(ctx: List<ConnectionContext>, signature: Signature, self: Variable) =
        ctx.flatMap { cc ->
            val from = port(cc.from, signature, self)
            cc.to.map { from to port(it, signature, self) }
        }.toMutableList()

    private fun port(ioportContext: IoportContext, signature: Signature, self: Variable) = IOPort(
        ioportContext.inst?.let { inst ->
            if (inst.text == "self") {
                self
            } else {
                (signature.all).find { it.name == inst.text }
                    ?: error("Could not find '${inst.text}' in signature $signature")
            }
        } ?: self,
        ioportContext.port.text
    )

    private fun cleanCode(text: String?): String? = text?.substring(2, text.length - 2)

    private fun parseIo(io: List<IoContext>): Signature {
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
                    if (typename in KNOWN_BUILT_IN_TYPES) {
                        BuiltInType(typename)
                    } else {
                        SystemType(
                            model.systems.find { it.name == typename }
                                ?: error("Could not find a system with $typename ${varctx.position}")
                        )
                    }
                val init = varctx.init?.asExpr()
                for (token in varctx.n) list.add(Variable(token.text, type, init))
            }
        }
        return sig
    }

    /*override fun visitInvariant(ctx: InvariantContext) {
        /*contracts.add(
            AGContract(
                ctx.name.text,
                parseIo(ctx.io()),
                parseHistory(ctx.history()),
                ctx.pre.text.trim('"'), ctx.post.text.trim('"')
            ).setParent(ctx.use_contracts())
        )*/
    }*/

    private fun Contract.setParent(inherit: MutableList<Use_contractsContext>): Contract {
        val contracts = inherit.flatMap { seq ->
            seq.use_contract().map { uc ->
                val contract: Contract = (
                    model.contracts.find { c -> c.name == uc.ident().text }
                        ?: error("Could not find contract ${uc.ident().text}")
                    )
                UseContract(contract, parseSubst(uc.subst(), signature, self))
            }
        }
        parent.addAll(contracts)
        return this
    }

    override fun visitAutomata(ctx: AutomataContext) {
        val localcontracts = ctx.prepost().associate {
            it.name.text to PrePost(
                it.pre.asExpr(),
                it.post.asExpr(),
                it.name.text
            )
        }

        val transitions = ctx.transition().map {
            it.vvguard()?.accept(this)

            val contract =
                if (it.contr != null) {
                    localcontracts[it.contr.text]
                } else {
                    PrePost(
                        it.pre.asExpr(),
                        it.post.asExpr(),
                        "contract_trans_${it.from.text}_${it.to.text}_${PrePost.counter.getAndIncrement()}"
                    )
                }
            contract ?: error("Could not find contract ${it.contr.text}")
            CATransition("t_${it.start.line}", it.from.text, it.to.text, vvGuard, contract)
        }
        model.contracts.add(
            Contract(ctx.name.text, parseIo(ctx.io()), parseHistory(ctx.history()), transitions)
                .setParent(ctx.use_contracts())
        )
    }

    private fun parseHistory(history: List<HistoryContext>): List<Pair<String, Int>> =
        history.map { it.n.text to it.INT().text.toInt() }

    private fun ExprContext.asExpr() = this.accept(ExpressionParser)

    object ExpressionParser : SystemDefBaseVisitor<SMVExpr>() {
        override fun visitExpr(ctx: ExprContext): SMVExpr {
            if (ctx.unaryop != null) {
                return SUnaryExpression(
                    if (ctx.unaryop.type == NOT) {
                        SUnaryOperator.NEGATE
                    } else {
                        SUnaryOperator.MINUS
                    },
                    ctx.expr(0).accept(this) as SMVExpr
                )
            }

            return when {
                ctx.terminalAtom() != null ->
                    ctx.terminalAtom().accept(this) as SMVExpr

                ctx.QUESTION_MARK() != null ->
                    SCaseExpression(
                        mutableListOf(
                            SCaseExpression.Case(
                                ctx.expr(0).accept(this) as SMVExpr,
                                ctx.expr(1).accept(this) as SMVExpr
                            ),
                            SCaseExpression.Case(
                                SLiteral.TRUE,
                                ctx.expr(2).accept(this) as SMVExpr
                            )
                        )
                    )

                else -> SBinaryExpression(
                    ctx.expr(0).accept(this) as SMVExpr,
                    SBinaryOperator.findBySymbol(ctx.op.text)!!,
                    ctx.expr(1).accept(this) as SMVExpr
                )
            }
        }

        override fun visitVariablewithprefix(ctx: VariablewithprefixContext): SMVExpr {
            var variable: SMVExpr = SVariable(ctx.ident().text)

            for (varprefix in ctx.varprefix()) {
                when (varprefix) {
                    is ArrayaccessContext -> variable = SArrayAccess(variable, varprefix.index.accept(this))
                    is FieldaccessContext -> variable = SFieldAccess(variable, SVariable(varprefix.dotted.text))
                }
            }

            return variable
        }

        override fun visitParen(ctx: ParenContext): SMVExpr = ctx.expr().accept(this)

        override fun visitWordValue(ctx: WordValueContext): SMVExpr {
            val p = ctx.text.split("_")
            val gdt = p[0][1] == 's'

            val bits = Integer.parseInt(p[0].substring(3))
            return SWordLiteral(BigInteger(p[1]), SMVWordType(gdt, bits))
        }

        override fun visitCasesExpr(ctx: CasesExprContext): SMVExpr {
            val e = SCaseExpression()
            for (a in ctx.caseBranch()) {
                val cond = a.cond.accept(this) as SMVExpr
                val `val` = a.`val`.accept(this) as SMVExpr
                e.add(cond, `val`)
            }
            return e
        }

        override fun visitTrueExpr(ctx: TrueExprContext): SLiteral = SLiteral.TRUE

        override fun visitFalseExpr(ctx: FalseExprContext): SLiteral = SLiteral.FALSE

        override fun visitFunctionExpr(ctx: FunctionExprContext): SMVExpr {
            val exprs = getSMVExprs(ctx)
            return SFunction(ctx.name.text, exprs)
        }

        private fun getSMVExprs(ctx: FunctionExprContext): List<SMVExpr> = ctx.expr().map { it.accept(this) }

        override fun visitCasesExprAtom(ctx: CasesExprAtomContext): SMVExpr = super.visitCasesExprAtom(ctx)

        override fun visitFieldaccess(ctx: FieldaccessContext): SMVExpr = super.visitFieldaccess(ctx)

        override fun visitArrayaccess(ctx: ArrayaccessContext): SMVExpr = super.visitArrayaccess(ctx)

        override fun visitIntegerLiteral(ctx: IntegerLiteralContext): SMVExpr =
            SIntegerLiteral(BigInteger(ctx.value.text))

        override fun visitFloatLiteral(ctx: FloatLiteralContext): SMVExpr = SFloatLiteral(BigDecimal(ctx.value.text))

        override fun visitCaseBranch(ctx: CaseBranchContext): SMVExpr = super.visitCaseBranch(ctx)
    }
}