@file:Suppress("unused", "unused", "UNUSED_VARIABLE")

package cagen.expr

import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import java.util.regex.Pattern


/**
 * Defines an SMV operator by name and precedence.
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
interface SOperator {
    fun symbol(): String
    fun precedence(): Int
}

/**
 * @author Alexander Weigl
 * @version 1 (09.04.18)
 */
sealed class SMVAst {
    fun repr(): String = SMVPrinter.toString(this)
    abstract fun <T> accept(visitor: SMVAstVisitor<T>): T
    abstract fun clone(): SMVAst
}

data class SAssignment(
    var target: SVariable,
    var expr: SMVExpr
) : SMVAst() {
    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone() = copy()
}

data class SBinaryExpression(
    var left: SMVExpr,
    var operator: SBinaryOperator,
    var right: SMVExpr
) : SMVExpr() {


    override val dataType: SMVType?
        get() = SMVTypes.infer(operator, left.dataType, right.dataType)

    override fun prefix(prefix: String): SBinaryExpression {
        return SBinaryExpression(
            left.prefix(prefix),
            operator, right.prefix(prefix)
        )
    }

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone() = SBinaryExpression(left.clone(), operator, right.clone())
}

operator fun SMVExpr.contains(e: SBinaryExpression): Boolean {
    class Find(val target: SMVExpr) : SMVAstDefaultVisitorNN<Unit>() {
        var found: Boolean = false

        override fun defaultVisit(top: SMVAst) {
            found = found || top == target
        }
    }

    val f = Find(e)
    this.accept(f)
    return f.found
}


data class SCaseExpression(var cases: MutableList<Case> = arrayListOf()) : SMVExpr() {
    override val dataType: SMVType?
        get() {
            val list = cases.map { a: Case -> a.then.dataType!! }
            return SMVTypes.infer(list)
        }

    fun add(condition: SMVExpr, value: SMVExpr) {
        cases.add(Case(condition, value))
    }

    fun compress(): SMVExpr {
        // if all cases have the same value then finish
        if (cases.size == 0) return this
        val firstCase = cases[0]
        val b = cases.stream().allMatch { aCase -> firstCase.then == aCase.then }
        if (b)
            return firstCase.then
        //
        val esac = SCaseExpression()
        var previous = firstCase
        var condition = previous.condition

        for (i in 1 until cases.size) {
            val current = cases[i]
            if (previous.then == current.then) {
                condition = condition.or(current.condition)
            } else {
                esac.addCase(condition, previous.then)
                previous = current
                condition = current.condition
            }
        }
        esac.addCase(condition, previous.then)
        return esac
    }

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun prefix(prefix: String): SCaseExpression {
        val sCaseExpression = SCaseExpression()
        for (c in cases) {
            sCaseExpression.add(c.condition.prefix(prefix), c.then.prefix(prefix))
        }
        return sCaseExpression
    }

    fun addCase(cond: SMVExpr, `var`: SMVExpr): Case {
        val c = Case(cond, `var`)
        cases.add(c)
        return c
    }

    data class Case(
        var condition: SMVExpr,
        var then: SMVExpr
    ) {
        fun clone(): Case = Case(condition.clone(), then.clone())
    }

    override fun clone() = SCaseExpression(cases.map { it.clone() }.toMutableList())
}


/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
data class SFunction(
    val name: String,
    var arguments: List<SMVExpr>
) : SMVExpr() {
    private var typeSolver: FunctionTypeSolver? = null

    override val dataType: SMVType?
        get() = typeSolver?.invoke(this)

    constructor(funcName: String, vararg expr: SMVExpr) :
            this(funcName, listOf(*expr))

    override fun clone() = SFunction(name, arguments.map { it.clone() })

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun prefix(prefix: String): SFunction {
        return SFunction(name,
            arguments.map { a -> a.prefix(prefix) })
    }
}

fun ite(cond: SMVExpr, then: SMVExpr, otherwise: SMVExpr) = SCaseExpression().apply {
    add(cond, then)
    add(SLiteral.TRUE, otherwise)
}

sealed class SLiteral(open val value: Any, override val dataType: SMVType) : SMVExpr() {
    override fun <T> accept(visitor: SMVAstVisitor<T>): T = visitor.visit(this)

    abstract override fun clone(): SLiteral

    companion object {
        @JvmStatic
        val TRUE = SBooleanLiteral(true)

        @JvmStatic
        val FALSE = SBooleanLiteral(false)

        @JvmStatic
        fun integer(from: Long) = integer(BigInteger.valueOf(from))

        @JvmStatic
        fun integer(from: BigInteger) = SIntegerLiteral(from)

        /*@JvmStatic
        fun create(value: Any) = LiteralBuilder(value)

        class LiteralBuilder(value: Any) {
            private val literal = SLiteral(value)

            fun with(width: Int, signed: Boolean) =
                    with(SMVWordType(signed, width))

            fun withSigned(width: Int) =
                    with(width, true)

            fun withUnsigned(width: Int) =
                    with(width, false)

            fun asBool() = with(SMVTypes.BOOLEAN)

            fun with(type: SMVType): SLiteral {
                literal.dataType = type
                return literal
            }
        }*/
    }
}

data class SIntegerLiteral(override var value: BigInteger) : SLiteral(value, SMVTypes.INT) {
    override fun prefix(prefix: String): SMVExpr = SIntegerLiteral(value)

    override fun clone() = copy()
}

data class SFloatLiteral(override var value: BigDecimal) : SLiteral(value, SMVTypes.FLOAT) {
    override fun prefix(prefix: String): SMVExpr = SFloatLiteral(value)
    override fun clone() = copy()
}

data class SWordLiteral(
    override var value: BigInteger,
    override var dataType: SMVWordType
) : SLiteral(value, dataType) {
    override fun prefix(prefix: String): SMVExpr = SWordLiteral(value, dataType)
    override fun clone() = copy()
}

data class SBooleanLiteral(override var value: Boolean) : SLiteral(value, SMVTypes.BOOLEAN) {
    override fun prefix(prefix: String): SMVExpr = SBooleanLiteral(value)
    override fun clone() = copy()
}

data class SEnumLiteral(
    override var value: String,
    override var dataType: EnumType = SMVTypes.GENERIC_ENUM
) : SLiteral(value, dataType) {
    override fun prefix(prefix: String): SMVExpr = SEnumLiteral(value)
    override fun clone() = copy()
}

// Use with caution!
data class SGenericLiteral(
    override var value: Any,
    override var dataType: SMVType
) : SLiteral(value, dataType) {
    init {
        require(dataType.allowedValue(value)) {
            "Value $value is not allowed for $dataType"
        }
    }

    override fun prefix(prefix: String): SMVExpr = SGenericLiteral(value, dataType)
    override fun clone() = copy()
}


abstract class SMVExpr : SMVAst() {
    abstract val dataType: SMVType?

    //region builder methods
    fun eventually(): SQuantified = SQuantified(STemporalOperator.F, this)

    fun globally(): SQuantified = SQuantified(STemporalOperator.G, this)

    operator fun next(): SQuantified = SQuantified(STemporalOperator.X, this)

    fun since(): SQuantified = SQuantified(STemporalOperator.S, this)

    fun once(): SQuantified = SQuantified(STemporalOperator.O, this)

    fun until(other: SMVExpr): SQuantified = SQuantified(STemporalOperator.U, this, other)

    infix fun equal(e: SMVExpr): SBinaryExpression = op(SBinaryOperator.EQUAL, e)

    infix fun and(e: SMVExpr): SBinaryExpression = op(SBinaryOperator.AND, e)

    infix fun or(e: SMVExpr): SBinaryExpression = op(SBinaryOperator.OR, e)

    fun op(o: SBinaryOperator, e: SMVExpr): SBinaryExpression {
        val product = SBinaryExpression(this, o, e)
        product.operator = o
        product.right = e
        return product
    }

    operator fun plus(e: SMVExpr) = op(SBinaryOperator.PLUS, e)
    operator fun div(e: SMVExpr) = op(SBinaryOperator.DIV, e)
    operator fun minus(e: SMVExpr) = op(SBinaryOperator.MINUS, e)
    operator fun times(e: SMVExpr) = op(SBinaryOperator.MUL, e)

    infix fun le(e: SMVExpr) = op(SBinaryOperator.LESS_EQUAL, e)
    infix fun lt(e: SMVExpr) = op(SBinaryOperator.LESS_THAN, e)
    infix fun ge(e: SMVExpr) = op(SBinaryOperator.GREATER_EQUAL, e)
    infix fun gt(e: SMVExpr) = op(SBinaryOperator.GREATER_THAN, e)
    infix fun eq(e: SMVExpr) = op(SBinaryOperator.EQUAL, e)
    infix fun neq(e: SMVExpr) = op(SBinaryOperator.NOT_EQUAL, e)


    operator fun not(): SUnaryExpression = SUnaryExpression(SUnaryOperator.NEGATE, this)

    fun negate(): SUnaryExpression = SUnaryExpression(SUnaryOperator.MINUS, this)

    infix fun implies(e: SMVExpr): SMVExpr = op(SBinaryOperator.IMPL, e)

    /**
     * prefiexed and expression
     */
    fun inModule(module: SVariable): SMVExpr {
        return inModule(module.name)
    }

    fun inModule(module: String) = prefix("$module.")
    abstract fun prefix(prefix: String): SMVExpr

    fun wordConcat(b: SMVExpr): SMVExpr =
        op(SBinaryOperator.WORD_CONCAT, b)

    //fun bitAccess(from: Long, to: Long) = SMVFacade.bitAccess(this, from, to)

    /*operator fun get(range: IntRange): SMVExpr {
        return bitAccess(range.start.toLong(), range.last.toLong())
    }*/

    fun inNext(): SFunction =
        SFunction("next", this)
    //endregion

    abstract override fun clone(): SMVExpr

    fun replaceExhaustive(definitions: Map<out SMVExpr, SMVExpr>): SMVExpr {
        val r = ExpressionReplacerRecur(definitions)
        return accept(r) as SMVExpr
    }
}

operator fun MutableList<SAssignment>.set(eq: SVariable, value: SMVExpr) {
    this.add(SAssignment(eq, value))
}

operator fun MutableList<SAssignment>.get(eq: SVariable): SMVExpr? {
    return this.find { it.target == eq }?.expr
}


data class SMVModule
@JvmOverloads constructor(
    var name: String,
    /**
     *
     */
    var inputVars: MutableList<SVariable> = ArrayList(),
    var moduleParameters: MutableList<SVariable> = ArrayList(),
    /**
     *
     */
    var stateVars: MutableList<SVariable> = ArrayList(),
    /**
     *
     */
    var frozenVars: MutableList<SVariable> = ArrayList(),
    var initAssignments: MutableList<SAssignment> = ArrayList(),
    var invariants: MutableList<SMVExpr> = ArrayList(),
    var invariantSpecs: MutableList<SMVExpr> = ArrayList(),
    var ltlSpec: MutableList<SMVExpr> = ArrayList(),
    var ctlSpec: MutableList<SMVExpr> = ArrayList(),
    var nextAssignments: MutableList<SAssignment> = ArrayList(),
    var transExpr: MutableList<SMVExpr> = ArrayList(),
    var initExpr: MutableList<SMVExpr> = ArrayList(),
    var definitions: MutableList<SAssignment> = ArrayList()
) : SMVAst() {
    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone() = copy()
}

data class SArrayAccess(var expr: SMVExpr, var index: SMVExpr) : SMVExpr() {
    override var dataType: SMVType? = null
    override fun prefix(prefix: String): SMVExpr {
        TODO("Not yet implemented")
    }

    override fun clone(): SMVExpr = copy()
    override fun <T> accept(visitor: SMVAstVisitor<T>): T = visitor.visit(this)
}

data class SFieldAccess(var expr: SMVExpr, var sub: SVariable) : SMVExpr() {
    override var dataType: SMVType? = null
    override fun prefix(prefix: String): SMVExpr {
        TODO("Not yet implemented")
    }

    override fun clone(): SMVExpr = copy()
    override fun <T> accept(visitor: SMVAstVisitor<T>): T = visitor.visit(this)
}

data class SVariable(var name: String) : SMVExpr(), Comparable<SVariable> {
    override var dataType: SMVType? = null

    constructor(n: String, dt: SMVType) : this(n) {
        dataType = dt
    }

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun compareTo(other: SVariable): Int {
        return name.compareTo(other.name)
    }

    /*override fun toString(): String {
        return name
    }*/

    override fun clone() = copy().also { it.dataType = dataType }

    override fun prefix(prefix: String): SVariable {
        return create("$prefix$name").with(dataType)
    }

    infix fun assignTo(expr: SMVExpr) = SAssignment(this, expr)

    class Builder(name: String) {
        internal var v = SVariable(name)

        fun with(type: SMVType?): SVariable {
            v.dataType = type
            return v
        }

        fun with(width: Int, signed: Boolean): SVariable =
            with(SMVWordType(signed, width))

        fun withSigned(width: Int): SVariable =
            with(width, true)

        fun withUnsigned(width: Int): SVariable =
            with(width, false)

        fun asBool(): SVariable {
            return with(SMVTypes.BOOLEAN)
        }
    }

    companion object {
        fun bool(name: String) = Builder(name).asBool()
        fun create(name: String) = Builder(name)
        fun create(fmt: String, vararg values: Any): Builder {
            return create(String.format(fmt, *values))
        }
    }
}


/*
 * The order of parsing precedence for operators from high to low is:
 * 0: [ ] , [ : ]
 * 1: !
 * 2: ::
 * 3: - (unary minus)
 * 4: /
 * 6: mod
 * 7: *
 * 8: + -
 * 9: << >>
 * 10: union
 * 11: in
 * 12: = !=  <  >
 * 13: &
 * 14: | xor xnor
 * 15: (• ? • : •)
 * 16: <->
 * 17: ->
 */
enum class SBinaryOperator(private val symbol: String, private val precedence: Int) : SOperator {
    /**
     *
     */
    PLUS("+", 8),

    /**
     *
     */
    MINUS("-", 8),

    /**
     *
     */
    DIV("/", 4),

    /**
     *
     */
    MUL("*", 6),

    /**
     *
     */
    AND("&", 13),

    /**
     *
     */
    OR("|", 14),

    /**
     *
     */
    LESS_THAN("<", 12),

    /**
     *
     */
    LESS_EQUAL("<=", 12),

    /**
     *
     */
    GREATER_THAN(">", 12),

    /**
     *
     */
    GREATER_EQUAL(">=", 12),

    /**
     *
     */
    XOR("xor", 14),

    /**
     *
     */
    XNOR("xnor", 14),

    /**
     *
     */
    EQUAL("=", 12),

    /**
     *
     */
    IMPL("->", 17),

    /**
     *
     */
    EQUIV("<->", 16),

    /**
     *
     */
    NOT_EQUAL("!=", 12),

    /**
     *
     */
    MOD("mod", 5),

    /**
     *
     */
    SHL("<<", 9),

    /**
     *
     */
    SHR(">>", 9),

    WORD_CONCAT("::", 10);

    override fun precedence(): Int {
        return precedence
    }

    override fun symbol(): String {
        return symbol
    }

    companion object {

        fun findBySymbol(symbol: String): SBinaryOperator? {
            for (op in entries) {
                if (op.symbol.equals(symbol, ignoreCase = true)) {
                    return op
                }
            }
            return null
        }
    }
}


/**
 * @author Alexander Weigl
 * @version 1 (11.06.17)
 */
data class SQuantified(
    var operator: STemporalOperator,
    var quantified: MutableList<SMVExpr> = ArrayList(2)
) : SMVExpr() {

    override val dataType: SMVTypes.BOOLEAN
        get() = SMVTypes.BOOLEAN

    constructor(operator: STemporalOperator, vararg expr: SMVExpr) : this(operator, mutableListOf<SMVExpr>(*expr))

    override fun prefix(prefix: String): SQuantified =
        SQuantified(
            operator,
            ArrayList(quantified.map { a -> a.prefix(prefix) })
        )

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    operator fun set(i: Int, value: SMVExpr): SMVExpr = quantified.set(i, value)
    operator fun get(i: Int) = quantified[i]

    override fun clone() = SQuantified(operator, quantified.map { it.clone() }.toMutableList())

}


/**
 * @author Alexander Weigl
 * @version 1 (11.06.17)
 */
enum class STemporalOperator(
    val language: TemporalLanguage,
    val arity: Int,
    val symbol: String,
    val desc: String
) {
    X(TemporalLanguage.LTL, 1, "X", "NEXT"),
    G(TemporalLanguage.LTL, 1, "G", "GLOBALLY"),
    F(TemporalLanguage.LTL, 1, "F", "FINALLY"),
    Y(TemporalLanguage.LTL, 1, "Y", "YESTERDAY"),
    Z(TemporalLanguage.LTL, 1, "Z", "?"),
    H(TemporalLanguage.LTL, 1, "H", "?"),
    O(TemporalLanguage.LTL, 1, "O", "ONCE"),

    U(TemporalLanguage.LTL, 2, "U", "UNTIL"),
    V(TemporalLanguage.LTL, 2, "V", "RELEASE"),
    S(TemporalLanguage.LTL, 2, "S", "SINCE"),
    T(TemporalLanguage.LTL, 2, "T", "?"),

    AU(TemporalLanguage.CTL, 2, "AU", ""),
    EU(TemporalLanguage.CTL, 2, "EU", ""),

    EG(TemporalLanguage.CTL, 2, "EG", ""),
    EF(TemporalLanguage.CTL, 2, "EF", ""),
    EX(TemporalLanguage.CTL, 2, "EX", ""),
    AG(TemporalLanguage.CTL, 2, "AG", ""),
    AF(TemporalLanguage.CTL, 2, "AF", ""),
    AX(TemporalLanguage.CTL, 2, "AX", "");

    fun arity(): Int {
        return arity
    }

    fun symbol(): String {
        return symbol
    }

    enum class TemporalLanguage {
        LTL, CTL, PSL
    }
}


/**
 *
 */
data class SUnaryExpression(
    /**
     *
     */
    var operator: SUnaryOperator,
    /**
     *
     */
    var expr: SMVExpr
) : SMVExpr() {

    override val dataType: SMVType?
        get() = expr.dataType

    override fun prefix(prefix: String): SUnaryExpression {
        return SUnaryExpression(operator, expr.prefix(prefix))
    }

    override fun clone() = SUnaryExpression(operator, expr.clone())

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    /*override fun toString(): String {
        return operator.symbol() + expr
    }*/
}


/**
 *
 */
enum class SUnaryOperator(private val symbol: String, private val precedence: Int) : SOperator {
    /**
     *
     */
    NEGATE("!", 1),

    /**
     *
     */
    MINUS("-", 3);

    override fun precedence(): Int {
        return precedence
    }

    override fun symbol(): String {
        return symbol
    }

    override fun toString(): String {
        return symbol()
    }
}


interface SMVAstVisitor<out T> {
    fun visit(top: SMVAst): T
    fun visit(v: SVariable): T
    fun visit(be: SBinaryExpression): T
    fun visit(ue: SUnaryExpression): T
    fun visit(l: SLiteral): T
    fun visit(a: SAssignment): T
    fun visit(ce: SCaseExpression): T
    fun visit(smvModule: SMVModule): T
    fun visit(func: SFunction): T
    fun visit(quantified: SQuantified): T
    fun visit(access: SFieldAccess): T
    fun visit(access: SArrayAccess): T

}

/**
 * @author Alexander Weigl
 * @version 1 (12.06.17)
 */
open class SMVAstDefaultVisitor<T> : SMVAstVisitor<T?> {
    protected open fun defaultVisit(top: SMVAst): T? = null
    override fun visit(top: SMVAst): T? = defaultVisit(top)
    override fun visit(v: SVariable): T? = defaultVisit(v)
    override fun visit(be: SBinaryExpression): T? = defaultVisit(be)
    override fun visit(ue: SUnaryExpression): T? = defaultVisit(ue)
    override fun visit(l: SLiteral): T? = defaultVisit(l)
    override fun visit(a: SAssignment): T? = defaultVisit(a)
    override fun visit(ce: SCaseExpression): T? = defaultVisit(ce)
    override fun visit(smvModule: SMVModule): T? = defaultVisit(smvModule)
    override fun visit(func: SFunction): T? = defaultVisit(func)
    override fun visit(quantified: SQuantified): T? = defaultVisit(quantified)
    override fun visit(access: SFieldAccess): T? = defaultVisit(access)
    override fun visit(access: SArrayAccess): T? = defaultVisit(access)
}


abstract class SMVAstDefaultVisitorNN<T> : SMVAstVisitor<T> {
    protected abstract fun defaultVisit(top: SMVAst): T
    override fun visit(top: SMVAst): T = defaultVisit(top)
    override fun visit(v: SVariable): T = defaultVisit(v)
    override fun visit(be: SBinaryExpression): T = defaultVisit(be)
    override fun visit(ue: SUnaryExpression): T = defaultVisit(ue)
    override fun visit(l: SLiteral): T = defaultVisit(l)
    override fun visit(a: SAssignment): T = defaultVisit(a)
    override fun visit(ce: SCaseExpression): T = defaultVisit(ce)
    override fun visit(smvModule: SMVModule): T = defaultVisit(smvModule)
    override fun visit(func: SFunction): T = defaultVisit(func)
    override fun visit(quantified: SQuantified): T = defaultVisit(quantified)
    override fun visit(access: SFieldAccess): T = defaultVisit(access)
    override fun visit(access: SArrayAccess): T = defaultVisit(access)
}


open class SMVAstScanner : SMVAstVisitor<Unit> {
    override fun visit(top: SMVAst) = defaultVisit(top)
    override fun visit(v: SVariable) = defaultVisit(v)
    protected open fun defaultVisit(ast: SMVAst) {}

    override fun visit(be: SBinaryExpression) {
        be.left.accept(this)
        be.right.accept(this)
    }

    override fun visit(ue: SUnaryExpression) {
        ue.expr.accept(this)
    }

    override fun visit(l: SLiteral) = defaultVisit(l)

    override fun visit(a: SAssignment) {
        a.expr.accept(this)
        a.target.accept(this)
    }

    override fun visit(ce: SCaseExpression) {
        for (c in ce.cases) {
            c.condition.accept(this)
            c.then.accept(this)
        }
    }

    override fun visit(smvModule: SMVModule) {
        smvModule.ctlSpec.forEach { it.accept(this) }
        smvModule.ltlSpec.forEach { it.accept(this) }
        smvModule.initAssignments.forEach { it.accept(this) }
        smvModule.initExpr.forEach { it.accept(this) }
        smvModule.definitions.forEach { it.accept(this) }
        smvModule.frozenVars.forEach { it.accept(this) }
        smvModule.inputVars.forEach { it.accept(this) }
        smvModule.stateVars.forEach { it.accept(this) }
        smvModule.invariantSpecs.forEach { it.accept(this) }
        smvModule.invariants.forEach { it.accept(this) }
        smvModule.moduleParameters.forEach { it.accept(this) }
        smvModule.nextAssignments.forEach { it.accept(this) }
        smvModule.transExpr.forEach { it.accept(this) }
    }

    override fun visit(func: SFunction) = defaultVisit(func)
    override fun visit(quantified: SQuantified) {
        quantified.quantified
            .forEach { it.accept(this) }

    }

    override fun visit(access: SArrayAccess) {
        access.expr.accept(this)
        access.index.accept(this)
    }

    override fun visit(access: SFieldAccess) {
        access.expr.accept(this)
        access.sub.accept(this)
    }
}

/**
 */
abstract class SMVAstMutableVisitor : SMVAstVisitor<SMVAst> {
    override fun visit(top: SMVAst) = top
    override fun visit(v: SVariable): SMVExpr = v

    override fun visit(be: SBinaryExpression): SMVExpr {
        be.left = be.left.accept(this) as SMVExpr
        be.right = be.right.accept(this) as SMVExpr
        return be
    }

    override fun visit(ue: SUnaryExpression): SMVExpr {
        ue.expr = ue.expr.accept(this) as SMVExpr
        return ue
    }

    override fun visit(l: SLiteral): SMVExpr = l

    override fun visit(a: SAssignment): SAssignment {
        a.expr = a.expr.accept(this) as SMVExpr
        a.target = a.target.accept(this) as SVariable
        return a
    }

    override fun visit(ce: SCaseExpression): SMVExpr {
        for (c in ce.cases) {
            c.condition = c.condition.accept(this) as SMVExpr
            c.then = c.then.accept(this) as SMVExpr
        }
        return ce
    }

    override fun visit(smvModule: SMVModule): SMVModule {
        smvModule.initAssignments = smvModule.initAssignments.visitAll()
        smvModule.nextAssignments = smvModule.nextAssignments.visitAll()
        smvModule.definitions = smvModule.definitions.visitAll()
        smvModule.ltlSpec = smvModule.ltlSpec.visitAll()
        smvModule.ctlSpec = smvModule.ctlSpec.visitAll()
        smvModule.frozenVars = smvModule.frozenVars.visitAll()
        smvModule.stateVars = smvModule.stateVars.visitAll()
        smvModule.inputVars = smvModule.inputVars.visitAll()
        smvModule.invariants = smvModule.invariants.visitAll()
        smvModule.moduleParameters = smvModule.moduleParameters.visitAll()
        return smvModule
    }

    override fun visit(access: SFieldAccess): SMVAst {
        access.expr = access.expr.accept(this) as SMVExpr
        access.sub = access.sub.accept(this) as SVariable
        return access
    }

    override fun visit(access: SArrayAccess): SMVAst {
        access.expr = access.expr.accept(this) as SMVExpr
        access.index = access.index.accept(this) as SMVExpr
        return access
    }

    override fun visit(func: SFunction): SMVExpr {
        return func
    }

    override fun visit(quantified: SQuantified): SMVExpr {
        quantified.quantified = quantified.quantified
            .map { it.accept(this) as SMVExpr }
            .toMutableList()
        return quantified
    }

    private fun <E : SMVAst> List<E>.visitAll(): MutableList<E> =
        map {
            @Suppress("UNCHECKED_CAST")
            it.accept(this@SMVAstMutableVisitor) as E
        }.toMutableList()
}

class VariableReplacer(val map: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    override fun visit(v: SVariable): SMVExpr {
        return map.getOrDefault(v, v)
    }
}

open class ExpressionReplacer(val assignments: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    private var changed = false
    protected open fun replace(x: SMVExpr): SMVExpr {
        val a = assignments[x]
        return if (a == null)
            super.visit(x) as SMVExpr
        else {
            changed = true
            a
        }
    }

    override fun visit(v: SVariable): SMVExpr = replace(v)
    override fun visit(be: SBinaryExpression) = replace(be)
    override fun visit(ue: SUnaryExpression) = replace(ue)
    override fun visit(l: SLiteral) = replace(l)
    override fun visit(func: SFunction) = replace(func)
    override fun visit(quantified: SQuantified) = replace(quantified)
}

open class SMVAstMutableTraversal(val visitor: SMVAstMutableVisitor) : SMVAstMutableVisitor() {
    override fun visit(top: SMVAst) = top
    override fun visit(v: SVariable): SMVExpr = v

    override fun visit(be: SBinaryExpression): SMVExpr {
        be.left = be.left.accept(visitor) as SMVExpr
        be.right = be.right.accept(visitor) as SMVExpr
        return be
    }

    override fun visit(ue: SUnaryExpression): SMVExpr {
        ue.expr = ue.expr.accept(visitor) as SMVExpr
        return ue
    }

    override fun visit(l: SLiteral): SMVExpr = l

    override fun visit(a: SAssignment): SAssignment {
        a.expr = a.expr.accept(visitor) as SMVExpr
        a.target = a.target.accept(visitor) as SVariable
        return a
    }

    override fun visit(ce: SCaseExpression): SMVExpr {
        for (c in ce.cases) {
            c.condition = c.condition.accept(visitor) as SMVExpr
            c.then = c.then.accept(visitor) as SMVExpr
        }
        return ce
    }

    /*override fun visit(smvModule: SMVModule): SMVModule {
        smvModule.initAssignments = smvModule.initAssignments.visitAll()
        smvModule.nextAssignments = smvModule.nextAssignments.visitAll()
        smvModule.definitions = smvModule.definitions.visitAll()
        smvModule.ltlSpec = smvModule.ltlSpec.visitAll()
        smvModule.ctlSpec = smvModule.ctlSpec.visitAll()
        smvModule.frozenVars = smvModule.frozenVars.visitAll()
        smvModule.stateVars = smvModule.stateVars.visitAll()
        smvModule.inputVars = smvModule.inputVars.visitAll()
        smvModule.invariants = smvModule.invariants.visitAll()
        smvModule.moduleParameters = smvModule.moduleParameters.visitAll()
        return smvModule
    }
*/
    override fun visit(func: SFunction): SMVExpr {
        func.arguments =
            func.arguments.map { it.accept(visitor) as SMVExpr }
                .toMutableList()
        return func
    }

    override fun visit(quantified: SQuantified): SMVExpr {
        quantified.quantified = quantified.quantified
            .map { it.accept(visitor) as SMVExpr }
            .toMutableList()
        return quantified
    }
}

open class ExpressionReplacerRecur(private val assignments: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    private val traversal = SMVAstMutableTraversal(this)
    private var changed: Boolean = false

    private fun replace(x: SMVExpr): SMVExpr {
        var a = x
        do {
            val nxt = assignments[a]
            if (nxt != null) a = nxt
            else break
        } while (true)

        changed = changed || a != x
        return a.accept(traversal) as SMVExpr
    }

    override fun visit(v: SVariable): SMVExpr = replace(v)
    override fun visit(be: SBinaryExpression): SMVExpr = replace(be)
    override fun visit(ue: SUnaryExpression): SMVExpr = replace(ue)
    override fun visit(l: SLiteral): SMVExpr = replace(l)
    override fun visit(func: SFunction): SMVExpr = replace(func)
    override fun visit(quantified: SQuantified): SMVExpr = replace(quantified)
}


/**
 *
 * @author Alexander Weigl
 * @version 1 (09.04.18)
 */

interface SMVType {
    fun format(value: Any): String
    fun read(str: String): Any
    fun valueOf(str: String): SLiteral
    fun repr(): String
    fun allowedValue(obj: Any): Boolean
}

data class SMVWordType(
    val signed: Boolean,
    val width: Int
) : SMVType {

    override fun valueOf(str: String) = SWordLiteral(read(str), this)

    override fun read(str: String): BigInteger {
        val re = Pattern.compile("(?<sign>-)?0(?<t>[su])d(?<w>\\d+)_(?<v>\\d+)")
        val m = re.matcher(str)
        if (m.matches()) {
            val s = m.group("sign")?.let { -1 } ?: 1
            val signed = m.group("t").equals("s")
            val len = m.group("w").toInt()
            val v = m.group("v").toInt() * s
            return v.toBigInteger()
        }
        return BigInteger.ZERO
    }

    override fun repr(): String {
        return String.format(
            "%s word[%d]",
            if (signed) "signed"
            else "unsigned", width
        )
    }

    override fun allowedValue(obj: Any): Boolean {
        return obj is BigInteger
    }

    override fun format(value: Any): String {
        return when (value) {
            is BigInteger ->
                String.format(
                    "%s0%sd%d_%s",
                    if (value.signum() < 0) "-" else "",
                    if (signed) "s" else "u",
                    width,
                    value.abs().toString()
                )

            is Long -> format(BigInteger.valueOf(value))
            is Int -> format(BigInteger.valueOf(value.toLong()))
            else -> error("not implemented for ${value.javaClass}")
        }
    }
}

object SMVTypes {
    val GENERIC_ENUM = EnumType(listOf())

    object INT : SMVType {
        override fun valueOf(str: String): SLiteral = SIntegerLiteral(BigInteger(str))
        override fun format(value: Any): String = value.toString()
        override fun read(str: String): Any = BigInteger(str)
        override fun repr(): String = "int"
        override fun allowedValue(obj: Any): Boolean = obj is BigInteger
    }

    object FLOAT : SMVType {
        override fun valueOf(str: String): SLiteral = SFloatLiteral(BigDecimal(str))
        override fun format(value: Any) = value.toString()
        override fun read(str: String) = BigDecimal(str)
        override fun repr(): String = "real"
        override fun allowedValue(obj: Any): Boolean = obj is BigDecimal
    }

    object BOOLEAN : SMVType {
        override fun valueOf(str: String) = if (str.equals("true", true)) SLiteral.TRUE else SLiteral.FALSE
        override fun format(value: Any): String = value.toString().uppercase(Locale.getDefault())
        override fun read(str: String): Any = str.equals("TRUE", true)
        override fun repr(): String = "boolean"
        override fun allowedValue(obj: Any): Boolean = obj is Boolean
    }

    @JvmStatic
    fun infer(list: List<SMVType>): SMVType? {
        return if (list.stream().allMatch { a -> a == list[0] }) list[0] else null
    }


    @JvmStatic
    fun infer(op: SBinaryOperator, a: SMVType?, b: SMVType?): SMVType? {
        return when (op) {
            SBinaryOperator.AND -> BOOLEAN
            SBinaryOperator.OR -> BOOLEAN
            SBinaryOperator.LESS_THAN -> BOOLEAN
            SBinaryOperator.LESS_EQUAL -> BOOLEAN
            SBinaryOperator.GREATER_THAN -> BOOLEAN
            SBinaryOperator.GREATER_EQUAL -> BOOLEAN
            SBinaryOperator.XOR -> BOOLEAN
            SBinaryOperator.XNOR -> BOOLEAN
            SBinaryOperator.EQUAL -> BOOLEAN
            SBinaryOperator.IMPL -> BOOLEAN
            SBinaryOperator.EQUIV -> BOOLEAN
            SBinaryOperator.NOT_EQUAL -> BOOLEAN
            SBinaryOperator.WORD_CONCAT -> TODO()
            else -> infer(a, b)
        }
    }

    @JvmStatic
    fun infer(a: SMVType?, b: SMVType?): SMVType? {
        return if (a == b) a else null
    }

    @JvmStatic
    fun unsigned(i: Int): SMVWordType {
        return SMVWordType(false, i)
    }

    @JvmStatic
    fun signed(i: Int): SMVWordType {
        return SMVWordType(true, i)
    }
}

data class EnumType(var values: List<String>) : SMVType {
    override fun format(value: Any): String = SMVPrinter.quoted(value.toString())
    override fun read(str: String): String = str
    override fun repr(): String = toString()

    override fun allowedValue(obj: Any): Boolean = obj is String

    override fun valueOf(str: String): SLiteral {
        if (!values.contains(str)) {
            throw IllegalArgumentException()
        }
        return SEnumLiteral(str, this)
    }

    override fun toString(): String {
        return if (values.isEmpty()) "{}"
        else
            values.joinToString(", ", "{", "}") { format(it) }
    }
}

data class ModuleType(
    val moduleName: String, val parameters: List<SMVExpr>
) : SMVType {
    override fun format(value: Any): String = error("not implemented")
    override fun read(str: String): Any = error("not implemented")
    override fun valueOf(str: String): SLiteral = error("not implemented")
    override fun repr(): String = toString()

    override fun allowedValue(obj: Any): Boolean = obj is String

    constructor(name: String, vararg variables: SVariable) :
            this(name, mutableListOf<SVariable>(*variables))

    override fun toString(): String {
        val params = if (parameters.isNotEmpty()) {
            parameters.joinToString(", ") { it.repr() }
        } else ""
        return "${moduleName}($params)"

    }
}


/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
typealias FunctionTypeSolver = (SFunction) -> SMVType?

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
object FunctionTypeSolvers {
    val FIRST_ARGUMENT: FunctionTypeSolver = { it.arguments[0].dataType }
    val LAST_ARGUMENT: FunctionTypeSolver = { it.arguments[it.arguments.size - 1].dataType }

    val TO_SIGNED = { f: SFunction ->
        val (_, width) = FIRST_ARGUMENT(f) as SMVWordType
        SMVWordType(true, width)
    }

    val TO_UNSIGNED = { f: SFunction ->
        val (_, width) = FIRST_ARGUMENT(f) as SMVWordType
        SMVWordType(false, width)
    }

    fun specificType(dt: SMVType): FunctionTypeSolver = { dt }
}


fun Iterable<SMVExpr>.joinToExpr(operator: SBinaryOperator): SMVExpr =
    reduce { a, b -> a.op(operator, b) }

fun Iterable<SMVExpr>.disjunction(): SMVExpr = joinToExpr(SBinaryOperator.OR)
fun Iterable<SMVExpr>.conjunction(): SMVExpr = joinToExpr(SBinaryOperator.AND)

fun Collection<SMVExpr>.joinToExpr(operator: SBinaryOperator = SBinaryOperator.AND, default: SMVExpr? = null): SMVExpr =
    if (isNotEmpty() || default == null) {
        reduce { a, b -> a.op(operator, b) }
    } else {
        default
    }

fun Collection<SMVExpr>.disjunction(default: SMVExpr): SMVExpr =
    joinToExpr(SBinaryOperator.OR, default)

fun Collection<SMVExpr>.conjunction(default: SMVExpr): SMVExpr =
    joinToExpr(SBinaryOperator.AND, default)