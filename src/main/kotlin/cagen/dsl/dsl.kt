package cagen.dsl

import cagen.*
import cagen.expr.SIntegerLiteral
import cagen.expr.SMVExpr
import cagen.expr.SVariable

fun model(block: ModelLevel.() -> Unit): Model {
    val m = ModelLevel(Model())
    m.block()
    return m.model
}

class ModelLevel(val model: Model) {
    fun contract(name: String = "", block: ContractLevel.() -> Unit): Contract {
        val m = ContractLevel(name)
        m.block()
        val c = m.build()
        model.contracts.add(c)
        return c
    }

    fun system(name: String = "", block: SystemLevel.() -> Unit): System {
        val m = SystemLevel(name)
        m.block()
        val sys = m.build()
        model.systems.add(sys)
        return sys
    }

    inner class SystemLevel(
        var name: String = "",
        override var signature: Signature = Signature(),
        var connections: MutableList<Pair<IOPort, IOPort>> = arrayListOf(),
        var code: String? = "",
        var contracts: MutableList<UseContract> = arrayListOf()
    ) : SignatureLevel {
        fun build(): System {
            return System(name, signature, connections, code, contracts)
        }

        fun connect(a: IOPort, b: IOPort) {
            connections.add(a to b)
        }

        fun connect(a: Var, b: IOPort) = connect(IOPort(self, a.sigVariable.name), b)
        fun connect(a: IOPort, b: Var) = connect(a, IOPort(self, b.sigVariable.name))
        fun connect(a: Var, b: Var) = connect(IOPort(self, a.sigVariable.name), IOPort(self, b.sigVariable.name))

        fun useContract(c: Contract, vararg subst: Pair<String, IOPort>): UseContract =
            useContract(c, subst.toMutableList())

        fun useContract(c: Contract, subst: MutableList<Pair<String, IOPort>>): UseContract {
            val u = UseContract(c, subst)
            contracts.add(u)
            return u
        }

        fun Contract.use(vararg subst: Pair<String, IOPort>) = useContract(this, subst.toMutableList())

        fun Contract.use() = useContract(
            this,
            (signature.inputs + signature.outputs).map {
                it.name to IOPort(self, it.name)
            }.toMutableList()
        )
    }

    class ContractLevel(
        var name: String = "",
        override var signature: Signature = Signature(),
        var history: MutableList<Pair<String, Int>> = arrayListOf(),
        var transitions: MutableList<CATransition> = arrayListOf(),
        var parent: MutableList<UseContract> = arrayListOf()
    ) : SignatureLevel {
        fun build(): Contract = Contract(name, signature, history, transitions, parent)

        fun trans(from: String, to: String, pre: SMVExpr, post: SMVExpr): CATransition {
            val t = CATransition("", from, to, VVGuard.DEFAULT, PrePost(pre, post))
            transitions.add(t)
            return t
        }
    }
}

interface SignatureLevel {
    var signature: Signature

    fun input(type: Type, vararg name: String) = variables(name, type, signature.inputs)
    fun state(type: Type, vararg name: String) = variables(name, type, signature.internals)
    fun state(type: System, vararg name: String): List<Var> = state(SystemType(type), *name)
    fun output(type: Type, vararg name: String) = variables(name, type, signature.outputs)

    fun variables(name: Array<out String>, type: Type, target: MutableList<Variable>): List<Var> {
        val v = name.map { Variable(it, type) }
        target.addAll(v)
        return v.map { Var(it, SVariable(it.name)) }
    }

    fun bool(): BuiltInType = type("bool")
    val bool
        get() = bool()

    fun int(): BuiltInType = type("int")
    val int
        get() = bool()

    fun type(name: String) = BuiltInType(name).also { require(name in KNOWN_BUILT_IN_TYPES) }
}


data class Var(val sigVariable: Variable, val smvVariable: SVariable) {
    val smv get() = smvVariable

    fun port(s: String): IOPort {
        require(sigVariable.type is SystemType)
        val sys = sigVariable.type.system
        val v = sys.signature.accessible(s)
        require(v != null)
        return IOPort(sigVariable, s)
    }

    infix fun and(other: SMVExpr): SMVExpr = smvVariable.and(other)
    infix fun and(other: Var): SMVExpr = and(other.smvVariable)

    infix fun or(other: SMVExpr): SMVExpr = smvVariable.or(other)
    infix fun or(other: Var): SMVExpr = or(other.smvVariable)

    infix fun div(other: SMVExpr): SMVExpr = smvVariable.div(other)
    infix fun div(other: Var): SMVExpr = div(other.smvVariable)

    operator fun times(other: SMVExpr): SMVExpr = smvVariable.times(other)
    operator fun times(other: Var): SMVExpr = times(other.smvVariable)

    operator fun plus(other: SMVExpr): SMVExpr = smvVariable.plus(other)
    operator fun plus(other: Var): SMVExpr = plus(other.smvVariable)

    operator fun minus(other: SMVExpr): SMVExpr = smvVariable.div(other)
    operator fun minus(other: Var): SMVExpr = div(other.smvVariable)
    operator fun unaryMinus(): SMVExpr = smvVariable.negate()
    operator fun not(): SMVExpr = smvVariable.not()
    infix fun lte(other: Int) = smv le SIntegerLiteral(other.toBigInteger())
    infix fun gte(other: Int) = smv ge SIntegerLiteral(other.toBigInteger())
    infix fun lt(other: Int) = smv lt SIntegerLiteral(other.toBigInteger())
    infix fun gt(other: Int) = smv gt SIntegerLiteral(other.toBigInteger())

    infix fun lte(other: SMVExpr) = smv le other
    infix fun gte(other: SMVExpr) = smv ge other
    infix fun lt(other: SMVExpr) = smv lt other
    infix fun gt(other: SMVExpr) = smv gt other

    infix fun lte(other: Var) = smv le other.smv
    infix fun gte(other: Var) = smv ge other.smv
    infix fun lt(other: Var) = smv lt other.smv
    infix fun gt(other: Var) = smv gt other.smv

    infix fun eq(rhs: SMVExpr) = smv eq rhs
    infix fun eq(rhs: Var) = smv eq rhs.smv
}

infix fun Int.lte(i: Var): SMVExpr = this lte i.smv
infix fun Int.gte(i: Var): SMVExpr = this gte i.smv
infix fun Int.gt(i: Var): SMVExpr = this lt i.smv
infix fun Int.lt(i: Var): SMVExpr = this lt i.smv

infix fun Int.lte(i: SMVExpr): SMVExpr = SIntegerLiteral(toBigInteger()) le i
infix fun Int.gte(i: SMVExpr): SMVExpr = SIntegerLiteral(toBigInteger()) ge i
infix fun Int.gt(i: SMVExpr): SMVExpr = SIntegerLiteral(toBigInteger()) gt i
infix fun Int.lt(i: SMVExpr): SMVExpr = SIntegerLiteral(toBigInteger()) lt i


