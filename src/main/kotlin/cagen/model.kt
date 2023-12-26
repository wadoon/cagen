package cagen

import cagen.cagen.expr.SMVExpr
import java.util.concurrent.atomic.AtomicInteger

val KNOWN_BUILT_IN_TYPES = setOf(
    "int", "int8", "int16", "int32", "int64",
    "uint", "uint8", "uint16", "uint32", "uint64",
    "float", "double", "short", "long", "bool",
)

data class Model(
    val systems: MutableList<System> = arrayListOf(),
    val contracts: MutableList<Contract> = arrayListOf(),
    val globalDefines: MutableList<Variable> = arrayListOf(),
    val variants: VariantLattice = VariantLattice(),
    var globalCode: String = ""
) {
    fun findVariant(text: String) = variants.findVariant(text)

    fun activateVersion(current: List<VV>): Unit {
        contracts.forEach { it.activateVersion(current) }
    }
}


sealed interface Component {
    val name: String
    val signature: Signature
    val nodeDotStyle: String
        get() = ""
}

sealed interface Type {
    val name: String
}

data class BuiltInType(override val name: String) : Type
data class SystemType(val system: System) : Type {
    override val name: String
        get() = system.name
}

data class Variable(val name: String, val type: Type, val initValue: String)

data class Signature(
    val inputs: MutableList<Variable> = arrayListOf(),
    val outputs: MutableList<Variable> = arrayListOf(),
    val internals: MutableList<Variable> = arrayListOf(),
) {
    fun get(name: String) = all.find { it.name == name }

    val all
        get() = inputs + outputs + internals

    val instances
        get() = internals.filter { it.type is SystemType }

    val plainInternals
        get() = internals.filter { it.type !is SystemType }
}

data class System(
    override val name: String,
    override val signature: Signature,
    val connections: MutableList<Pair<IOPort, IOPort>> = arrayListOf(),
    val code: String? = null,
    val contracts: MutableList<UseContract> = arrayListOf()
) : Component {
    val subSystems
        get() = signature.instances.map { (it.type as SystemType).system }

    val subSystemsTrans: List<System>
        get() = listOf(this) + subSystems.flatMap { it.subSystemsTrans }


    val toporder: String
        get() = toporder(ArrayList(signature.instances), ArrayList(connections))
}

data class UseContract(val contract: Contract, val variableMap: MutableList<Pair<String, IOPort>>)

//sealed interface Contract : Component {}

/*data class AGContract(
    override val name: String, override val signature: Signature,
    override val history: List<Pair<String, Int>>,
    val pre: String, val post: String, val isLtl: Boolean = false
) : Contract {
    override var parent: MutableList<UseContract> = arrayListOf()
}*/

data class Contract(
    override val name: String,
    override val signature: Signature,
    val history: List<Pair<String, Int>>,
    var transitions: List<CATransition>,
    val parent: MutableList<UseContract> = arrayListOf()
) : Component {
    fun activateVersion(current: List<VV>) {
        val allTrans = transitions + disabledTransitions
        val t = allTrans.groupBy { it.vvGuard.evaluate(current) }
        transitions = t[true] ?: listOf()
        disabledTransitions = t[false] ?: listOf()
    }

    val contracts
        get() = transitions.map { it.contract }.toSet()
    val states
        get() = transitions.flatMap { listOf(it.from, it.to) }.toSet()

    var disabledTransitions: List<CATransition> = mutableListOf()
}

data class PrePost(
    val pre: /*String*/ SMVExpr,
    val post: /*String*/ SMVExpr,
    var name: String = "anonymous_contract_${counter.getAndIncrement()}"
) {
    companion object {
        val counter = AtomicInteger()
    }
}

data class CATransition(
    val name: String,
    val from: String, val to: String,
    val vvGuard: VVGuard,
    val contract: PrePost
)

private fun toporder(
    remaining: MutableList<Variable>,
    ports: MutableList<Pair<IOPort, IOPort>>
): String {
    if (remaining.isEmpty()) return ""

    val remPorts = ports.filter { it.second.variable in remaining && it.first.variable in remaining }

    // find variable which does not have an incoming edge (ignoring self edges)
    val front = remaining.filter { v ->
        remPorts.all { (_, to) -> to.variable != v }
    }

    if (front.isEmpty() && ports.isNotEmpty())
        error("We have a problem building the topological order. Check for cycles!")

    fun variable(v: IOPort): String =
        if (v.variable.name == "self") "state->${v.portName}"
        else "state->${v.variable.name}.${v.portName}"

    val s = buildString {
        for (variable in front) {
            val incoming = ports.filter { it.second.variable == variable }
            val outgoing = ports.filter { it.first.variable == variable }

            incoming.forEach { (from, to) -> appendLine("${variable(to)} =${variable(from)}") }
            appendLine("// call  ${variable.name} of type ${variable.type.name}")
            appendLine("next_${variable.type.name}(&state->${variable.name});")
            outgoing.forEach { (from, to) -> appendLine("${variable(to)} =${variable(from)}") }
            ports.removeAll(incoming)
            ports.removeAll(outgoing)
        }
    }
    remaining.removeAll(front)
    return s + toporder(remaining, ports)
}

private fun topordersys(
    remaining: MutableList<Variable>,
    ports: MutableList<Pair<IOPort, IOPort>>
): List<Variable> {
    if (remaining.isEmpty()) return listOf()

    val remPorts = ports.filter { it.second.variable in remaining && it.first.variable in remaining }

    // find variable which does not have an incoming edge (ignoring self edges)
    val front = remaining.filter { v ->
        remPorts.all { (_, to) -> to.variable != v }
    }

    if (front.isEmpty() && ports.isNotEmpty())
        error("We have a problem building the topological order. Check for cycles!")

    fun variable(v: IOPort): String =
        if (v.variable.name == "self") "state->${v.portName}"
        else "state->${v.variable.name}.${v.portName}"

    for (variable in front) {
        val incoming = ports.filter { it.second.variable == variable }
        val outgoing = ports.filter { it.first.variable == variable }
        ports.removeAll(incoming)
        ports.removeAll(outgoing)
    }
    remaining.removeAll(front)
    return front + topordersys(remaining, ports)
}

//region
data class VVGuard(val vv: List<VVRange> = listOf()) {
    fun evaluate(current: List<VV>): Boolean {
        if (vv.isEmpty()) return true
        return vv.all { it.evaluate(current) }
    }

    companion object {
        val DEFAULT: VVGuard = VVGuard()
    }
}

data class VVRange(val start: VV, val stop: VV) {
    fun evaluate(current: List<VV>): Boolean = current.any {
        start.lessThanOrEqual(it) && it.lessThanOrEqual(stop)
    }

    constructor(single: VV) : this(single, single)

    init {
        require(start.compareTo(stop)?.let { it <= 0 } ?: false) {
            "Variant $start must be smaller than variant two variant $stop"
        }
    }
}

sealed class VV {
    abstract fun compareTo(other: VV): Int?
    fun lessThanOrEqual(other: VV) = compareTo(other)?.let { it <= 0 } ?: false
}

data class VariantFamily(private val names: MutableList<Variant> = mutableListOf()) {
    constructor(vararg names: String) : this() {
        names.forEach { add(it) }
    }

    fun add(s: String) {
        names.addLast(Variant(this, s))
    }

    fun index(name: Variant): Int = names.indexOf(name)
    operator fun contains(text: String): Boolean = get(text) != null
    fun get(text: String): Variant? = names.find { text == it.name }
}

class Variant(val family: VariantFamily, val name: String) : VV() {
    val value
        get() = family.index(this)

    override fun compareTo(other: VV): Int? =
        when (other) {
            is Variant -> if (family == other.family) value - other.value else null
            is Version -> null
        }
}

data class Version(val number: List<Int>) : VV() {
    constructor(s: String) : this(s.trimStart('v', 'V').split(".").map { it.toInt() })

    init {
        number.forEach { require(it >= 0) }
    }

    operator fun compareTo(other: Version): Int {
        for ((a, b) in number.zip(other.number)) {
            if (a != b) return a - b
        }
        return number.size - other.number.size
    }

    override fun compareTo(other: VV): Int? =
        when (other) {
            is Variant -> null
            is Version -> this.compareTo(other)
        }
}

data class VariantLattice(private val families: MutableList<VariantFamily> = mutableListOf()) {
    fun evaluate(expr: VVGuard, current: List<VV>): Boolean {
        return false
    }

    fun findVariant(text: String): Variant? {
        val families = families.filter { text in it }
        return when {
            families.isEmpty() -> null
            families.size == 1 -> return families.first().get(text)
            else -> error("Find two variant families with the same variant!")
        }
    }

    fun add(vf: VariantFamily) = families.addLast(vf)
}
//endregion