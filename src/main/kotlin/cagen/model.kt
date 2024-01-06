package cagen

import cagen.expr.SMVExpr
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
    var globalCode: String? = null
) {
    fun findVariant(text: String) = variants.findVariant(text)
    fun activateVersion(current: List<VV>) = contracts.forEach { it.activateVersion(current) }
    fun findSystemByName(name: String): System? = systems.find { it.name == name }
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

data class Variable(val name: String, val type: Type, val initValue: SMVExpr? = null)

val self = Variable("self", BuiltInType("self"), null)

data class Signature(
    val inputs: MutableList<Variable> = arrayListOf(),
    val outputs: MutableList<Variable> = arrayListOf(),
    val internals: MutableList<Variable> = arrayListOf(),
) {
    fun get(name: String) = all.find { it.name == name }
    fun accessible(name: String) = (inputs + outputs).find { it.name == name }

    val all
        get() = inputs + outputs + internals

    val instances
        get() = internals.filter { it.type is SystemType }

    val plainInternals
        get() = internals.filter { it.type !is SystemType }

    operator fun plus(signature: Signature): Signature = Signature(
        (inputs + signature.inputs).toMutableList(),
        (outputs + signature.outputs).toMutableList(),
        (internals + signature.internals).toMutableList()
    )
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

    val variablesInToporder: List<List<Variable>>
        get() = toporderSystem(ArrayList(signature.instances), ArrayList(connections))

    val toporder: String
        get() = toporder(ArrayList(signature.instances), ArrayList(connections))
}

data class UseContract(val contract: Contract, val variableMap: MutableList<Pair<String, IOPort>>) {
    /**
     * Returns a contract that uses the variable renaming
     */
    fun prefix(prefix: String): UseContract {
        val renamedTransitions = contract.transitions.map {
            it.copy(contract = it.contract.prefix(prefix))
        }
        val c = contract.copy(transitions = renamedTransitions)
        val newMap = variableMap.map { (a, b) -> prefix + a to b }
            .toMutableList()
        return UseContract(c, newMap)
    }
}

private fun PrePost.prefix(prefix: String): PrePost = copy(pre.prefix(prefix), post.prefix(prefix))

data class Contract(
    override val name: String,
    override val signature: Signature,
    val history: List<Pair<String, Int>>,
    val transitions: List<CATransition>,
    val parent: MutableList<UseContract> = arrayListOf()
) : Component {
    var disabledTransitions: List<CATransition> = mutableListOf()
    var activeTransitions: List<CATransition> = mutableListOf()

    fun activateVersion(current: List<VV>) {
        val allTrans = transitions + disabledTransitions
        val t = allTrans.groupBy { it.vvGuard.evaluate(current) }
        activeTransitions = t[true] ?: listOf()
        disabledTransitions = t[false] ?: listOf()
    }

    val contracts
        get() = transitions.map { it.contract }.toSet()
    val states
        get() = transitions.flatMap { listOf(it.from, it.to) }.toSet()

    infix operator fun times(other: Contract): Contract {
        val sig = signature + other.signature
        val his = history + other.history
        val trans = transitions * other.transitions
        return Contract(name + "_" + other.name, sig, his, trans)
    }
}

private operator fun Iterable<CATransition>.times(transitions: Iterable<CATransition>): List<CATransition> =
    flatMap { t ->
        transitions.map { s ->
            val contract = PrePost(
                t.contract.pre and s.contract.pre,
                t.contract.post and s.contract.post,
                "${t.name}_${s.name}_contract"
            )

            CATransition(
                "${t.name}_${s.name}", "${t.from}_${s.from}", "${t.to}_${s.to}",
                t.vvGuard and s.vvGuard,
                contract
            )
        }
    }

val counter = AtomicInteger()

data class PrePost(
    val pre: SMVExpr,
    val post: SMVExpr,
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

private fun toporderSystem(
    remaining: MutableList<Variable>,
    ports: MutableList<Pair<IOPort, IOPort>>
): List<List<Variable>> {
    val incoming = mutableMapOf<Variable, MutableList<Variable>>()
    val results = mutableListOf<List<Variable>>()
    ports.forEach { (i, o) ->
        (incoming.computeIfAbsent(o.variable) { mutableListOf() }).add(i.variable)
    }

    for (i in 0 until remaining.size) {
        val layer = remaining.filter { incoming[it]?.isEmpty() ?: false }
        results.add(layer)

        incoming.forEach { (_, u) -> u.removeAll(layer) }
        remaining.removeAll(layer)
    }
    require(remaining.isEmpty())
    return results
}

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
data class VVGuard(val values: List<VVRange> = listOf()) {
    fun evaluate(current: List<VV>): Boolean {
        if (values.isEmpty()) return true
        return values.all { it.evaluate(current) }
    }

    infix fun and(other: VVGuard): VVGuard {
        return VVGuard(values + other.values)
    }

    companion object {
        val DEFAULT: VVGuard = VVGuard()
    }
}

data class VVRange(val start: VV, val stop: VV) {
    val isSingleton: Boolean
        get() = start == stop

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

data class VariantFamily(val names: MutableList<Variant> = mutableListOf()) {
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

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Variant) return false

        if (name != other.name) return false

        return true
    }

    override fun hashCode(): Int {
        return name.hashCode()
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

data class VariantLattice(val families: MutableList<VariantFamily> = mutableListOf()) {
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