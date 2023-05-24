package cagen

import java.util.concurrent.atomic.AtomicInteger

val KNOWN_BUILT_IN_TYPES = setOf(
    "int", "int8", "int16", "int32", "int64",
    "uint", "uint8", "uint16", "uint32", "uint64",
    "float", "double", "short", "long", "bool",
)

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
    val toporder: String
        get() = toporder(ArrayList(signature.instances), ArrayList(connections))
}

data class UseContract(val contract: Contract, val variableMap: MutableList<Pair<String, IOPort>>)

sealed interface Contract : Component {
    val parent: MutableList<UseContract>
}

data class AGContract(
    override val name: String, override val signature: Signature,
    val pre: String, val post: String, val isLtl: Boolean = false
) : Contract {
    override var parent: MutableList<UseContract> = arrayListOf()
}

data class ContractAutomata(
    override val name: String,
    override val signature: Signature,
    val transitions: List<CATransition>
) :
    Contract {
    override var parent: MutableList<UseContract> = arrayListOf()
    val contracts
        get() = transitions.map { it.contract }.toSet()
    val states
        get() = transitions.flatMap { listOf(it.from, it.to) }.toSet()
}

val counter = AtomicInteger()

data class PrePost(val pre: String, val post: String) {
    var name: String = "anonymous_${counter.getAndIncrement()}"
}

data class CATransition(
    val name: String,
    val from: String, val to: String,
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