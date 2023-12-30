package cagen.draw

import cagen.*

object Dot {
    const val REFINEMENT_EDGE = ""
    const val INFFLOW_EDGE = ""
    const val LTL_NODE = "shape=record,bgcolor=lightblue"
    const val INPUT_NODE = ""
    const val OUTPUT_NODE = ""

    fun __print_dot_node(name: String, label: String, style: String = "") =
        print("{name} [ label=\"{label}\", {style}]")


    fun __structured_label(instance: String, name: String, inputs: List<Variable>, outputs: List<Variable>): String {
        val label_fn = { v: Variable -> "<{v.name}> {v.name}" }
        val inports = inputs.joinToString("|", transform = label_fn)
        val outports = outputs.joinToString("|", transform = label_fn)
        return "{ { $inports } | $instance\\n $name | { $outports}}"
    }

    fun Component._print_dot(instance: String) {
        __print_dot_node(
            instance,
            __structured_label(instance, name, signature.inputs, signature.outputs),
            nodeDotStyle
        )
    }

    fun Contract.print_dot(instance: String) {
        print("subgraph cluster_$instance  { bgcolor=\"#cccccc\" \nlabel=\"$instance : ${name}\" \n")
        print("subgraph automaton  { rankDir=lr label=\"\" compound=True ")
        val count_state = mutableMapOf<String, Int>()
        val label_state = mutableMapOf<String, String>()
        for (edge in transitions) {
            if (edge.from !in label_state) {
                label_state[edge.from] = "{{" + edge.from
                count_state[edge.from] = 0
            }
            val cur = count_state[edge.from]
            count_state[edge.from] = (count_state[edge.from] ?: 0) + 1
            print("${edge.from}:c$cur -> ${edge.to} [label=\"$cur\"]")
            label_state[edge.from] = label_state[edge.from] +
                    "|<c{cur}>{cur}\\n{escapeDotLabel(edge.pre)}\\n{escapeDotLabel(edge.post)}"
        }

        for ((node, label) in label_state.entries) {
            print("$node [label=\"$label}}\"]")
        }
        print("}")
        print("}")
    }

    /*
@print_dot.when_type(model.ConstantSystem)
fun print_dot(self, instance: model.ConstantSystem) {
    instance = instance or name
    __print_dot_node(instance, constantValue, node_dot_style)
    if use_contract:
    print("{instance} -> {use_contract.contract.name} [ {REFINEMENT_EDGE} ]")
}

@print_dot.when_type(model.FunctionSystem)
fun _(self, instance):
        instance = instance or name
__print_dot_node(instance, display or func, node_dot_style)
if use_contract:
print("{instance} -> {use_contract.contract.name} [ {REFINEMENT_EDGE} ]")
*/

    fun System.print_dot(instance: String? = null) {
        val instname = instance ?: name
        val dotFunc = { v: Variable -> "<{name}>{v.name}" }
        val inports = signature.inputs.joinToString("|", transform = dotFunc)
        val outports = signature.outputs.joinToString("|", transform = dotFunc)

        print("subgraph cluster_$instance  { bgcolor=\"lightyellow\" \nlabel=\"$instance : $name\"")
        val INPUT_NODE = ""
        print("subgraph cluster_input  { rankDir=tb \n label=\"\"")
        for (inp in signature.inputs) {
            print("${inp.name} [$INPUT_NODE]")
        }
        print("}")


        print("subgraph components  { rankDir=lr \n label=\"\" ")
        for (inst in signature.instances)
            (inst.type as SystemType).system.print_dot(inst.name)
        print("}")
        print("subgraph cluster_output { rankDir=tb \n label=\"\"")
        for (inp in signature.outputs)
            print("${inp.name} [$INPUT_NODE]")
        print("}")

        contracts.forEach { c ->
            print("$instance -> ${c.contract.name} [ $REFINEMENT_EDGE ]")
        }
    }

    /*
fun edgeNode(a: Instance, port: String) {
    if (a.system is model.ConstantSystem || a.system is model.FunctionSystem)
        return a.variable
    else
        return if (a.variable == "sel") port else "{a.variable}:{port}"

    for key in connections:
    start = edgeNode(key.fromSystem, key.out_port)
    end = edgeNode(key.toSystem, key.in_port)
    print("%s:e -> %s:w [%s]" % (start, end, INFFLOW_EDGE))
    print("}")
}
*/

    /*fun AGContract.print_dot(instance: String = "") {
        val inst = if (instance == "") name else instance
        print("$inst [ label=\"{{$name|$pre|$post}}\", $LTL_NODE]")
    }*/
}