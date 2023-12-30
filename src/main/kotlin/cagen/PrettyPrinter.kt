package cagen

import cagen.expr.CodeWriter
import cagen.modelchecker.toSMVExpr
import java.io.StringWriter
import java.io.Writer

/**
 *
 * @author Alexander Weigl
 * @version 1 (30.12.23)
 */
class PrettyPrinter(writer: Writer = StringWriter()) {
    val out = CodeWriter(writer)
    fun pp(model: Model) {
        // model: include* defines? variants* globalCode=CODE? (contract|system)* EOF;
        printDefines(model.globalDefines)
        pp(model.variants)
        pp(model.globalCode)
        pp(model.contracts)
        pp(model.systems)
    }

    fun pp(variants: VariantLattice) = variants.families.forEach { pp(it) }
    fun pp(it: VariantFamily) {
        out.println("variants ${it.names.joinToString(", ")}")
    }

    fun pp(code: String) = out.print("{= $code =}")

    @JvmName("ppLC")
    fun pp(contracts: MutableList<Contract>) = contracts.forEach { pp(it) }
    fun pp(contract: Contract) {
        out.cblock("contract ${contract.name} {", "}") {
            pp(contract.signature)
            contract.transitions.groupBy { it.vvGuard }.forEach { (a, b) ->
                pp(a)
                pp(b)
            }

            pp(contract.parent)
        }
    }

    @JvmName("ppLS")
    fun pp(systems: MutableList<System>) = systems.forEach { pp(it) }
    fun pp(system: System) {
        out.cblock("reactor ${system.name} {", "}") {
            pp(system.signature)
            pp(system.contracts)
            pp(system.connections)
            system.code?.let { pp(it) }
        }
    }

    @JvmName("ppLT")
    fun pp(transitions: List<CATransition>) {
        transitions.forEach { pp(it) }
    }

    fun pp(t: CATransition) {
        out.println("${t.from} -> ${t.to} :: ${t.contract.pre.toSMVExpr()} / ${t.contract.post.toSMVExpr()}")
    }

    fun pp(vvGuard: VVGuard) {
        //vvguard: '#[' (vvexpr (COMMA? vvexpr)*)?  ']';
        out.println("#[ ${vvGuard.values.joinToString(", ")}]")
    }

    fun pp(signature: Signature) {
        signature.inputs.sortedBy { it.name }.forEach { pp("input", it) }
        signature.outputs.sortedBy { it.name }.forEach { pp("output", it) }
        signature.internals.sortedBy { it.name }.forEach { pp("state", it) }
    }

    fun pp(modifier: String, variable: Variable) {
        out.println("$modifier ${variable.name} : ${variable.type} := ${variable.initValue}")
    }

    @JvmName("ppLU")
    private fun pp(contracts: MutableList<UseContract>) = contracts.forEach { pp(it) }
    fun pp(uc: UseContract) {
        out.println("contract ${uc.contract.name}[${
            uc.variableMap.joinToString(", ") { (a, b) ->
                "$a <= ${pp(b)}"
            }
        }]"
        )
    }

    fun pp(ioPort: IOPort): String = "${ioPort.variable.name}.${ioPort.portName}"

    @JvmName("ppLP")
    private fun pp(connections: MutableList<Pair<IOPort, IOPort>>) = connections.forEach { pp(it) }
    fun pp(connection: Pair<IOPort, IOPort>) {
        val (from, to) = connection
        out.println("${pp(from)} -> ${pp(to)}")
    }

    private fun printDefines(defines: MutableList<Variable>) {
        if (defines.isNotEmpty()) {
            out.block("\\defines {") {
                defines.forEach {
                    //variable: n+=Ident (COMMA n+=Ident)* COLON t=Ident (':=' init=STRING)?;
                    if (it.initValue.isNotBlank()) {
                        printf("%s : %s", it.name, it.type)
                    } else {
                        printf("%s : %s", it.name, it.type, it.initValue)
                    }
                }
            }
        }
    }
}