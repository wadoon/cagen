package cagen

import cagen.gen.inState
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.writeText


abstract class ProofObligation(val name: String) {
    abstract fun createFiles(folder: Path): List<POTask>
}

class ImplPOInv(val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_fulfills_${contract.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
        require(contract.contract is AGContract && !contract.contract.isLtl)
        val vars = system.signature.all
        val cfile =
            """
                // ProofObligation: $name
                #include <${system.name}.c>
                
                int nondet_int(); 
                bool nondet_bool();

                int main() {
                    ${system.name}_state __state; init_${system.name}(&__state);
                    while(true) {
                        ${system.signature.inputs.joinToString { (v, t) -> "__state.$v = nondet_${t.name}();" }}
                        assume(${contract.contract.pre.inState(vars, "state.")});
                        next_${system.name}(&__state);
                        assert(${contract.contract.post.inState(vars, "state.")});
                    }
                }
            """.trimIndent()
        (folder / "po_$name.c").writeText(cfile)
        return listOf(
            POTask("${name}_cbmc", "cbmc --unwind 10 po_$name.c"),
            POTask("${name}_seahorn", "seahorn --unwind 10 po_$name.c"),
            POTask("${name}_cpachecker", "cpachecker --unwind 10 po_$name.c"),
        )
    }
}

/**
 * Verify the implementation against a contract (inv or contract automata)
 * */
class ImplPOMonitor(val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_fulfills_${contract.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
        val outputFolder = folder / name
        Files.createDirectories(outputFolder)
        val cfile =
            """
                // ProofObligation: $name
                #include <${system.name}.c>
                #include <${contract.contract.name}.c>
                
                int nondet_int(); 
                bool nondet_bool();

                int main() {
                    ${system.name}_state __state; init_${system.name}(&__state);
                    ${contract.contract.name}_state __cstate; init_${contract.contract.name}(&__cstate);
                    while(true) {
                        ${system.signature.inputs.joinToString { (v, t) -> "__state.$v = nondet_${t.name}();" }}
                        next_${system.name}(&__state);
                        ${
                (contract.contract.signature.inputs + contract.contract.signature.outputs)
                    .joinToString { (v, _) ->
                        val n = contract.variableMap.find { it.first == v }?.second?.let {
                            if (it.variable.name == "self") it.portName
                            else "${it.variable.name}.${it.portName}"
                        } ?: v
                        "__cstate.$v = __state.${n}"
                    }
            }
                        next_${contract.contract.name}(&__cstate);
                        assert(__cstate._error_);
                    }
                }
            """.trimIndent()
        (outputFolder / "po_$name.c").writeText(cfile)
        return listOf(POTask(/*"seahorn", "po_$name.c"*/))
        //(outputFolder / "Makefile").writeText(template_env.get_template("Makefile.jinja2"))
    }
}

data class POTask(val taskName: String = "", val command: String = "")

class ComposedValidPO(val system: System) : ProofObligation("PO_${system.name}_composition_valid") {
    override fun createFiles(folder: Path): List<POTask> {
        return listOf()
    }
}

class ComposedRefinedPO(val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_composition_refine") {
    override fun createFiles(folder: Path): List<POTask> {
        val filename = folder / "$name.smv"
        val subContracts = system.signature.instances.map {
            (it.type as SystemType).system.contracts.first()
        }

        filename.writeText(
            "MODULE main" + "\n" +
                    subContracts.joinToString("\n-- --- --\n") { it.contract.toSmv() }
        )

        return listOf(POTask(name, "nuXmv $filename"))
    }
}

class ContractRefinementPO(val contract: Contract, val refined: UseContract) :
    ProofObligation("PO_${contract.name}_refines_${refined.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
        val sub = contract.signature.all
        for (variable in refined.contract.signature.all) {
            if (variable !in sub && variable.name notin refined.variableMap) {
                error("Variable ${variable.name} defined in parent contract '${refined.contract.name}' is not defined in child contract '${contract.name}'")
            }
        }

        val filename = folder / "$name}.smv"
        filename.writeText(
            SmvUtils.refinement(contract, refined) + "\n" + contract.toSmv() + "\n" + refined.contract.toSmv()
        )
        return listOf(POTask(name, "nuXmv $filename"))
    }
}

private infix fun String.notin(map: List<Pair<String, IOPort>>): Boolean = map.find { it.first == this } == null

private fun Contract.toSmv() = when (this) {
    is ContractAutomata -> SmvUtils.toSmv(this)
    is AGContract -> if (isLtl) SmvUtils.ltl_module(name, signature, pre, post)
    else SmvUtils.inv_module(name, signature, pre, post)
}

fun createProofObligations(components: List<Component>): List<ProofObligation> {
    val obligations = mutableListOf<ProofObligation>()
    for (c in components) {
        if (c is Contract) {
            c.parent.forEach {
                obligations.add(ContractRefinementPO(c, it))
            }
        }

        if (c is System) {
            if (c.code != null)
                c.contracts.forEach {
                    if (it.contract is ContractAutomata)
                        obligations.add(ImplPOMonitor(c, it))
                    else
                        obligations.add(ImplPOInv(c, it))
                }
            else {
                c.contracts.forEach {
                    obligations.add(ComposedRefinedPO(c, it))
                }
                obligations.add(ComposedValidPO(c))
            }
        }
    }
    return obligations
}