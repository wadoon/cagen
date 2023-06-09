package cagen

import cagen.cagen.gen.CCodeUtilsSimplified
import cagen.gen.CCodeUtils
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.bufferedWriter
import kotlin.io.path.div
import kotlin.io.path.writeText


abstract class ProofObligation(val name: String) {
    abstract fun createFiles(folder: Path): List<POTask>
}


/**
 * Verify the implementation against a contract (inv or contract automata)
 * */
class ImplPOMonitor(val model: Model, val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_fulfills_${contract.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
        val outputFolder = folder / name
        Files.createDirectories(outputFolder)

        CCodeUtils.writeGlobals(folder, model.globalDefines, model.globalCode)
        CCodeUtils.writeContractAutomata(contract.contract, outputFolder)
        CCodeUtils.writeSystemCode(system, outputFolder)
        CCodeUtils.writeGlueCode(system, contract, outputFolder / "$name.c")

        return listOf(
            POTask("${name}_cbmc", "cbmc --unwind 10 $name.c"),
            POTask("${name}_seahorn", "seahorn --unwind 10 $name.c"),
            POTask("${name}_cpachecker", "cpachecker --unwind 10 $name.c")
        )
    }
}

class ImplPOMonitorSimplified(val model: Model, val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_fulfills_${contract.contract.name}_simple") {
    override fun createFiles(folder: Path): List<POTask> {
        val outputFile = folder / "$name.c"
        Files.createDirectories(outputFile.parent)

        PrintWriter(outputFile.bufferedWriter()).use { out ->
            CCodeUtilsSimplified.header(out, model)
            CCodeUtilsSimplified.writeContractAutomata(contract.contract, out)
            CCodeUtilsSimplified.writeSystemCode(system, out)
            CCodeUtilsSimplified.writeGlueCode(system, contract, out)
        }
        return listOf(
            POTask("${name}_cbmc", "cbmc --unwind 10 $name.c"),
            POTask("${name}_seahorn", "seahorn --unwind 10 $name.c"),
            POTask("${name}_cpachecker", "cpachecker --unwind 10 $name.c")
        )
    }
}

data class POTask(val taskName: String = "", val command: String = "")


class ValidityPO(val model: Model, val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_composition_refine") {
    override fun createFiles(folder: Path): List<POTask> {
        val contracts = listOf(contract.contract) +
                system.signature.instances.map { (it.type as SystemType).system.contracts.first().contract }

        val filename = folder / "$name.smv"

        filename.writeText(
            SmvUtils.toSmv(model, system, contract)
                    + "\n----\n" + SmvUtils.toSmv(model, contract.contract) + "\n----\n"
                    + "\n----\n" + createHistoryModules(contracts)
        )

        filename.parent.resolve("ic3.xmv").writeText(
            """
            set default_trace_plugin 1
            set traces_show_defines_with_next 1

            read_model 
            flatten_hierarchy
            show_vars
            encode_variables
            build_boolean_model
            check_invar_ic3 -v 5
            quit
        """.trimIndent()
        )

        return listOf(POTask(name, "nuXmv -source ic3.xmv ${filename.fileName}"))
    }

}


fun createHistoryModules(vararg seq: Contract): String = createHistoryModules(seq.toList())
fun createHistoryModules(seq: Iterable<Contract>): String = buildString {
    val generated = setOf<String>()
    seq.forEach { c ->
        c.history.forEach { h ->
            val depth = h.second
            val type = c.signature.get(h.first)!!.type
            val key = "History_${type.name}_$depth"
            if (key !in generated) {
                append(createHistoryModule(depth, type))
            }
        }
    }
}


private fun createHistoryModule(depth: Int, type: Type): String {
    require(depth > 0) { "History length should be positive." }

    val vars = (1..depth).joinToString("\n") {
        "_$it : ${type.asSmvType};"
    }

    val assigns = (1..depth).joinToString("\n") {
        "init(_${it}) := 0sd32_0;\nnext(_${it}) := _${it - 1};"
    }

    return """
            MODULE History_${type.name}_$depth(input) 
            VAR $vars
            DEFINE _0 := input;
            ASSIGN
            $assigns
        """.trimIndent()
}


class ContractRefinementPO(val model: Model, val contract: Contract, val refined: UseContract) :
    ProofObligation("PO_${contract.name}_refines_${refined.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
        val sub = contract.signature.all
        for (variable in refined.contract.signature.all) {
            if (variable !in sub && variable.name notin refined.variableMap) {
                error(
                    "Variable ${variable.name} defined in parent contract '${refined.contract.name}'" + " is not defined in child contract '${contract.name}'"
                )
            }
        }

        val filename = folder / "$name.smv"

        filename.writeText(
            SmvUtils.refinement(
                contract,
                refined
            ) + "\n----\n" + SmvUtils.toSmv(model, contract) + "\n----\n"
                    + SmvUtils.toSmv(model, refined.contract) + "\n----\n" + createHistoryModules(
                contract,
                refined.contract
            )
        )

        filename.parent.resolve("ic3.xmv").writeText(
            """
            set default_trace_plugin 1
            set traces_show_defines_with_next 1

            read_model 
            flatten_hierarchy
            show_vars
            encode_variables
            build_boolean_model
            check_invar_ic3 -v 5
            quit
        """.trimIndent()
        )

        return listOf(POTask(name, "nuXmv -source ic3.xmv ${filename.fileName}"))
    }
}

private infix fun String.notin(map: List<Pair<String, IOPort>>): Boolean = map.find { it.first == this } == null


fun createProofObligations(model: Model): List<ProofObligation> {
    val obligations = mutableListOf<ProofObligation>()
    model.contracts.forEach { c ->
        c.parent.forEach {
            obligations.add(ContractRefinementPO(model, c, it))
        }
    }

    for (c in model.systems) {
        if (c.code != null) c.contracts.forEach {
            obligations.add(ImplPOMonitor(model, c, it))
            obligations.add(ImplPOMonitorSimplified(model, c, it))
        }
        else {
            c.contracts.forEach {
                obligations.add(ValidityPO(model, c, it))
            }
        }
    }
    return obligations
}