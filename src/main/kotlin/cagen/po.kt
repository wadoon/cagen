package cagen

import cagen.gen.CCodeUtils
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.writeText


abstract class ProofObligation(val name: String) {
    abstract fun createFiles(folder: Path): List<POTask>
}

/*class ImplPOInv(val system: System, val useContract: UseContract) :
    ProofObligation("PO_${system.name}_fulfills_${useContract.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
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
                        assume(${useContract.contract.pre.inState(vars, "state.")});
                        next_${system.name}(&__state);
                        assert(${useContract.contract.post.inState(vars, "state.")});
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
}*/

/**
 * Verify the implementation against a contract (inv or contract automata)
 * */
class ImplPOMonitor(val system: System, val contract: UseContract) :
    ProofObligation("PO_${system.name}_fulfills_${contract.contract.name}") {
    override fun createFiles(folder: Path): List<POTask> {
        val outputFolder = folder / name
        Files.createDirectories(outputFolder)

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

private fun System.toC(): String = buildString {
    append("struct ${name}_state {  ${signature.all.joinToString("\n") { "${it.type.toC()} ${it.name};" }}};")
    append("""
        void init_${name}(${name}_state* s) { 
        s = {${
        signature.all.filter { it.initValue.isNotBlank() }.joinToString(", ") {
            ".${it.name} = ${it.initValue.toCValue()}"
        }
    }};} """)

    append("""
        void next_${name}(${name}_state* s) {
         ${
        (signature.all).joinToString("\n") {
            "${it.type.toC()} ${it.name} = s->${it.name};"
        }
    }
        ${code ?: ""}
        ${
        (signature.all).joinToString("\n") {
            "s->${it.name} = ${it.name};"
        }
    }
    }"""
    )
}

fun Type.toC(): String = name

private fun String.toCValue() = when (this) {
    "TRUE" -> 1
    "FALSE" -> 0
    else -> when {
        startsWith("0") -> this.substringAfter("_")
        else -> this
    }
}

private fun Contract.toC(): String = buildString {
    append(
        """
        struct ${name}_state {  
        ${signature.all.joinToString("\n") { "${it.type.toC()} ${it.name};" }}
        ${states.joinToString("\n") { "bool $it;" }}
        bool _error_, _final_,  _assume_;
        
        ${
            history.forEach { (n, d) ->
                val t = signature.get(n)?.type?.toC()
                (0..d).joinToString("\n") { "$t h_${n}_$it;" }
            }
        }        
        };"""
    )

    append("""
        void init_${name}(${name}_state* s) { 
        s = {._error_=false, ._final_=false,  ._assume_=false,
        ${
        states.joinToString(", ") {
            ".${name} = ${if (name.first().isLowerCase()) "true" else "false"}"
        }
    }};
    }""")



    append("void next_${name}(${name}_state* s) {")
    append(
        (signature.all).joinToString("\n") {
            "${it.type.toC()} ${it.name} = s->${it.name};"
        })
    append(
        history.forEach { (n, d) ->
            val t = signature.get(n)?.type?.toC()
            (d downTo 1).joinToString("\n") { "h_${n}_$it = h_${n}_${it - 1};" } +
                    "h_${n}_0 = $n;"
        }
    )

    fun assignb(v: String, e: String) = "bool $v = ${e.toCExpr()};"

    append("""
    STATE_IN_NEXT := ( ${states.joinToString(" | ") { "next($it)" }} );
    ${
        contracts.joinToString("\n") {
            assignb("pre_${it.name}", it.pre) + assignb("post_${it.name}", it.post)

            "post_${it.name} := ${it.post};\n" +
                    "${it.name} := pre_${it.name} & post_${it.name};\n"
        }
    }
    ${transitions.joinToString("\n") { "${it.name} := ${it.from} & ${it.contract.name};" }}
    bool VALID_PRE_COND := ${transitions.joinToString(" | ") { "(${it.from} & pre_${it.contract.name})" }};
    bool VALID_POST_COND := ${transitions.joinToString(" | ") { "(${it.from} & post_${it.contract.name})" }};
         
    ${
        transitions.groupBy { it.to }.toList().joinToString("\n") { (s, inc) ->
            "s->$s) := ${inc.joinToString(" | ") { it.name }};"
        }
    }
 
    s->_error_ = ! STATE_IN_NEXT    & VALID_PRE_COND;
    s->_assume_ = ! STATE_IN_NEXT  & ! VALID_PRE_COND;
    """.trimIndent()
    )

    append((signature.all).joinToString("\n") {
        "s->${it.name} = ${it.name};"
    })
    append("}")
}

fun String.toCExpr(): String {
    return this.replace("0sd32_", "")
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
                error(
                    "Variable ${variable.name} defined in parent contract '${refined.contract.name}'" +
                            " is not defined in child contract '${contract.name}'"
                )
            }
        }

        val filename = folder / "$name.smv"

        filename.writeText(
            SmvUtils.refinement(contract, refined) + "\n----\n"
                    + contract.toSmv() + "\n----\n"
                    + refined.contract.toSmv() + "\n----\n"
                    + createHistoryModules(contract, refined.contract)
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

    private fun createHistoryModules(vararg seq: Contract): String = buildString {
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
            "next(_${it}) := _${it - 1};"
        }

        return """
            MODULE History_${type.name}_$depth(input) 
            VAR $vars
            DEFINE _0 := input;
            ASSIGN
            $assigns
        """.trimIndent()
    }
}

private infix fun String.notin(map: List<Pair<String, IOPort>>): Boolean = map.find { it.first == this } == null

private fun Contract.toSmv() = SmvUtils.toSmv(this)

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
                    obligations.add(ImplPOMonitor(c, it))
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