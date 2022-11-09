package cagen.gen

import cagen.*
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.writeText

object CCodeUtils {
    fun writeSystemCode(system: System, folder: Path) {
        writeHeaderFile(system, folder)
        writeCodeFile(system, folder)
    }

    private fun initValue(type: Type): String = when (type) {
        is BuiltInType -> when {
            "int" in type.name || "short" == type.name || "long" in type.name -> "0"
            type.name == "float" || type.name == "double" -> "0.0"
            type.name == "bool" -> "false"
            else -> type.name
        }

        is SystemType -> "${type.name}_state"
    }

    private fun writeCodeFile(system: System, folder: Path) {
        val signature = system.signature
        val name = system.name
        val code = system.code

        val codeContent = """
            #include "$name.h";

            void init_$name(${name}_state* state) {
                // Inputs
                ${signature.inputs.joinToString("\n") { "state->${it.name} = ${initValue(it.type)};" }}
                // Outputs
                ${signature.outputs.joinToString("\n") { "state->${it.name} = ${initValue(it.type)};" }}
                // Internals
                ${signature.plainInternals.joinToString("\n") { "state->${it.name} = ${initValue(it.type)};" }}
                <signature.instances:{v | init_<v.type.name>(&state-><v.name>);}>
            }

            void next_${name}(${name}_state* state) {
            ${
            if (code != null) {
                signature.all.typesOverwriteWithStage() + "\n" + code + "\n" + signature.all.assignStage()
            } else {
                system.toporder
            }
        }
        """.trimIndent()
        val codeFilename = folder / "${system.name}.c"
        codeFilename.writeText(codeContent)
        println("Write code of ${system.name} to $codeFilename")
    }

    private fun writeHeaderFile(system: System, folder: Path) {
        val signature = system.signature
        val name = system.name
        val headerContent = """
            #pragma once
            #include <stdbool>
            ${
            signature.instances.map { it.type.name }.toSet()
                .joinToString("\n") { "#include <$it.h>"; }
        }

            typedef struct ${name}_state {
              // Inputs
              ${signature.inputs.declvars()}
              // Outputs
              ${signature.outputs.declvars()}
              // Internals
              ${signature.internals.declvars()}
            } ${name}_state;

            void init_${name}(${name}_state* state);
            void next_${name}(${name}_state* state);           
        """.trimIndent()
        writeHeader(folder, system.name, headerContent)
    }

    private fun writeHeader(folder: Path, name: String, headerContent: String) {
        val headerFilename = folder / "${name}.h"
        headerFilename.writeText(headerContent)
        println("Write header of ${name} to $headerFilename")
    }

    private fun writeCode(folder: Path, name: String, code: String) {
        val headerFilename = folder / "${name}.c"
        headerFilename.writeText(code)
        println("Write code of ${name} to $headerFilename")
    }

    private fun Iterable<Variable>.declvars() = joinToString { "${it.type.name} ${it.name};" }

    private fun Iterable<Variable>.assignStage(): String = joinToString { "stage->${it.name} = ${it.name};" }

    private fun Iterable<Variable>.typesOverwriteWithStage(): String = joinToString {
        "${it.type.name} ${it.name} = stage->${it.name};"
    }

    fun writeContractAutomata(contract: ContractAutomata, folder: Path) {
        writeHeaderFile(contract, folder)
        writeCodeFile(contract, folder)
    }

    fun writeHeaderFile(contract: ContractAutomata, folder: Path) {
        val signature = contract.signature
        val name = contract.name
        val content = """
            #pragma once
            #include <stdbool>

            typedef struct ${contract.name}_state {
              ${signature.inputs.declvars()}
              ${signature.outputs.declvars()}
              ${signature.internals.declvars()}
              
              bool ${contract.states.joinToString(", ")};
              bool _error_, _final_, _assume_;
            } ${contract.name}_state;

            void init_${name}(${name}_state* state);
            void next_${name}(${name}_state* state);           
        """.trimIndent()
        writeHeader(folder, contract.name, content)
    }

    fun writeCodeFile(contract: ContractAutomata, folder: Path) {
        val name = contract.name
        val stateVars = contract.signature.inputs + contract.signature.outputs
        val content = """
            void init_${name}(${name}_state* state) {
                ${contract.states.joinToString("\n") { "state->$it = ${!it.startsWith("init")};" }}
                state->_error_= false;
                state->_final_= false;
                state->_assume_= false;
            };

            void ${name}_next(${name}_state *state) {
                bool ALL_PRE_CONDITIONS_VIOLATED = true;
                bool ALL_POST_CONDITION_VIOLATED = true;
                bool EXISTS_APPLICABLE_CONTRACT = false;
                           
                ${contract.transitions.joinToString("\n") {
                    "bool pre_${it.name} = ${it.contract.pre.inState(stateVars)};\n"+
                            "bool post_${it.name} = ${it.contract.post.inState(stateVars)};\n"+
                            "ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_{it.name};\n"+
                            "ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_{it.name};\n"+
                            "EXISTS_APPLICABLE_CONTRACT = EXISTS_A_VALID_CONTRACT | (pre_${it.name} & post_${it.name});\n"
                }}
                ${contract.transitions.incomingList().joinToString("\n") { it.transitionAssignment() }}

                bool STATE_IN_NEXT = !( ${contract.states.joinToString(" | ") { "next_$it" }} );
                state->_error_ = !STATE_IN_NEXT && !ALL_PRE_CONDITIONS_VIOLATED;        
                state->_final_ = false; //        
                state->_assume_ = !STATE_IN_NEXT && ALL_PRE_CONDITIONS_VIOLATED;
                ${contract.states.joinToString("\n") { s -> "state->$s=next_$s;" }}
    """.trimIndent()
        writeCode(folder, contract.name, content)
    }
}

private fun Pair<String, List<CATransition>>.transitionAssignment(): String = buildString {
    val (state, inc) = this@transitionAssignment
    append("bool next_$state = ")
    inc.joinTo(this, " | ") {
        "state->${it.from} & pre_${it.name} & post_${it.name}"
    }
    append(";")
}

private fun String.inState(stateVars: List<Variable>): String {
    var result = this
    stateVars.forEach {
        result = result.replace("\\b${it.name}\\b".toRegex(), "state->${it.name}")
    }
    return result
}

private fun List<CATransition>.incomingList(): List<Pair<String, List<CATransition>>> = this.groupBy { it.to }.toList()
