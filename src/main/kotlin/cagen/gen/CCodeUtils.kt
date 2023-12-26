package cagen.gen

import cagen.*
import cagen.cagen.expr.SMVExpr
import cagen.cagen.gen.CCodeUtilsSimplified.toC
import cagen.cagen.gen.CCodeUtilsSimplified.toCExpr
import cagen.cagen.gen.CCodeUtilsSimplified.toCValue
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.writeText

val Variable.isSelf: Boolean
    get() = name == "self"

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
            #include "$name.h"

            void init_$name(${name}_state* state) {
                // Inputs
                ${signature.inputs.joinToString("\n") { "state->${it.name} = ${initValue(it.type)};" }}
                // Outputs
                ${signature.outputs.joinToString("\n") { "state->${it.name} = ${initValue(it.type)};" }}
                // Internals
                ${signature.plainInternals.joinToString("\n") { "state->${it.name} = ${initValue(it.type)};" }}
                ${signature.instances.joinToString("\n") { "init_${it.type.name}(&state->${it.name});" }}
            }

            void next_${name}(${name}_state* state) {
            ${
            if (code != null) {
                signature.all.typesOverwriteWithStage() + "\n" + code + "\n" + signature.all.assignStage()
            } else {
                system.toporder
            }
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
            #include <stdbool.h>            
            #define TRUE true
            #define FALSE false
            
            ${
            signature.instances.map { it.type.name }.toSet()
                .joinToString("\n") { "#include \"$it.h\"" }
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
        println("Write header of $name to $headerFilename")
    }

    private fun writeCode(folder: Path, name: String, code: String) {
        val headerFilename = folder / "${name}.c"
        headerFilename.writeText(code)
        println("Write code of $name to $headerFilename")
    }

    private fun Iterable<Variable>.declvars() = joinToString("\n") { "${it.type.name} ${it.name};" }

    private fun Iterable<Variable>.assignStage(): String = joinToString("\n") { "state->${it.name} = ${it.name};" }

    private fun Iterable<Variable>.typesOverwriteWithStage(): String = joinToString("\n") {
        "${it.type.name} ${it.name} = state->${it.name};"
    }

    fun writeContractAutomata(contract: Contract, folder: Path) {
        writeHeaderFile(contract, folder)
        writeCodeFile(contract, folder)
    }

    fun writeHeaderFile(contract: Contract, folder: Path) {
        val signature = contract.signature
        val name = contract.name
        val content = """
            #pragma once
            
            #include <stdbool.h>
            #define TRUE true
            #define FALSE false
            
            typedef struct ${contract.name}_state {
              ${signature.inputs.declvars()}
              ${signature.outputs.declvars()}
              ${signature.internals.declvars()}
              
              bool ${contract.states.joinToString(", ")};
              bool _error_, _final_, _assume_;
              
                 ${
            contract.history.joinToString("\n") { (n, d) ->
                val t = contract.signature.get(n)?.type?.toC()
                (0..d).joinToString("\n") { "$t h_${n}_$it;" }
            }
        }        
              
              
            } ${contract.name}_state;

            void init_${name}(${name}_state* state);
            void next_${name}(${name}_state* state);           
        """.trimIndent()
        writeHeader(folder, contract.name, content)
    }

    fun writeCodeFile(contract: Contract, folder: Path) {
        val name = contract.name
        val stateVars = contract.signature.inputs + contract.signature.outputs
        val history =
            contract.history.joinToString("\n") { (n, d) ->
                val t = contract.signature.get(n)?.type?.toC()
                (d downTo 1).joinToString("\n") { "state->h_${n}_$it = state->h_${n}_${it - 1}; $t h_${n}_$it =state->h_${n}_$it;" } +
                        "state->h_${n}_0 = state->$n;" + "$t h_${n}_0 = state->$n;"
            }

        val content = """
            #include "${name}.h"
            
            void init_${name}(${name}_state* state) {
                ${contract.states.joinToString("\n") { "state->$it = ${!it.startsWith("init")};" }}
                state->_error_= false;
                state->_final_= false;
                state->_assume_= false;
            };

            void next_${name}(${name}_state *state) {
                bool ALL_PRE_CONDITIONS_VIOLATED = true;
                bool ALL_POST_CONDITIONS_VIOLATED = true;
                bool EXISTS_APPLICABLE_CONTRACT = false;
            
                $history
                           
                ${
            contract.transitions.joinToString("\n") {
                "bool pre_${it.name} = ${it.contract.pre.inState(stateVars)};\n" +
                        "bool post_${it.name} = ${it.contract.post.inState(stateVars)};\n" +
                        "ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_${it.name};\n" +
                        "ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_${it.name};\n" +
                        "EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_${it.name} & post_${it.name});\n"
            }
        }
                ${contract.transitions.incomingList().joinToString("\n") { it.transitionAssignment() }}

                bool STATE_IN_NEXT = !( ${contract.states.joinToString(" | ") { "state->$it" }} );
                state->_error_ = !STATE_IN_NEXT && !ALL_PRE_CONDITIONS_VIOLATED;        
                state->_final_ = false; //        
                state->_assume_ = !STATE_IN_NEXT && ALL_PRE_CONDITIONS_VIOLATED;
                
                }
    """.trimIndent()
        //${contract.states.joinToString("\n") { s -> "state->$s=next_$s;" }}
        writeCode(folder, contract.name, content)
    }

    fun writeGlueCode(system: System, contract: UseContract, outputFile: Path) {
        val cfile =
            """ 
                #include <stdbool.h>
                #define TRUE true
                #define FALSE false
            
                #include <assert.h>
                #include "${contract.contract.name}.c"
                #include "${system.name}.c"

                #ifdef __CPROVER__
                int nondet_int(); 
                bool nondet_bool();
                #else 
                int nondet_int() { int i; return i;}
                bool nondet_bool() { bool b; return b;}
                #endif

                int main() {
                    ${system.name}_state __state; 
                    init_${system.name}(&__state);
                    
                    ${contract.contract.name}_state __cstate; 
                    init_${contract.contract.name}(&__cstate);
                    
                    while(true) {
                        ${system.signature.inputs.joinToString { (v, t) -> "__state.$v = nondet_${t.name}();" }}
                        next_${system.name}(&__state);
                        ${
                contract.variableMap.joinToString("") { (cv, sv) ->
                    val n = applySubst(sv)
                    "__cstate.$cv = __state.${n};"
                }
            }
                        next_${contract.contract.name}(&__cstate);
                        assert(__cstate._error_);
                    }
                }
            """.trimIndent()
        outputFile.writeText(cfile)
    }

    fun applySubst(port: IOPort): String {
        val (sub, name) = port
        return if (sub.isSelf) name else "$sub.$name"
    }

    fun writeGlobals(folder: Path, globalDefines: MutableList<Variable>, globalCode: String) {
        val file = folder / "globals.h"
        file.writeText(
            """
        ${
                globalDefines.joinToString("\n") {
                    "const ${it.type.toC()} ${it.name} = ${it.initValue.toCValue()};"
                }
            }
        $globalCode            
        """.trimIndent()
        )
    }
}

private fun Pair<String, List<CATransition>>.transitionAssignment(): String = buildString {
    val (state, inc) = this@transitionAssignment
    //append("bool next_$state = ")
    append("state->$state = ")
    inc.joinTo(this, " | ") {
        "state->${it.from} & pre_${it.name} & post_${it.name}"
    }
    append(";")
}

internal fun SMVExpr.inState(stateVars: List<Variable>, prefix: String = "state->"): String {
    var result = this.toCExpr()
    stateVars.forEach {
        result = result.replace("\\b${it.name}\\b".toRegex(), "$prefix${it.name}")
    }
    return result
}

private fun List<CATransition>.incomingList(): List<Pair<String, List<CATransition>>> = this.groupBy { it.to }.toList()
