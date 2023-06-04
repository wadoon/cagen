package cagen.cagen.gen

import cagen.Contract
import cagen.System
import cagen.Type
import cagen.UseContract
import cagen.gen.CCodeUtils
import java.io.PrintWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.06.23)
 */
object CCodeUtilsSimplified {
    fun writeContractAutomata(contract: Contract, out: PrintWriter) {
        with(contract) {
            signature.all.forEach {
                out.println("${it.type.toC()} ${it.name};")
            }
            states.forEach { out.println("bool $it;") }
            out.println("bool _error_, _final_,  _assume_;")
            contract.history.forEach { (n, d) ->
                val t = signature.get(n)?.type?.toC()
                (0..d).forEach { out.println("$t h_${n}_$it;") }
            }

            out.println(
                """
                void init_${name}() { 
                    _error_=false; _final_=false; _assume_=false;
                """
            )

            states.forEach { name ->
                out.println("$name = ${if (name.first().isLowerCase()) "true" else "false"};")
            }

            history.forEach { (n, d) ->
                val t = signature.get(n)
                (d downTo 1).forEach {
                    out.println("h_${n}_$it = ${t!!.initValue.toCValue()};")
                }
            }
            out.println("}")

            out.println("void next_${name}() {")
            history.forEach { (n, d) ->
                val t = signature.get(n)?.type?.toC()
                (d downTo 1).forEach {
                    out.println("h_${n}_$it = h_${n}_${it - 1};")
                    out.println("h_${n}_0 = $n;")
                }
            }

            /*states.forEach { name ->
                out.println("_$name = $name;")
            }*/

            fun assignb(v: String, e: String) = out.println("bool $v = ${e.toCExpr()};")


            contracts.forEach {
                assignb("pre_${it.name}", it.pre)
                assignb("post_${it.name}", it.post)
                out.println("bool ${it.name} = pre_${it.name} && post_${it.name};")
            }
            transitions.forEach { out.println("bool ${it.name} = ${it.from} && ${it.contract.name};") }

            out.println("bool VALID_PRE_COND = ${transitions.joinToString(" || ") { "(${it.from} && pre_${it.contract.name})" }};")
            out.println("bool VALID_POST_COND = ${transitions.joinToString(" || ") { "(${it.from} && ${it.name})" }};")

            transitions.groupBy { it.to }.toList().forEach { (s, inc) ->
                out.println("$s = ${inc.joinToString(" || ") { it.name }};")
            }

            out.println("bool STATE_IN_NEXT = ( ${states.joinToString(" || ") { it }});")
            out.println("_error_  =  _error_  || (!STATE_IN_NEXT &&  VALID_PRE_COND);")
            out.println("_assume_ =  _assume_ || (!STATE_IN_NEXT && !VALID_PRE_COND);")
            out.println("}")
        }
    }

    fun writeSystemCode(system: System, out: PrintWriter, prefix: String = "sys_") = with(system) {
        fun append(s: String) = out.println(s)
        signature.all.forEach {
            append("${it.type.toC()} $prefix${it.name};")
        }
        append("void init_$prefix${name}() {")
        signature.all.filter { it.initValue.isNotBlank() }.forEach {
            append("$prefix${it.name} = ${it.initValue.toCValue()};")
        }
        append("}")

        append("void next_$prefix${name}() {");
        signature.all.forEach {
            append("${it.type.toC()} ${it.name} = $prefix${it.name};")
        }
        append(code ?: "")
        signature.all.forEach {
            append("$prefix${it.name} = ${it.name};")
        }
        append("}")
    }

    fun writeGlueCode(system: System, contract: UseContract, out: PrintWriter) = with(system) {
        with(contract) {
            fun append(s: String) = out.println(s)
            append("void main() {")
            append("init_sys_${system.name}();")
            append("init_${contract.contract.name}();")
            append("while(true) {")
            for (input in system.signature.inputs) {
                append("sys_${input.name} = nondet_${input.type.toC()}();")
            }
            append("next_sys_${system.name}();")
            contract.variableMap.forEach { (cv, sv) ->
                val n = CCodeUtils.applySubst(sv)
                append("$cv = sys_${n};")
            }
            append(
                """
                next_${contract.contract.name}();
                #ifdef SEAHORN
                sassert(!_error_);
                #else
                assert(!_error_);
                #endif
                """.trimIndent()
            )
            append("}")
            append("}")
        }
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

    fun String.toCExpr() = this.replace("0sd32_", "")
        .replace("=", "==")
        .replace("&", "&&")
        .replace("|", "||")

    fun header(out: PrintWriter) {
        out.println(
            """
            #include <stdbool.h>
            #include <stdint.h>
            #ifdef SEAHORN
            #include "seahorn/seahorn.h"
            #else 
            #include <assert.h>
            #endif 
            bool nondet_bool() {bool b;return b;}
            bool nondet_int() {int i;return i;}
        """.trimIndent()
        )
    }
}