/* *****************************************************************
 * This file belongs to cagen (https://github.com/wadoon/cagen).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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
    companion object {
        fun asString(block: PrettyPrinter.() -> Unit): String {
            val sw = StringWriter()
            PrettyPrinter(sw).apply(block)
            return sw.toString()
        }
    }

    val out = CodeWriter(writer)
    fun pp(model: Model) {
        // model: include* defines? variants* globalCode=CODE? (contract|system)* EOF;
        printDefines(model.globalDefines)
        pp(model.variants)
        model.globalCode?.let {
            pp(it)
            out.println("")
        }
        pp(model.contracts)
        pp(model.systems)
    }

    fun pp(variants: VariantLattice) = variants.families.forEach { pp(it) }
    fun pp(it: VariantFamily) {
        out.print("variants ")

        it.names.forEachLast { hasMore, variant ->
            pp(variant)
            if (hasMore) out.print(", ")
        }

        out.println("")
    }

    fun pp(variant: Variant) = out.print(variant.name)

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
        out.println("${t.from} -> ${t.to} :: ${t.contract.pre.toSMVExpr()} ==> ${t.contract.post.toSMVExpr()}")
    }

    fun pp(vvGuard: VVGuard) {
        // vvguard: '#[' (vvexpr (COMMA? vvexpr)*)?  ']';
        out.print("#[ ")
        vvGuard.values.forEachLast { hasMore, it ->
            pp(it)
            if (hasMore) out.print(", ")
        }
        out.println(" ]")
    }

    fun pp(vvrange: VVRange) {
        pp(vvrange.start)
        if (!vvrange.isSingleton) {
            out.print("..")
            pp(vvrange.stop)
        }
    }

    fun pp(vv: VV) = out.print(
        when (vv) {
            is Version -> "v${vv.number.joinToString(".")}"
            is Variant -> vv.name
        },
    )

    fun pp(signature: Signature) {
        signature.inputs.sortedBy { it.name }.forEach { pp("input", it) }
        signature.outputs.sortedBy { it.name }.forEach { pp("output", it) }
        signature.internals.sortedBy { it.name }.forEach { pp("state", it) }
    }

    fun pp(modifier: String, variable: Variable) {
        out.print("$modifier ${variable.name} : ${variable.type.name}")
        if (variable.initValue != null) {
            out.println(" := ${variable.initValue}")
        }
        out.println("")
    }

    @JvmName("ppLU")
    private fun pp(contracts: MutableList<UseContract>) = contracts.forEach { pp(it) }
    fun pp(uc: UseContract) {
        out.println(
            "contract ${uc.contract.name}[${
                uc.variableMap.joinToString(", ") { (a, b) ->
                    "$a <= ${pp(b)}"
                }
            }]",
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
                    // variable: n+=Ident (COMMA n+=Ident)* COLON t=Ident (':=' init=STRING)?;
                    if (it.initValue == null) {
                        printf("%s : %s", it.name, it.type)
                    } else {
                        printf("%s : %s", it.name, it.type, it.initValue)
                    }
                }
            }
        }
    }
}

inline fun <T> Collection<T>.forEachLast(action: (hasMore: Boolean, T) -> Unit) {
    for ((index, item) in this.withIndex()) {
        action(index < size - 1, item)
    }
}