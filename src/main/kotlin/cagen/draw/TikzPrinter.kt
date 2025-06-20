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
package cagen.draw

import cagen.*
import cagen.expr.CodeWriter
import java.io.StringWriter
import java.io.Writer

private const val REFINEMENT_EDGE = ""
private const val INFFLOW_EDGE = ""
private const val LTL_NODE = "shape=record,bgcolor=lightblue"
private const val INPUT_NODE = ""
private const val OUTPUT_NODE = ""

class TikzPrinter(writer: Writer) {
    companion object {
        fun asString(block: TikzPrinter.() -> Unit): String {
            val sw = StringWriter()
            TikzPrinter(sw).apply(block)
            return sw.toString()
        }
    }

    private val out = CodeWriter(writer)
    fun println(s: String) = out.println(s)

    fun tikz(comps: List<Component>) {
        println("\\begin{tikzpicture}")
        for (c in comps) {
            c.print_tikz("toplevel")
        }
        println("\\end{tikzpicture}")
    }

    fun tikz_standalone(comps: List<Component>) {
        println(
            """
\documentclass{standalone}

\usepackage{microtype}
\usepackage{tikz}
\usetikzlibrary{fit,calc,shapes}
\begin{document}


\tikzset{
    component/.style={},
    contract/.style={},
    composed/.style={},
    ca/.style={},
    port/.style={},
    iport/.style={anchor=west,port},
    oport/.style={anchor=east,port},
}

% instance num port type
\newcommand\attachinput[4]{
    \node[iport] at ($(#1.north west) + (-.1cm,-#2*.75cm-.1cm)$) (#1_#3) {#3};}
\newcommand\attachoutput[3]{
    \node[oport] at ($(#1.north west) + (+.1cm,-#2*.75cm-.1cm)$) (#1_#3) {#3};}


"""
        )
        tikz(comps)
        println("\\end{document}")
    }

    private fun __print_tikz_node(name: String, label: String, style: String = "") {
        println("\\node[$style] ($name) {$label};")
    }

    private fun __structured_label(instance: String, signature: Signature) {
        signature.inputs.forEachIndexed { index, (name, type) ->
            println("\\attachinput{$instance}{$index}{$name}{$type}")
        }
        signature.outputs.forEachIndexed { index, (name, type) ->
            println("\\attachoutput{$instance}{$index}{$name}{$type}")
        }
    }

    fun Component.print_tikz(instance: String = "") =
        when (this) {
            is System -> this.print_tikz(instance)
            is Contract -> this.print_tikz(instance)
        }
    // __print_tikz_node(instance, "$instance:$name", "component")
    // __structured_label(instance, signature)

    fun System.print_tikz(instance: String) {
        __print_tikz_node(instance, "$instance:$name", "component")
        __structured_label(instance, signature)
        contracts.forEach {
            println("\\draw[->,contract] ({instance}) -- (${it.contract.name});")
        }
    }

    fun Contract.print_tikz(instance: String) {
        var label = "\\begin{tikzpicture}"
        val label_state = hashMapOf<String, MutableList<String>>()
        val edge_num = hashMapOf<CATransition, Int>()
        for (edge in transitions) {
            if (edge.from !in label_state) {
                label_state[edge.from] = arrayListOf()
                edge_num[edge] = label_state[edge.from]?.size ?: 0
            }
            label_state[edge.from]?.add(
                "\\calabel{${edge_num[edge]}}{${edge.contract.pre}}{${edge.contract.post}}"
            )
        }

        for ((node, lbl) in label_state.entries) {
            label += "\\node[ca-state] ($node) {$lbl};"
        }

        for (edge in transitions) {
            label += "\\draw[->,ca-edge] (${edge.from}) -- node[auto] {${edge_num[edge]}} (${edge.to});"
        }

        label += "\\end{tikzpicture}"
        __print_tikz_node(instance, instance + ":" + name + label, "ca")
        __structured_label(instance, signature)
    }

    /*
@print_tikz.when_type(model.ConstantSystem)
fun _(self: model.ConstantSystem, instance: String):
        __print_tikz_node(instance, str(self.constantValue), "ca")
if self.use_contract:
println(f"\\draw[->,contract] {instance} -- {obj.use_contract.contract.name};")


@print_tikz.when_type(model.FunctionSystem)
fun _(self, instance):
        __print_tikz_node(instance, str(self.display or self.func), "ca")
if self.use_contract:
println(f"\\draw[->,contract] {instance} -- {obj.use_contract.contract.name};")
*/

    fun print_tikz_cs_(self: System, instance: String) {
        println("\\node[composed] ($instance) {$instance\\\\begin{tikzpicture}")
        for (variable in self.signature.instances) {
            (variable.type as SystemType).system.print_tikz(variable.name)
        }

        fun edgeNode(a: Variable, port: String): String {
            /*  return if (isinstance(a.system, model.ConstantSystem) || isinstance(a.system, model.FunctionSystem))
                  a.variable
              else*/
            return if (a.name == "self") port else "${a.name}_$port"
        }

        for ((from, to) in self.connections) {
            val start = edgeNode(from.variable, from.portName)
            val end = edgeNode(to.variable, to.portName)
            println("\\draw[->,port] ($start) -- ($end);")
        }
        println("\\end{tikzpicture}")
        __structured_label(instance, self.signature)
    }

    /*fun AGContract.print_tikz(instance: String = "") {
        val inst = if (instance == "") name else instance
        println("$inst [ lbl=\"{{$name|$pre|$post}}\", $LTL_NODE]")
    }*/
}
