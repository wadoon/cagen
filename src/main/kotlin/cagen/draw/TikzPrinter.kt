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
@file:Suppress("unused")

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
            c.printTikz("toplevel")
        }
        println("\\end{tikzpicture}")
    }

    fun tikzStandalone(comps: List<Component>) {
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

    private fun printTikzNode(name: String, label: String, style: String = "") {
        println("\\node[$style] ($name) {$label};")
    }

    private fun structuredLabel(instance: String, signature: Signature) {
        signature.inputs.forEachIndexed { index, (name, type) ->
            println("\\attachinput{$instance}{$index}{$name}{$type}")
        }
        signature.outputs.forEachIndexed { index, (name, type) ->
            println("\\attachoutput{$instance}{$index}{$name}{$type}")
        }
    }

    fun Component.printTikz(instance: String = "") = when (this) {
        is System -> this.printTikz(instance)
        is Contract -> this.printTikz(instance)
    }
    // __print_tikz_node(instance, "$instance:$name", "component")
    // __structured_label(instance, signature)

    fun System.printTikz(instance: String) {
        printTikzNode(instance, "$instance:$name", "component")
        structuredLabel(instance, signature)
        contracts.forEach {
            println("\\draw[->,contract] ({instance}) -- (${it.contract.name});")
        }
    }

    fun Contract.printTikz(instance: String) {
        var label = "\\begin{tikzpicture}"
        val labelState = hashMapOf<String, MutableList<String>>()
        val edgeNum = hashMapOf<CATransition, Int>()
        for (edge in transitions) {
            if (edge.from !in labelState) {
                labelState[edge.from] = arrayListOf()
                edgeNum[edge] = labelState[edge.from]?.size ?: 0
            }
            labelState[edge.from]?.add(
                "\\calabel{${edgeNum[edge]}}{${edge.contract.pre}}{${edge.contract.post}}"
            )
        }

        for ((node, lbl) in labelState.entries) {
            label += "\\node[ca-state] ($node) {$lbl};"
        }

        for (edge in transitions) {
            label += "\\draw[->,ca-edge] (${edge.from}) -- node[auto] {${edgeNum[edge]}} (${edge.to});"
        }

        label += "\\end{tikzpicture}"
        printTikzNode(instance, instance + ":" + name + label, "ca")
        structuredLabel(instance, signature)
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

    fun printTikzCs(self: System, instance: String) {
        println("\\node[composed] ($instance) {$instance\\\\begin{tikzpicture}")
        for (variable in self.signature.instances) {
            (variable.type as SystemType).system.printTikz(variable.name)
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
        structuredLabel(instance, self.signature)
    }

    /*fun AGContract.print_tikz(instance: String = "") {
        val inst = if (instance == "") name else instance
        println("$inst [ lbl=\"{{$name|$pre|$post}}\", $LTL_NODE]")
    }*/
}