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
package cagen.expr

import cagen.expr.SBinaryOperator.*

class CPrinter : SMVAstVisitor<String> {
    companion object {
        fun toString(a: SMVExpr) = a.accept(CPrinter())
    }

    override fun visit(v: SVariable) = v.name

    override fun visit(be: SBinaryExpression) =
        "(${be.left.accept(this)} ${operator(be.operator)} ${be.right.accept(this)})"

    private fun operator(operator: SBinaryOperator) = when (operator) {
        PLUS -> "+"
        MINUS -> "-"
        DIV -> "/"
        MUL -> "*"
        AND -> "&&"
        OR -> "||"
        LESS_THAN -> "<"
        LESS_EQUAL -> "<="
        GREATER_THAN -> ">"
        GREATER_EQUAL -> ">="
        XOR -> "^"
        EQUAL -> "=="
        NOT_EQUAL -> "!="
        MOD -> "%"
        SHL -> "<<"
        SHR -> ">>"
        else -> TODO()
    }

    override fun visit(ue: SUnaryExpression) = "${ue.operator}${ue.expr.accept(this)}"

    override fun visit(l: SLiteral): String = l.value.toString()

    override fun visit(a: SAssignment): String = "${a.target.accept(this)} = ${a.expr.accept(this)};"

    override fun visit(ce: SCaseExpression): String = visit(ce.cases)

    private fun visit(cases: List<SCaseExpression.Case>): String {
        if (cases.isEmpty()) return ""
        when (cases.size) {
            1 -> {
                val (a, b) = cases.first()
                return "${a.accept(this)} ? ${b.accept(this)}:-1"
            }

            2 -> {
                val (a, b) = cases.first()
                val (_, d) = cases[1]
                return "${a.accept(this)} ? ${b.accept(this)}:${d.accept(this)}"
            }

            else -> {
                val (a, b) = cases.first()
                return "${a.accept(this)} ? ${b.accept(this)}:(${visit(cases.drop(1))})"
            }
        }
    }

    override fun visit(func: SFunction): String =
        "${func.name}(${func.arguments.joinToString(", ") { it.accept(this) }})"

    override fun visit(access: SFieldAccess): String = "${access.expr.accept(this)}->${access.sub.accept(this)}"

    override fun visit(access: SArrayAccess): String = "${access.expr.accept(this)}[${access.index.accept(this)}]"

    override fun visit(quantified: SQuantified): String = TODO("Not yet implemented")
    override fun visit(smvModule: SMVModule): String = TODO("Not yet implemented")
    override fun visit(top: SMVAst): String = TODO("Not yet implemented")
}