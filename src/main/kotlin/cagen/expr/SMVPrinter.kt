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

import java.io.*
import java.util.*
import kotlin.math.max

class SMVPrinter(val stream: CodeWriter = CodeWriter()) : SMVAstVisitor<Unit> {
    val sort = true

    override fun visit(top: SMVAst): Unit = throw IllegalArgumentException("not implemented for $top")

    override fun visit(be: SBinaryExpression) {
        val pleft = precedence(be.left)
        val pright = precedence(be.right)
        val pown = precedence(be)

        stream.print('(')
        be.left.accept(this)
        stream.print(" " + be.operator.symbol() + " ")
        be.right.accept(this)
        stream.print(')')
    }

    private fun precedence(expr: SMVExpr): Int {
        if (expr is SBinaryExpression) {
            val operator = expr.operator
            return operator.precedence()
        }
        if (expr is SUnaryExpression) {
            return expr.operator.precedence()
        }

        return if (expr is SLiteral ||
            expr is SVariable ||
            expr is SFunction
        ) {
            -1
        } else {
            1000
        }
    }

    override fun visit(ue: SUnaryExpression) {
        if (ue.expr is SBinaryExpression) {
            stream.print(ue.operator.symbol())
            stream.print("(")
            ue.expr.accept(this)
            stream.print(")")
        } else {
            stream.print(ue.operator.symbol())
            ue.expr.accept(this)
        }
    }

    override fun visit(l: SLiteral) {
        stream.print(l.dataType.format(l.value))
    }

    override fun visit(a: SAssignment) {
        a.target.accept(this)
        stream.print(" := ")
        a.expr.accept(this)
        stream.print(";").nl()
    }

    override fun visit(ce: SCaseExpression) {
        stream.print("case").increaseIndent()
        for ((condition, then) in ce.cases) {
            stream.nl()
            condition.accept(this)
            stream.print(" : ")
            then.accept(this)
            stream.print("; ")
        }
        stream.decreaseIndent().nl().print("esac")
    }

    override fun visit(m: SMVModule) {
        stream.print("MODULE ")
        stream.print(m.name)
        if (!m.moduleParameters.isEmpty()) {
            stream.print("(")
            m.moduleParameters.forEachIndexed { index, sVariable ->
                sVariable.accept(this)
                if (index + 1 < m.moduleParameters.size) stream.print(", ")
            }
            stream.print(")")
        }
        stream.nl()

        printVariables("IVAR", m.inputVars)
        printVariables("FROZENVAR", m.frozenVars)
        printVariables("VAR", m.stateVars)

        printDefinition(m.definitions)

        printSection("LTLSPEC", m.ltlSpec)
        printSection("CTLSPEC", m.ctlSpec)
        printSection("INVARSPEC", m.invariantSpecs)
        printSection("INVAR", m.invariants)
        printSectionSingle("INIT", m.initExpr)
        printSectionSingle("TRANS", m.transExpr)

        if (m.initAssignments.size > 0 || m.nextAssignments.size > 0) {
            stream.print("ASSIGN").increaseIndent()
            printAssignments("init", m.initAssignments)
            printAssignments("next", m.nextAssignments)
            stream.decreaseIndent()
        }
        stream.nl().print("-- end of module ${m.name}").nl()
    }

    private fun printSectionSingle(section: String, exprs: List<SMVExpr>) {
        if (!exprs.isEmpty()) {
            stream.print(section).increaseIndent().nl()
            exprs.conjunction().accept(this)
            stream.print(";").decreaseIndent().nl()
        }
    }

    private fun printDefinition(assignments: List<SAssignment>) {
        stream.printf("DEFINE").increaseIndent()

        for ((target, expr) in assignments) {
            stream.nl().print(target.name).print(" := ")
            expr.accept(this)
            stream.print(";")
        }
        stream.decreaseIndent().nl()
    }

    private fun printAssignments(func: String, a: List<SAssignment>) {
        val assignments = if (sort) a.sortedBy { it.target.name } else a
        for ((target, expr) in assignments) {
            stream.nl().print(func).print('(').print(quoted(target.name)).print(") := ")
            expr.accept(this)
            stream.print(";")
        }
    }

    private fun printSection(section: String, exprs: List<SMVExpr>) {
        if (exprs.isNotEmpty()) {
            exprs.forEach { e ->
                stream.nl().print(section).increaseIndent().nl()
                e.accept(this)
                stream.decreaseIndent().nl().nl()
            }
        }
    }

    override fun visit(func: SFunction) {
        val FUNCTION_ID_BIT_ACCESS = "<bitaccess>"
        when (func.name) {
            FUNCTION_ID_BIT_ACCESS -> visitBitAccess(func)
        }

        stream.print(func.name)
        stream.print('(')
        func.arguments.forEachIndexed { i, e ->
            e.accept(this)
            if (i + 1 < func.arguments.size) {
                stream.print(", ")
            }
        }
        stream.print(')')
    }

    private fun visitBitAccess(func: SFunction) {
        TODO("not implemented")
    }

    override fun visit(quantified: SQuantified) {
        when (quantified.operator.arity()) {
            1 -> {
                stream.print(quantified.operator.symbol())
                stream.print("( ")
                quantified[0].accept(this)
                stream.print(")")
            }

            2 -> {
                stream.print("( ")
                (quantified[0].accept(this))
                stream.print(")")
                stream.print(quantified.operator.symbol())
                stream.print("( ")
                (quantified[1].accept(this))
                stream.print(")")
            }

            else -> throw IllegalStateException("too much arity")
        }
    }

    override fun visit(access: SFieldAccess) {
        access.expr.accept(this)
        stream.print(".")
        access.sub.accept(this)
    }

    override fun visit(access: SArrayAccess) {
        access.expr.accept(this)
        stream.print("[")
        access.index.accept(this)
        stream.print("]")
    }

    private fun printVariables(type: String, v: List<SVariable>) {
        val vars =
            if (sort) {
                v.sorted()
            } else {
                v
            }

        if (vars.isNotEmpty()) {
            stream.print(type).increaseIndent()

            for (svar in vars) {
                stream.nl()
                printQuoted(svar.name)
                stream.print(" : ")
                stream.print(svar.dataType?.repr() ?: "<")
                stream.print(";")
            }

            stream.decreaseIndent().nl().print("-- end of $type").nl()
        }
    }

    override fun visit(v: SVariable) = printQuoted(v.name)

    fun printQuoted(name: String) {
        stream.print(quoted(name))
    }

    companion object {
        private val RESERVED_KEYWORDS = hashSetOf(
            "A", "E", "F", "G", "INIT", "MODULE", "case", "easc",
            "next", "init", "TRUE", "FALSE", "in", "mod", "union", "process", "AU", "EU", "U", "V", "S",
            "T", "EG", "EX", "EF", "AG", "AX", "AF", "X", "Y", "Z", "H", "O", "min", "max"
        )

        private val regex by lazy {
            val rk = RESERVED_KEYWORDS.joinToString("|", "(", ")")
            "(?<![a-zA-Z\$_])($rk)(?![a-zA-Z\$_])".toRegex()
        }

        fun quoted(name: String): String {
            /*return regex.replace(name) {
                "\"${it.value}\""
            }*/
            return if (name in RESERVED_KEYWORDS) "\"$name\"" else name
        }

        @JvmStatic
        fun toString(m: SMVAst): String {
            val s = CodeWriter()
            val p = SMVPrinter(s)
            m.accept(p)
            return s.stream.toString()
        }

        @JvmStatic
        fun toFile(m: SMVAst, file: File, append: Boolean = false) {
            BufferedWriter(FileWriter(file, append)).use { stream ->
                CodeWriter(stream).let {
                    val p = SMVPrinter(it)
                    m.accept(p)
                }
            }
        }
    }
}

/**
 * CodeWriter class.
 *
 * @author weigla (15.06.2014)
 * @version 2
 */
open class CodeWriter(val stream: Writer = StringWriter()) : Appendable by stream {
    private val uppercaseKeywords = true
    private val ident = "    "
    protected var identDepth = 0

    fun write(x: String): CodeWriter {
        stream.write(x)
        return this
    }

    fun appendIdent(): CodeWriter {
        for (i in 0 until identDepth) {
            write(ident)
        }
        return this
    }

    fun increaseIndent(): CodeWriter {
        identDepth++
        return this
    }

    fun decreaseIndent(): CodeWriter {
        identDepth = max(identDepth - 1, 0)
        return this
    }

    open fun keyword(keyword: String): CodeWriter = printf(if (uppercaseKeywords) keyword.uppercase(Locale.getDefault()) else keyword.lowercase(Locale.getDefault()))

    fun nl(): CodeWriter {
        write("\n")
        appendIdent()
        return this
    }

    fun println(arg: String): CodeWriter = print(arg).nl()
    fun print(args: String): CodeWriter = write(args)

    fun print(vararg args: Any): CodeWriter {
        args.forEach { write(it.toString()) }
        return this
    }

    fun printf(fmt: String, vararg args: Any): CodeWriter = write(String.format(fmt, *args))

    fun block(text: String = "", nl: Boolean = false, function: CodeWriter.() -> Unit): CodeWriter {
        printf(text)
        if (nl) nl()
        increaseIndent()
        function()
        decreaseIndent()
        if (nl) nl()
        return this
    }

    fun appendReformat(text: String): CodeWriter {
        text.splitToSequence('\n').forEach { nl().printf(it) }
        return this
    }

    fun cblock(head: String, tail: String, function: CodeWriter.() -> Unit): CodeWriter {
        printf(head)
        increaseIndent()
        nl()
        function()
        decreaseIndent()
        nl()
        printf(tail)
        return this
    }

    operator fun CharSequence.unaryPlus(): CharSequence {
        this@CodeWriter.append(this@unaryPlus)
        return this@unaryPlus
    }

    companion object {
        fun with(fn: CodeWriter.() -> Unit): String {
            val cw = CodeWriter()
            fn(cw)
            return cw.stream.toString()
        }
    }
}
