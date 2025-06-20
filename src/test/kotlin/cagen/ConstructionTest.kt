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

import cagen.dsl.lte
import cagen.dsl.model
import cagen.expr.SLiteral
import org.junit.jupiter.api.Test

class ConstructionTest {
    @Test
    fun constructionTest() {
        model {
            val srContract = contract("SR") {
                val (S, R) = input(bool(), "S", "R")
                val (Q) = output(bool(), "Q")
                trans("off", "On", S and !R, Q.smv)
                trans("off", "On", R or !S, !Q)
                trans("On", "off", R or !S, !Q)
                trans("On", "On", !R or (R and S), !!Q)
            }

            val et8 = contract("ErrorThreshold8") {
                val (I) = input(int, "I")
                val (Q) = output(bool, "Q")
                trans("init", "init", (0 lte I) and (I lte 10), Q eq (I gte 8))
            }

            val et8sys = system("et8sys") {
                val (I) = input(int, "I")
                val (Q) = output(bool, "Q")
                code = "Q = (I >= 8);"
                et8.use()
            }

            val rsSystem = system("rsSystem") {
                val (S, R) = input(bool(), "S", "R")
                val (Q) = output(bool(), "Q")
                code = ""
                srContract.use()
            }

            val constFalseC = contract("cFalseContract") {
                val (Q) = output(bool(), "Q")
                trans("init", "init", SLiteral.TRUE, !Q)
            }

            val constFalse = system("cFalse") {
                val (Q) = output(bool(), "Q")
                code = "Q=false;"
                constFalseC.use()
            }

            val top = system("top") {
                val (I) = input(int, "I")
                val (Q) = output(bool(), "Q")

                val (s) = state(rsSystem, "rs1")
                val (t) = state(et8sys, "threshold")
                val (cf) = state(constFalse, "cfalse")

                connect(I, t.port("I"))
                connect(t.port("Q"), s.port("S"))
                connect(cf.port("Q"), s.port("R"))
                connect(s.port("Q"), Q)
            }

            val c = ConstructCAFacade.construct(top)
            val p = PrettyPrinter().apply {
                pp(c.contract)
                pp(c)
            }
            println(p.out.stream.toString())
        }
    }
}