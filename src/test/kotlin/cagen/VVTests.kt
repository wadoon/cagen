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

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

class VVTests {
    val lattice = VariantLattice(
        mutableListOf(
            VariantFamily("A", "B", "C", "D", "E"),
            VariantFamily("X", "Y", "Z"),
        )
    )

    @Test
    fun comparison() {
        assertNotNull(lattice.findVariant("A"))
        assertNotNull(lattice.findVariant("B"))
        assertNotNull(lattice.findVariant("C"))
        assertNotNull(lattice.findVariant("D"))
        assertNotNull(lattice.findVariant("E"))

        assertNotNull(lattice.findVariant("X"))
        assertNotNull(lattice.findVariant("Y"))
        assertNotNull(lattice.findVariant("Z"))

        assertTrue { lattice.findVariant("A")?.family == lattice.findVariant("A")?.family }
        assertTrue { lattice.findVariant("A")?.family == lattice.findVariant("B")?.family }
        assertFalse { lattice.findVariant("A")?.family == lattice.findVariant("X")?.family }

        val x = lattice.findVariant("X")!!
        val y = lattice.findVariant("Y")!!
        val z = lattice.findVariant("Z")!!

        assertTrue { x.compareTo(y)!! < 0 }
        assertTrue { x.compareTo(x)!! <= 0 }
        assertTrue { x.compareTo(z)!! < 0 }
        assertTrue { z.compareTo(y)!! > 0 }

        val c = lattice.findVariant("C")!!

        assertNull(c.compareTo(x))
        assertNull(c.compareTo(y))
    }
}

class VersionTests {
    @Test
    fun parse() {
        assertTrue {
            val v10 = Version("v1.0")
            v10.number == listOf(1, 0)
        }

        assertTrue {
            val v1234 = Version("v1.2.3.4")
            v1234.number == listOf(1, 2, 3, 4)
        }

        assertThrows<IllegalArgumentException> {
            Version("v-1")
        }

        Version("v1.1523.54231.42314231.42314231.4231.4234231.4231.423231.42314.2314231.4")
        Version("v616154231.42314.2314.16521.523.4231.546.5231.4231.4231.46154")

        assertTrue(Version("1.0") == Version("v1.0"))
    }

    @Test
    fun testSemver() {
        assertTrue { Version("v1.0") < Version("v1.2") }
        assertTrue { Version("v1.0") < Version("v1.0.2") }
        assertTrue { Version("v2.0.0.0.0.0.1") < Version("v3.0") }
    }
}
