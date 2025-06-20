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

object ConstructCAFacade {
    fun construct(composited: System): UseContract {
        // A list of non overlapping use contracts.
        val instantiated = composited.signature.instances
            .mapIndexed { idx, it ->
                val c = (it.type as SystemType).system.contracts.first()
                c.prefix(it.name + "_$idx")
            }

        val megaSubst = instantiated.map { (a, b) -> b }.flatten()
        val product = instantiated.map { (a, b) -> a }
            .reduce { a, b -> a * b }
        return UseContract(product, megaSubst.toMutableList())
    }
}