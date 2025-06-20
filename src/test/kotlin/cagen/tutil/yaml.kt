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
package cagen.tutil

import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.provider.AnnotationBasedArgumentsProvider
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsSource
import org.yaml.snakeyaml.Yaml
import java.io.FileReader
import java.io.InputStreamReader
import java.io.Reader
import java.util.stream.Stream

class YamlFileArgumentsProvider : AnnotationBasedArgumentsProvider<YamlSourceFile>() {
    private val yaml = Yaml()

    override fun provideArguments(context: ExtensionContext, annotation: YamlSourceFile): Stream<out Arguments> {
        val args = mutableListOf<Arguments>()

        for (source in annotation.sources) {
            FileReader(source).use {
                args.addAll(readResources(it, annotation.fieldsOrder))
            }
        }

        for (resource in annotation.resources) {
            context.testClass.get().getResourceAsStream(resource).use { input ->
                val stream = InputStreamReader(input!!)
                args.addAll(readResources(stream, annotation.fieldsOrder))
            }
        }

        return args.stream()
    }

    private fun readResources(input: Reader, fieldsOrder: Array<String>): Collection<Arguments> {
        val v = yaml.load<List<Map<String, Any>>>(input)
        return v.map {
            if (fieldsOrder.isEmpty()) {
                Arguments.of(*it.map { (_, v) -> v }.toTypedArray())
            } else {
                Arguments.of(*fieldsOrder.map { field -> it[field] }.toTypedArray())
            }
        }
    }
}

@Target(AnnotationTarget.FUNCTION, AnnotationTarget.ANNOTATION_CLASS, AnnotationTarget.PROPERTY_GETTER)
@ArgumentsSource(YamlFileArgumentsProvider::class)
annotation class YamlSourceFile(
    val sources: Array<String> = [],
    val resources: Array<String> = [],
    val fieldsOrder: Array<String> = []
)