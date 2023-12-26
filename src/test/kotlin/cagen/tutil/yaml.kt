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
            if (fieldsOrder.isEmpty())
                Arguments.of(*it.map { (_, v) -> v }.toTypedArray())
            else
                Arguments.of(*fieldsOrder.map { field -> it[field] }.toTypedArray())
        }
    }
}


@Target(AnnotationTarget.FUNCTION, AnnotationTarget.ANNOTATION_CLASS, AnnotationTarget.PROPERTY_GETTER)
@ArgumentsSource(YamlFileArgumentsProvider::class)
annotation class YamlSourceFile(
    val sources: Array<String> = [], val resources: Array<String> = [],
    val fieldsOrder: Array<String> = []
)