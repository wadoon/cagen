package cagen

import cagen.code.CCodeUtilsSimplified.toCExpr
import cagen.modelchecker.toSMVExpr
import cagen.tutil.YamlSourceFile
import org.antlr.v4.runtime.CharStreams
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File
import java.nio.file.Paths
import java.util.stream.Stream
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.name
import kotlin.io.path.walk
import kotlin.streams.asStream

class GrammarTests {
    @ParameterizedTest
    @YamlSourceFile(resources = ["/exprs/valid.yaml"], fieldsOrder = ["in", "c", "smv"])
    fun validExprs(input: String, expectedC: String?, expectedSMV: String?) {
        val expr = ParserFacade.parseExpr(input)
        val actualC = expr.toCExpr()
        val actualSmv = expr.toSMVExpr()

        assertThat(actualC).isEqualToIgnoringWhitespace(expectedC)
        assertThat(actualSmv).isEqualToIgnoringWhitespace(expectedSMV)
    }

    @ParameterizedTest
    @MethodSource("models")
    @Disabled("Re-parsing results into different names")
    fun validModels(input: File) {
        val m1 = ParserFacade.loadFile(input)
        val pp = PrettyPrinter.asString { pp(m1) }
        println(pp)
        val m2 = ParserFacade.loadFile(CharStreams.fromString(pp))
        assertThat(m1).isEqualTo(m2)
    }

    @ParameterizedTest
    @MethodSource("allSysFiles")
    fun parseable(input: File) {
        ParserFacade.loadFile(input)
    }


    companion object {
        @OptIn(ExperimentalPathApi::class)
        @JvmStatic
        fun models(): Stream<Arguments> {
            val path = Paths.get("src/test/resources/models")
            return path.walk().map { Arguments.of(it.toFile()) }.asStream()
        }

        @OptIn(ExperimentalPathApi::class)
        @JvmStatic
        fun allSysFiles(): Stream<Arguments> {
            val path = Paths.get("./")
            return path.walk()
                .filter { it.name.endsWith(".sys") }
                .map { Arguments.of(it.toFile()) }.asStream()
        }

    }
}