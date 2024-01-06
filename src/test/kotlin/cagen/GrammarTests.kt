package cagen

import cagen.code.CCodeUtilsSimplified.toCExpr
import cagen.modelchecker.toSMVExpr
import cagen.tutil.YamlSourceFile
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File
import java.nio.file.Paths
import java.util.stream.Stream
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.walk
import kotlin.streams.asStream

class GrammarTests {
    @ParameterizedTest
    @YamlSourceFile(resources = ["/exprs/valid.yaml"], fieldsOrder = ["in", "c", "smv"])
    fun validExprs(input: String, expectedC: String?, expectedSMV: String?) {
        val expr = ParserFacade.parseExpr(input)
        val actualC = expr.toCExpr()
        val actualSmv = expr.toSMVExpr()

        Assertions.assertEquals(expectedC?.trim(), actualC)
        Assertions.assertEquals(expectedSMV?.trim(), actualSmv)
    }

    @ParameterizedTest
    @MethodSource("models")
    fun validModels(input: File) {
        val m1 = ParserFacade.loadFile(input)
        val pp = PrettyPrinter.asString { pp(m1) }
        println(pp)
        val m2 = ParserFacade.loadFile(CharStreams.fromString(pp))
        Assertions.assertEquals(m1, m2)
    }

    companion object {
        @OptIn(ExperimentalPathApi::class)
        @JvmStatic
        fun models(): Stream<Arguments> {
            val path = Paths.get("src/test/resources/models")
            return path.walk().map { Arguments.of(it.toFile()) }.asStream()
        }
    }
}