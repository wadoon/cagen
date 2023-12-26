package cagen

import cagen.cagen.gen.CCodeUtilsSimplified.toCExpr
import cagen.tutil.YamlSourceFile
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest

class ExprTests {
    @ParameterizedTest
    @YamlSourceFile(resources = ["/exprs/valid.yaml"], fieldsOrder = ["in", "c", "smv"])
    fun validExprs(input: String, expectedC: String?, expectedSMV: String?) {
        val expr = ParserFacade.parseExpr(input)
        val actualC = expr.toCExpr()
        val actualSmv = expr.toSMVExpr()

        Assertions.assertEquals(expectedC?.trim(), actualC)
        Assertions.assertEquals(expectedSMV?.trim(), actualSmv)
    }
}