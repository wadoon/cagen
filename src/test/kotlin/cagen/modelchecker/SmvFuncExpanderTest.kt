package cagen.modelchecker

import cagen.ParserFacade
import cagen.modelchecker.SmvFuncExpander.expand
import org.junit.jupiter.api.Test

import org.junit.jupiter.api.Assertions.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (30.12.23)
 */
class SmvFuncExpanderTest {
    @Test
    fun expand() {
        val expr = ParserFacade.parseExpr("1+abs(-x)")
        val expected  = ParserFacade.parseExpr("1+(case -x < 0 : --x; TRUE: -x; esac)")
        val expanded = expr.expand()
        assertEquals(expected, expanded)
    }
}