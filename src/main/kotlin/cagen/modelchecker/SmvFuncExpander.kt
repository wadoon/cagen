package cagen.modelchecker

import cagen.expr.*

object SmvFuncExpander {
    fun SMVExpr.expand(): SMVExpr {
        return this.accept(SmvFuncExpanderVisitor) as SMVExpr
    }

    object SmvFuncExpanderVisitor : SMVAstMutableVisitor() {
        override fun visit(func: SFunction): SMVExpr {
            return when (func.name) {
                "abs" -> {
                    val arg = func.arguments.first()
                    val lit = (arg.dataType?: SMVTypes.signed(32)).literal(0)
                    ite(arg lt lit, arg.negate(), arg)
                }

                else -> super.visit(func)
            }
        }
    }
}

private fun SMVType.literal(i: Int): SLiteral = when (this) {
    SMVTypes.BOOLEAN -> if (i == 0) SLiteral.FALSE else SLiteral.TRUE
    SMVTypes.FLOAT -> SFloatLiteral(i.toBigDecimal())
    SMVTypes.INT -> SLiteral.integer(i.toBigInteger())
    is SMVWordType -> SWordLiteral(i.toBigInteger(), this)
    else -> {
        error("unreachable")
    }
}
