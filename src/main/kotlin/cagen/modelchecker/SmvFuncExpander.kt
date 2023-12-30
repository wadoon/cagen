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
                    ite(arg lt SLiteral.integer(0), arg.negate(), arg)
                }

                else -> super.visit(func)
            }
        }
    }
}