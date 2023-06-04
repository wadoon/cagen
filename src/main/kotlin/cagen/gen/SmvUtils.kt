package cagen

val Type.asSmvType: String
    get() = when (this) {
        is BuiltInType ->
            when (this.name) {
                "int", "int32" -> "signed word[32]"
                "int8" -> "signed word[32]"
                "short", "int16" -> "signed word[32]"
                "long", "int64" -> "signed word[32]"

                "uint", "uint32" -> "unsigned word[32]"
                "uint8" -> "unsigned word[32]"
                "uint16" -> "unsigned word[32]"
                "uint64" -> "unsigned word[32]"

                "float" -> "real"
                "double" -> "real"
                "bool" -> "boolean"
                else -> error("unexpected type")
            }

        else -> error("unexpected type")
    }


object SmvUtils {
    fun toSmv(contract: Contract): String {
        val name: String = contract.name
        val signature = contract.signature
        val states = contract.states

        val content = """
    ${moduleHead(name, signature)}
    VAR
    ${states.joinToString("\n") { "$it:boolean;" }}
    _error_:boolean;
    _final_:boolean;
    _assume_:boolean;

    ${handleHistory(contract)}

    DEFINE
    -- at least we have one follow-up state 
    STATE_IN_NEXT := ( ${states.joinToString(" | ") { "next($it)" }} );
    ${
            contract.contracts.joinToString("\n") {
                "pre_${it.name} := ${it.pre};\n" +
                        "post_${it.name} := ${it.post};\n" +
                        "${it.name} := pre_${it.name} & post_${it.name};\n"
            }
        }
    ${contract.transitions.joinToString("\n") { "${it.name} := ${it.from} & ${it.contract.name};" }}
    VALID_PRE_COND := ${contract.transitions.joinToString(" | ") { "(${it.from} & pre_${it.contract.name})" }};
    VALID_POST_COND := ${contract.transitions.joinToString(" | ") { "(${it.from} & post_${it.contract.name})" }};
    
    ASSUMPTION := !next(_assume_);
    GUARANTEE := !next(_error_);
    
    ASSIGN

    ${states.joinToString("\n") { "init($it) := ${if (it.first().isLowerCase()) "TRUE" else "FALSE"};" }}
    ${
            contract.transitions.groupBy { it.to }.toList().joinToString("\n") { (s, inc) ->
                "next($s) := ${inc.joinToString(" | ") { it.name }};"
            }
        }
            
    init(_error_) := FALSE;
    next(_error_) := _error_ | -- either there was already an error condition 
                        ( ! STATE_IN_NEXT -- not activate state 
                        & VALID_PRE_COND) ; -- and the reason is a post-condition violation (there exists a valid pre-condition)

    init(_final_) := FALSE;
    next(_final_) := FALSE;

    init(_assume_) := FALSE;
    next(_assume_) := _assume_ | (! STATE_IN_NEXT  & ! VALID_PRE_COND & !_error_); -- and the reason is all pre-condition will be violated
    """.trimIndent()
        return content
    }

    private fun handleHistory(contract: Contract): String =
        contract.history.joinToString("\n") { history ->
            val (name, depth) = history
            val type = contract.signature.get(name)!!.type.name
            val defines = (0..depth).joinToString("\n") {
                "h_${name}_${it} := h_${name}._${it};"
            }
            """
            VAR h_${name} : History_${type}_$depth($name);
            DEFINE
            $defines
            """.trimIndent()
        }


    fun inv_module(name: String, signature: Signature, pre: String, post: String) = """
    ${moduleHead(name, signature)}
    DEFINE
        ASSUMPTION := $pre;
        GUARANTEE := $post;
    
    INVARSPEC ASSUMPTION -> GUARANTEE;
    """.trimIndent()

    fun moduleHead(name: String, signature: Signature) = """
        MODULE ${name}(
        -- INPUTS
        ${signature.inputs.joinToString(", ") { it.name }.comma()}
        -- OUTPUTS
        ${signature.outputs.joinToString(", ") { it.name }}
        )
    """.trimIndent()

    fun ltl_module(name: String, signature: Signature, pre: String, post: String) = """
        ${moduleHead(name, signature)}
        DEFINE
            ASSUMPTION := $pre;
            GUARANTEE := $post;
        
        LTLSPEC ASSUMPTION -> GUARANTEE;"""

    fun refinement(contract: Contract, refined: UseContract): String {
        fun applySubst(v: Variable): String {
            val ioPort = refined.variableMap.find {
                it.first == v.name
            }
            return if (ioPort != null)
                "sub__${ioPort.second.portName}"
            else
                "parent__${v.name}"
        }

        val bot = (contract.signature.inputs + contract.signature.outputs)
            .map { it.copy(name = "sub__" + it.name) }

        val top = (refined.contract.signature.inputs + refined.contract.signature.outputs)
            .map { it.copy(name = "parent__" + it.name) }

        val inputs = (bot + top)
            .associate { it.name to it.type.asSmvType }
            .toList()
            .joinToString("\n") { "    ${it.first} : ${it.second};" }

        return """
MODULE main 
IVAR 
${inputs}

VAR
  parent : ${refined.contract.name}(
        ${refined.contract.signature.inputs.joinToString(", ") { applySubst(it) }.comma()}
        ${refined.contract.signature.outputs.joinToString(", ") { applySubst(it) }} );
  
  sub : ${contract.name}(
    ${contract.signature.inputs.joinToString(", ") { "sub__" + it.name }.comma()}
    ${contract.signature.outputs.joinToString(", ") { "sub__" + it.name }} );
 
INVARSPEC parent.ASSUMPTION -> sub.ASSUMPTION;
INVARSPEC sub.GUARANTEE -> parent.GUARANTEE;
""".trimIndent()
    }
}

private fun String.comma(): String = if (isBlank()) this else "$this,"