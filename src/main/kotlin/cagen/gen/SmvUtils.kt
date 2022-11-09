package cagen

object SmvUtils {
    fun toSmv(contract: ContractAutomata): String {
        val name: String = contract.name
        val signature = contract.signature
        val states = contract.states

        val content = """
    MODULE $name (
    -- INPUTS
    ${signature.inputs.joinToString(", ") { it.name }},
    -- OUTPUTS
    ${signature.outputs.joinToString(", ") { it.name }}
    )

    VAR
    ${states.joinToString("\n") { "$it:boolean;" }}
    _error_:boolean;
    _final_:boolean;
    _assum_:boolean;


    DEFINES       
    -- at least we have one follow-up state 
    STATE_IN_NEXT = !( ${states.joinToString(" | ") { "next_$it" }} );
    ${
            contract.contracts.joinToString("\n") {
                "pre_${it.name} := ${it.pre};\n" +
                        "post_${it.name} := ${it.post};\n" +
                        "${it.name} := pre_${it.name} & post_${it.name};\n"
            }
        }
    ${contract.transitions.joinToString("\n") { "${it.name} := ${it.from} & ${it.contract.name};" }}
    VALID_PRE_COND := ${contract.contracts.joinToString(" | ") { "pre_${it.name}" }};
    VALID_POST_COND := ${contract.contracts.joinToString(" | ") { "post_${it.name}" }};
    
    ASSUMPTION := VALID_PRE_COND;
    GUARANTEE := VALID_POST_COND;
    
    ASSIGN

    ${states.joinToString("\n") { "init($it) := ${it.startsWith("init")};" }}
    ${
            contract.transitions.groupBy { it.to }.toList().joinToString("\n") { (s, inc) ->
                "next($s) := ${inc.joinToString(" | ") { it.name }};"
            }
        }
            
    init(_error_) : = false;
    next(_error_) : = ! STATE_IN_NEXT -- not activate state 
                      & VALID_PRE_COND; --and the reason is a post-condition violation (there exists a valid pre-condition)

    init(_final_) := false;
    next(_final_) := false;

    init(_assume_) := false;
    next(_assume_) := ! STATE_IN_NEXT  & ! VALID_PRE_COND; -- and the reason is all pre-condition will be violated
    """
        return content
    }

    fun inv_module(name: String, signature: Signature, pre: String, post: String) = """
    ${moduleHead(name, signature)}
    DEFINES 
        ASSUMPTION := $pre;
        GUARANTEE := $post;
    
    INVARSPEC ASSUMPTION -> GUARANTEE;
    """.trimIndent()

    fun moduleHead(name: String, signature: Signature) = """
        MODULE ${name}}(
        -- INPUTS
        ${signature.inputs.joinToString(", ") { it.name }}
        -- OUTPUTS
        ${signature.outputs.joinToString(", ") { it.name }}
        )
    """.trimIndent()

    fun ltl_module(name: String, signature: Signature, pre: String, post: String) = """
        ${moduleHead(name, signature)}
        DEFINES
            ASSUMPTION := $pre;
            GUARANTEE := $post;
        
        LTLSPEC ASSUMPTION -> GUARANTEE;"""

    fun refinement(contract: Contract, refined: UseContract): String {
        fun applySubst(v: Variable): String =
            refined.variableMap.find { it.first == v.name }?.second?.portName ?: v.name

        val inputs = (contract.signature.inputs + refined.contract.signature.inputs
                + contract.signature.outputs + refined.contract.signature.outputs)
            .map { it.name to it.type }
            .toMap().toList().joinToString("\n") { "${it.first} : ${it.second};" }

        return """
        MODULE main 
        IVAR 
          ${inputs}
             
                
         VAR
          parent : ${refined.contract.name}(
                ${contract.signature.inputs.joinToString(", ") { applySubst(it) }},
                ${contract.signature.outputs.joinToString(", ") { applySubst(it) }}
          );
          
          sub : ${contract.name}(
            ${contract.signature.inputs.joinToString(", ") { applySubst(it) }},
            ${contract.signature.outputs.joinToString(", ") { applySubst(it) }}
          );
         
         INVARSPEC parent.ASSUMPTION -> sub.ASSUMPTION;
         INVARSPEC sub.GUARANTEE -> parent.GUARANTEE;
    """.trimIndent()
    }

}