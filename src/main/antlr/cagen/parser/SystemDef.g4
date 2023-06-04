grammar SystemDef;

// Parser

model: include* defines? globalCode=CODE? (contract|system)* EOF;
include: 'include' STRING;

contract: automata | invariant;

automata: CONTRACT name=Ident LBRACE
    io*
    history*
    prepost*
    transition*
    use_contracts*
    RBRACE;

prepost: CONTRACT name=Ident ':=' pre=STRING '==>' post=STRING;
transition: from=Ident ARROW to=Ident '::' (contr=Ident| pre=STRING '==>' post=STRING);

invariant: CONTRACT name=Ident LBRACE
  io*
  history*
  pre=STRING '==>' post=STRING
  use_contracts*
 RBRACE;

system: REACTOR Ident LBRACE
        io*
        use_contracts*
        connection*
        reaction?
        RBRACE;

connection: from=ioport ARROW
             (LPAREN (to+=ioport)+ RPAREN
             | to+=ioport)
             ;
ioport: (inst=Ident '.')? port=Ident;


use_contracts: CONTRACT use_contract (COMMA use_contract)*;
use_contract: Ident ('[' (subst (COMMA subst)*)? ']')?;
subst: local=Ident BARROW from=ioport;

defines: 'defines' LBRACE variable+ RBRACE;
io: type=(INPUT|OUTPUT|STATE) variable (COMMA variable)*;
history: 'history' n=Ident LPAREN INT RPAREN;
variable: n+=Ident (COMMA n+=Ident)* COLON t=Ident (':=' init=STRING)?;
reaction: CODE;


stateExpr:
     unaryop=(NOT|MINUS) stateExpr
    | stateExpr op=IN stateExpr
    | stateExpr op=UNION  stateExpr
    | stateExpr op=DIV stateExpr
    | stateExpr op=MOD stateExpr
    | stateExpr op=STAR stateExpr
    | stateExpr op=PLUS stateExpr
    | stateExpr op=MINUS stateExpr
    | stateExpr op=DCOLON stateExpr
    | stateExpr op=SHIFTL stateExpr
    | stateExpr op=SHIFTR stateExpr
    | stateExpr op=(EQ | NEQ | LT | GT | LTE | GTE) stateExpr
    | stateExpr op=AND stateExpr
    | stateExpr op=(OR | XOR | XNOR) stateExpr
    | stateExpr '?' stateExpr ':' stateExpr
    | stateExpr op=EQUIV stateExpr
    | stateExpr op=IMP stateExpr
    | terminalAtom
    ;

terminalAtom
    : LPAREN stateExpr RPAREN                                                   # paren
    | name=Ident LPAREN stateExpr ( COMMA  stateExpr)* RPAREN                   # functionExpr
    | casesExpr                                                                 # casesExprAtom
    //| var=ID                                                                    # variableAccess
    | var=Iden (LBRACKET INT RBRACKET)+                                         # arrayAccess
    | value=Ident (DOT dotted=terminalAtom | (LBRACKET array+=INT RBRACKET)*)   # variableDotted
    | value=INT                                                                 # integerLiteral
    | value=FLOAT                                                               # floatLiteral
    | value='TRUE'                                                              # trueExpr
    | value='FALSE'                                                             # falseExpr
    | LBRACE stateExpr ( COMMA  stateExpr)* RBRACE                              # setExpr
    | value=WORD_LITERAL                                                        # wordValue
  //  | rangeExpr                                                                 # rangeExpr2
    ;

//rangeExpr : lower=NUMBER DOTDOT upper=NUMBER;

casesExpr :
	CASE (branches+=caseBranch)+ ESAC;

caseBranch :
	cond=stateExpr COLON val=stateExpr SEMI;


// Lexer
DOT:'.';
LPAREN:'(';
RPAREN:')';
CODE: '{=' .*? '=}';
RBRACE: '}';
LBRACE: '{';
LBRACKET:'[';
RBRACKET:']';


WS: [ \n\f\r\t]+ -> skip;
COMMENT: '//' (~[\n\r]+) -> skip;
MCOMMENT: '/*' .*? '*/' -> skip;
STRING: '"' .*? '"';
REACTOR: 'reactor';
CONTRACT: 'contract';
//MAIN: 'main';
INPUT: 'input';
OUTPUT: 'output';
STATE: 'state';
ARROW: '->';
BARROW: '<-';
COLON: ':';
COMMA: ',';


WORD_LITERAL:
    '0' ('u' | 's')? ('b' | 'B' | 'o' | 'O' | '_' | 'd' | 'D' | 'h' | 'H') INT? '_' ('a'..'f' | 'A.' . 'F' | INT)*;

SEMI:';';

FLOAT: INT '.' INT;
INT: [0-9]+;
Ident: [a-zA-Z_][a-zA-Z_0-9]*;
ERROR: .;
