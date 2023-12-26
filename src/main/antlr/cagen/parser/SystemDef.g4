grammar SystemDef;

model: include* defines? variants* globalCode=CODE? (contract|system)* EOF;

include: 'include' STRING;

variants: 'variants' v+=Ident (COMMA? v+=Ident)* ;

version: 'v' INT (DOT INT)*;

contract: automata | invariant;

automata: CONTRACT name=Ident LBRACE
    io*
    history*
    prepost*
    transition*
    use_contracts*
    RBRACE;

vvguard: '#[' (vvexpr (COMMA? vvexpr)*)?  ']';
vvexpr: vv ('..' vv)?;
vv: version | Ident;

prepost: CONTRACT name=Ident ASSIGN pre=expr STRONG_ARROW post=expr;

transition: vvguard? from=Ident ARROW to=Ident DOUBLE_COLUMN
    (contr=Ident| pre=expr STRONG_ARROW post=expr);


invariant: CONTRACT name=Ident LBRACE
  io*
  history*
  pre=STRING STRONG_ARROW post=STRING
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

defines: DEFINES LBRACE variable+ RBRACE;

io: type=(INPUT|OUTPUT|STATE) variable (COMMA variable)*;
history: HISTORY n=Ident LPAREN INT RPAREN;

variable: n+=Ident (COMMA n+=Ident)* COLON t=Ident (':=' init=STRING)?;
reaction: CODE;

ident: Ident | HISTORY | DEFINES;


expr:
     unaryop=(NOT|MINUS) expr
    | expr op=DIV expr
    | expr op=MOD expr
    | expr op=STAR expr
    | expr op=PLUS expr
    | expr op=MINUS expr
    | expr op=SHIFTL expr
    | expr op=SHIFTR expr
    | expr op=(EQ | NEQ | LT | GT | LTE | GTE) expr
    | expr op=AND expr
    | expr op=(OR | XOR | XNOR) expr
    | expr QUESTION_MARK expr COLON expr
    | expr op=IMP expr
    | terminalAtom
    ;

QUESTION_MARK : '?' ;

terminalAtom
    : LPAREN expr RPAREN                                              # paren
    | name=Ident LPAREN expr ( COMMA  expr)* RPAREN                   # functionExpr
    | casesExpr                                                       # casesExprAtom
    | value=Ident varprefix*                                          # variablewithprefix
    | value=INT                                                       # integerLiteral
    | value=FLOAT                                                     # floatLiteral
    | value='TRUE'                                                    # trueExpr
    | value='FALSE'                                                   # falseExpr
    | value=WORD_LITERAL                                              # wordValue
    ;

varprefix : DOT dotted=Ident            #fieldaccess
          | LBRACKET index=expr RBRACKET #arrayaccess
          ;

casesExpr  : CASE (branches+=caseBranch)+ ESAC;
caseBranch : cond=expr COLON val=expr SEMI;


// Lexer
NOT: '!';
MINUS:'-';
PLUS:'+';
CASE:'case';
ESAC:'esac';
EQ:'=';
NEQ:'!=';
LT:'<';
GTE:'>=';
LTE:'<=';
GT:'>';
SHIFTL: '<<';
DIV:'/';
MOD:'%';
STAR:'*';
SHIFTR: '>>';
IMP:'=>';
OR:'|';
XOR:'xor';
XNOR:'xnor';
AND:'&';

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
DEFINES : 'defines' ;
HISTORY : 'history' ;
INPUT: 'input';
OUTPUT: 'output';
STATE: 'state';
ARROW: '->';
BARROW: '<-';
COLON: ':';
COMMA: ',';
ASSIGN : ':=' ;
STRONG_ARROW : '==>' ;
DOUBLE_COLUMN : '::' ;


WORD_LITERAL:
    '0' ('u' | 's')? ('b' | 'B' | 'o' | 'O' | '_' | 'd' | 'D' | 'h' | 'H') INT? '_' ('a'..'f' | 'A.' . 'F' | INT)*;

SEMI:';';

FLOAT: INT '.' INT;
INT: [0-9]+;
Ident: [a-zA-Z_][a-zA-Z_0-9]*;
ERROR: .;
