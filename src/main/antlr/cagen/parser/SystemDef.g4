grammar SystemDef;

// Parser

model: include* (contract|system)* EOF;
include: 'include' STRING;

contract: automata|invariant;

automata: CONTRACT name=Ident (COLON inherit=use_contract)? LBRACE
    io*
    prepost*
    transition*
    RBRACE;

prepost: CONTRACT name=Ident ':=' pre=STRING '==>' post=STRING;
transition: from=Ident ARROW to=Ident '::' (contr=Ident| pre=STRING '==>' post=STRING);

invariant: CONTRACT name=Ident (COLON inherit=use_contract)? LBRACE
  io*
  pre=STRING '==>' post=STRING
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

io: type=(INPUT|OUTPUT|STATE) variable (COMMA variable)*;
variable: n+=Ident (COMMA n+=Ident)* COLON t=Ident;
reaction: CODE;


// Lexer

LPAREN:'(';
RPAREN:')';
CODE: '{=' .*? '=}';
RBRACE: '}';
LBRACE: '{';

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

Ident: [a-zA-Z_][a-zA-Z_0-9]*;
ERROR: .;
