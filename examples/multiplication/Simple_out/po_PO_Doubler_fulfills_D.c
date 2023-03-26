// ProofObligation: PO_Doubler_fulfills_D
#include "Doubler.c"
#include <assert.h>

int nondet_int(); 
bool nondet_bool();

int main() {
    Doubler_state __state;
    init_Doubler(&__state);
    while(true) {
        __state.x = nondet_int();
        __CPROVER_assume(true);
        next_Doubler(&__state);
        assert(__state.y == __state.x + __state.x);
    }
}