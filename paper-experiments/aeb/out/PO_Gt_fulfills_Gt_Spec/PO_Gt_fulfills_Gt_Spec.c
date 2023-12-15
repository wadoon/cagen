#include <stdbool.h>
#define TRUE true
#define FALSE false

#include <assert.h>
#include "Gt_Spec.c"
#include "Gt.c"

#ifdef __CPROVER__
int nondet_int(); 
bool nondet_bool();
#else 
int nondet_int() { int i; return i;}
bool nondet_bool() { bool b; return b;}
#endif

int main() {
    Gt_state __state; 
    init_Gt(&__state);
    
    Gt_Spec_state __cstate; 
    init_Gt_Spec(&__cstate);
    
    while(true) {
        __state.a = nondet_int();
        next_Gt(&__state);
        __cstate.a = __state.a;__cstate.v = __state.v;
        next_Gt_Spec(&__cstate);
        assert(__cstate._error_);
    }
}