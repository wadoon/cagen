#include <stdbool.h>
#define TRUE true
#define FALSE false

#include <assert.h>
#include "TTC_Spec.c"
#include "TTCCalculation.c"

#ifdef __CPROVER__
int nondet_int(); 
bool nondet_bool();
#else 
int nondet_int() { int i; return i;}
bool nondet_bool() { bool b; return b;}
#endif

int main() {
    TTCCalculation_state __state; 
    init_TTCCalculation(&__state);
    
    TTC_Spec_state __cstate; 
    init_TTC_Spec(&__cstate);
    
    while(true) {
        __state.mioDistance = nondet_int();, __state.mioVelocity = nondet_int();
        next_TTCCalculation(&__state);
        __cstate.mioDistance = __state.mioDistance;__cstate.mioVelocity = __state.mioVelocity;__cstate.collision = __state.collision;__cstate.TTC = __state.TTC;
        next_TTC_Spec(&__cstate);
        assert(__cstate._error_);
    }
}