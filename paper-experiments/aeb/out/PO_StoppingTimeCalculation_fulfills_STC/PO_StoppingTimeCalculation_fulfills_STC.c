#include <stdbool.h>
#define TRUE true
#define FALSE false

#include <assert.h>
#include "STC.c"
#include "StoppingTimeCalculation.c"

#ifdef __CPROVER__
int nondet_int(); 
bool nondet_bool();
#else 
int nondet_int() { int i; return i;}
bool nondet_bool() { bool b; return b;}
#endif

int main() {
    StoppingTimeCalculation_state __state; 
    init_StoppingTimeCalculation(&__state);
    
    STC_state __cstate; 
    init_STC(&__cstate);
    
    while(true) {
        __state.egoVelocity = nondet_int();
        next_StoppingTimeCalculation(&__state);
        __cstate.egoVelocity = __state.egoVelocity;__cstate.FCWStoppingTime = __state.FCWStoppingTime;__cstate.PB1StoppingTime = __state.PB1StoppingTime;__cstate.PB2StoppingTime = __state.PB2StoppingTime;__cstate.FBStoppingTime = __state.FBStoppingTime;
        next_STC(&__cstate);
        assert(__cstate._error_);
    }
}