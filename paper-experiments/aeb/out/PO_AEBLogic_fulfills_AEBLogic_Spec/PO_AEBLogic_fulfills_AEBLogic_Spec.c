#include <stdbool.h>
#define TRUE true
#define FALSE false

#include <assert.h>
#include "AEBLogic_Spec.c"
#include "AEBLogic.c"

#ifdef __CPROVER__
int nondet_int(); 
bool nondet_bool();
#else 
int nondet_int() { int i; return i;}
bool nondet_bool() { bool b; return b;}
#endif

int main() {
    AEBLogic_state __state; 
    init_AEBLogic(&__state);
    
    AEBLogic_Spec_state __cstate; 
    init_AEBLogic_Spec(&__cstate);
    
    while(true) {
        __state.TTC = nondet_int();, __state.FCWtime = nondet_int();, __state.PB1time = nondet_int();, __state.PB2time = nondet_int();, __state.FBtime = nondet_int();, __state.stop = nondet_bool();
        next_AEBLogic(&__state);
        __cstate.TTC = __state.TTC;__cstate.FCWtime = __state.FCWtime;__cstate.PB1time = __state.PB1time;__cstate.PB2time = __state.PB2time;__cstate.FBtime = __state.FBtime;__cstate.stop = __state.stop;__cstate.FCWactivate = __state.FCWactivate;__cstate.decel = __state.decel;__cstate.AEBstatus = __state.AEBstatus;
        next_AEBLogic_Spec(&__cstate);
        assert(__cstate._error_);
    }
}