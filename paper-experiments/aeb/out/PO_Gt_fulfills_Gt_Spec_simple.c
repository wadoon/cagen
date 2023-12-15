            #include <stdbool.h>
            #include <stdint.h>
            #define TRUE true
            #define FALSE false
            
            #ifdef SEAHORN
            #include "seahorn/seahorn.h"
            #else 
            #include <assert.h>
            #endif 
            
            bool nondet_bool() {bool b;return b;}
            bool nondet_int() {int i;return i;}
            
            const int PB1_DECEL = 5;
const int PB2_DECEL = 10;
const int FB_DECEL = 15;
const int C1 = 1;
const int headawayOffset = 3;
const int reactTime = 2;
            
            
     const int M_DEFAULT = 0, M_FCW = 1, M_PARTIAL_BREAKING_1 = 2,
              M_PARTIAL_BREAKING_2 = 3, M_FULL_BREAKING = 4;
    int abs(int x) { return x < 0 ? -x : x; }
    int min(int x, int y) { return x < y ? x : y; }
    int max(int x, int y) { return x > y ? x : y; }
    int clamp(int l, int x, int u) { return min(max(x, l), u); }

int a;
bool v;
bool s1;
bool _error_, _final_,  _assume_;

                void init_Gt_Spec() { 
                    _error_=false; _final_=false; _assume_=false;
                
s1 = true;
}
void next_Gt_Spec() {
bool pre_contract_trans_s1_s1_9 = TRUE;
bool post_contract_trans_s1_s1_9 = v == (a <= C1);
bool contract_trans_s1_s1_9 = pre_contract_trans_s1_s1_9 && post_contract_trans_s1_s1_9;
bool t_165 = s1 && contract_trans_s1_s1_9;
bool VALID_PRE_COND = (s1 && pre_contract_trans_s1_s1_9);
bool VALID_POST_COND = (s1 && t_165);
s1 = t_165;
bool STATE_IN_NEXT = ( s1);
_error_  =  _error_  || (!STATE_IN_NEXT &&  VALID_PRE_COND);
_assume_ =  _assume_ || (!STATE_IN_NEXT && !VALID_PRE_COND);
}
int sys_a;
bool sys_v;
void init_sys_Gt() {
sys_a = 0;
sys_v = 0;
}
void next_sys_Gt() {
int a = sys_a;
bool v = sys_v;
 v = a <= C1; 
sys_a = a;
sys_v = v;
}
void main() {
init_sys_Gt();
init_Gt_Spec();
while(true) {
sys_a = nondet_int();
next_sys_Gt();
a = sys_a;
v = sys_v;
next_Gt_Spec();
#ifdef SEAHORN
sassert(!_error_);
#else
assert(!_error_);
#endif
}
}
