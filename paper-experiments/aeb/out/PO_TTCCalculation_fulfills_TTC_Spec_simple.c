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

int mioDistance;
int mioVelocity;
bool collision;
int TTC;
bool s1;
bool _error_, _final_,  _assume_;

                void init_TTC_Spec() { 
                    _error_=false; _final_=false; _assume_=false;
                
s1 = true;
}
void next_TTC_Spec() {
bool pre_contract_trans_s1_s1_7 =  0 <= mioDistance
                    &&            mioDistance <= 1024
                    && -1024 <= mioVelocity
                    &&                mioVelocity <= 1024 ;
bool post_contract_trans_s1_s1_7 =  (collision == ((mioDistance - headawayOffset) < 2));
bool contract_trans_s1_s1_7 = pre_contract_trans_s1_s1_7 && post_contract_trans_s1_s1_7;
bool t_109 = s1 && contract_trans_s1_s1_7;
bool VALID_PRE_COND = (s1 && pre_contract_trans_s1_s1_7);
bool VALID_POST_COND = (s1 && t_109);
s1 = t_109;
bool STATE_IN_NEXT = ( s1);
_error_  =  _error_  || (!STATE_IN_NEXT &&  VALID_PRE_COND);
_assume_ =  _assume_ || (!STATE_IN_NEXT && !VALID_PRE_COND);
}
int sys_mioDistance;
int sys_mioVelocity;
bool sys_collision;
int sys_TTC;
void init_sys_TTCCalculation() {
sys_mioDistance = 0;
sys_mioVelocity = 0;
sys_collision = 0;
sys_TTC = 0;
}
void next_sys_TTCCalculation() {
int mioDistance = sys_mioDistance;
int mioVelocity = sys_mioVelocity;
bool collision = sys_collision;
int TTC = sys_TTC;

      int headaway = mioDistance - headawayOffset;
      int abs = mioVelocity < 0 ? -mioVelocity : mioVelocity;
      int clamped = clamp(10, abs, 150);
      TTC = 128 * headaway / clamped;
      TTC = TTC * (mioVelocity < 0 ? -1 : 1);
      collision = headaway < 2;
    
sys_mioDistance = mioDistance;
sys_mioVelocity = mioVelocity;
sys_collision = collision;
sys_TTC = TTC;
}
void main() {
init_sys_TTCCalculation();
init_TTC_Spec();
while(true) {
sys_mioDistance = nondet_int();
sys_mioVelocity = nondet_int();
next_sys_TTCCalculation();
mioDistance = sys_mioDistance;
mioVelocity = sys_mioVelocity;
collision = sys_collision;
TTC = sys_TTC;
next_TTC_Spec();
#ifdef SEAHORN
sassert(!_error_);
#else
assert(!_error_);
#endif
}
}
