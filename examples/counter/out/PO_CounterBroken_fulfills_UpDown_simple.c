#include <stdbool.h>
#include <stdint.h>
#ifdef SEAHORN
#include "seahorn/seahorn.h"
#else 
#include <assert.h>
#endif 
bool nondet_bool() {bool b;return b;}
bool nondet_int() {int i;return i;}
bool tick;
int cnt;
bool down;
bool uP;
bool DOWN;
bool _error_, _final_,  _assume_;
int h_cnt_0;
int h_cnt_1;

                void init_UpDown() { 
                    _error_=false; _final_=false; _assume_=false;
                
uP = true;
DOWN = false;
h_cnt_1 = 0;
}
void next_UpDown() {
h_cnt_1 = h_cnt_0;
h_cnt_0 = cnt;
bool pre_contract_trans_uP_uP_1 =  tick;
bool post_contract_trans_uP_uP_1 = h_cnt_1 < cnt && cnt < 128;
bool contract_trans_uP_uP_1 = pre_contract_trans_uP_uP_1 && post_contract_trans_uP_uP_1;
bool pre_contract_trans_uP_uP_2 = ! tick;
bool post_contract_trans_uP_uP_2 = h_cnt_1 == cnt;
bool contract_trans_uP_uP_2 = pre_contract_trans_uP_uP_2 && post_contract_trans_uP_uP_2;
bool pre_contract_trans_DOWN_DOWN_3 =  tick;
bool post_contract_trans_DOWN_DOWN_3 = h_cnt_1 > cnt && cnt > -128;
bool contract_trans_DOWN_DOWN_3 = pre_contract_trans_DOWN_DOWN_3 && post_contract_trans_DOWN_DOWN_3;
bool pre_contract_trans_DOWN_DOWN_4 = ! tick;
bool post_contract_trans_DOWN_DOWN_4 = h_cnt_1 == cnt;
bool contract_trans_DOWN_DOWN_4 = pre_contract_trans_DOWN_DOWN_4 && post_contract_trans_DOWN_DOWN_4;
bool pre_contract_trans_uP_DOWN_5 = tick;
bool post_contract_trans_uP_DOWN_5 = cnt == 128;
bool contract_trans_uP_DOWN_5 = pre_contract_trans_uP_DOWN_5 && post_contract_trans_uP_DOWN_5;
bool pre_contract_trans_DOWN_uP_6 = tick;
bool post_contract_trans_DOWN_uP_6 = cnt ==-128;
bool contract_trans_DOWN_uP_6 = pre_contract_trans_DOWN_uP_6 && post_contract_trans_DOWN_uP_6;
bool t_13 = uP && contract_trans_uP_uP_1;
bool t_14 = uP && contract_trans_uP_uP_2;
bool t_16 = DOWN && contract_trans_DOWN_DOWN_3;
bool t_17 = DOWN && contract_trans_DOWN_DOWN_4;
bool t_19 = uP && contract_trans_uP_DOWN_5;
bool t_20 = DOWN && contract_trans_DOWN_uP_6;
bool VALID_PRE_COND = (uP && pre_contract_trans_uP_uP_1) || (uP && pre_contract_trans_uP_uP_2) || (DOWN && pre_contract_trans_DOWN_DOWN_3) || (DOWN && pre_contract_trans_DOWN_DOWN_4) || (uP && pre_contract_trans_uP_DOWN_5) || (DOWN && pre_contract_trans_DOWN_uP_6);
bool VALID_POST_COND = (uP && t_13) || (uP && t_14) || (DOWN && t_16) || (DOWN && t_17) || (uP && t_19) || (DOWN && t_20);
uP = t_13 || t_14 || t_20;
DOWN = t_16 || t_17 || t_19;
bool STATE_IN_NEXT = ( uP || DOWN);
_error_  =  _error_  || (!STATE_IN_NEXT &&  VALID_PRE_COND);
_assume_ =  _assume_ || (!STATE_IN_NEXT && !VALID_PRE_COND);
}
bool sys_tick;
int sys_val;
bool sys_down;
void init_sys_CounterBroken() {
sys_tick = 0;
sys_val = 0;
sys_down = 0;
}
void next_sys_CounterBroken() {
bool tick = sys_tick;
int val = sys_val;
bool down = sys_down;

        if(!down) val += 1;
        else      val -= 1;
        if(val == 128 || val == -128) down = !down;
    
sys_tick = tick;
sys_val = val;
sys_down = down;
}
void main() {
init_sys_CounterBroken();
init_UpDown();
while(true) {
sys_tick = nondet_bool();
next_sys_CounterBroken();
cnt = sys_val;
tick = sys_tick;
next_UpDown();
#ifdef SEAHORN
sassert(!_error_);
#else
assert(!_error_);
#endif
}
}
