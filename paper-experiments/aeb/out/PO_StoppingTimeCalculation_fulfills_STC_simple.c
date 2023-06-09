#include <stdbool.h>
#include <stdint.h>

#ifdef SEAHORN
#include "seahorn/seahorn.h"
#else
#include <assert.h>
#endif

bool nondet_bool() {
  bool b;
  return b;
}
bool nondet_int() {
  int i;
  return i;
}

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

int egoVelocity;
int FCWStoppingTime;
int PB1StoppingTime;
int PB2StoppingTime;
int FBStoppingTime;
bool s1;
bool _error_, _final_, _assume_;

void init_STC() {
  _error_ = false;
  _final_ = false;
  _assume_ = false;

  s1 = true;
}
void next_STC() {
  bool pre_contract_trans_s1_s1_8 = 0 <= PB1_DECEL && PB1_DECEL <= PB2_DECEL &&
                                    PB2_DECEL <= FB_DECEL && 0 <= egoVelocity;
  bool post_contract_trans_s1_s1_8 =
      reactTime <= FCWStoppingTime && 0 <= FBStoppingTime &&
      FBStoppingTime <= PB1StoppingTime && PB1StoppingTime <= PB2StoppingTime;
  bool contract_trans_s1_s1_8 =
      pre_contract_trans_s1_s1_8 && post_contract_trans_s1_s1_8;
  bool t_137 = s1 && contract_trans_s1_s1_8;
  bool VALID_PRE_COND = (s1 && pre_contract_trans_s1_s1_8);
  bool VALID_POST_COND = (s1 && t_137);
  s1 = t_137;
  bool STATE_IN_NEXT = (s1);
  _error_ = _error_ || (!STATE_IN_NEXT && VALID_PRE_COND);
  _assume_ = _assume_ || (!STATE_IN_NEXT && !VALID_PRE_COND);
}
int sys_egoVelocity;
int sys_FCWStoppingTime;
int sys_PB1StoppingTime;
int sys_PB2StoppingTime;
int sys_FBStoppingTime;
void init_sys_StoppingTimeCalculation() {
  sys_egoVelocity = 0;
  sys_FCWStoppingTime = 0;
  sys_PB1StoppingTime = 0;
  sys_PB2StoppingTime = 0;
  sys_FBStoppingTime = 0;
}
void next_sys_StoppingTimeCalculation() {
  int egoVelocity = sys_egoVelocity;
  int FCWStoppingTime = sys_FCWStoppingTime;
  int PB1StoppingTime = sys_PB1StoppingTime;
  int PB2StoppingTime = sys_PB2StoppingTime;
  int FBStoppingTime = sys_FBStoppingTime;

  FBStoppingTime = egoVelocity / FB_DECEL;
  PB1StoppingTime = egoVelocity / PB1_DECEL;
  PB1StoppingTime = egoVelocity / PB2_DECEL;
  FCWStoppingTime = FBStoppingTime + reactTime;

  sys_egoVelocity = egoVelocity;
  sys_FCWStoppingTime = FCWStoppingTime;
  sys_PB1StoppingTime = PB1StoppingTime;
  sys_PB2StoppingTime = PB2StoppingTime;
  sys_FBStoppingTime = FBStoppingTime;
}
void main() {
  init_sys_StoppingTimeCalculation();
  init_STC();
  while (true) {
    sys_egoVelocity = nondet_int();
    next_sys_StoppingTimeCalculation();
    egoVelocity = sys_egoVelocity;
    FCWStoppingTime = sys_FCWStoppingTime;
    PB1StoppingTime = sys_PB1StoppingTime;
    PB2StoppingTime = sys_PB2StoppingTime;
    FBStoppingTime = sys_FBStoppingTime;
    next_STC();
#ifdef SEAHORN
    sassert(!_error_);
#else
    assert(!_error_);
#endif
  }
}
