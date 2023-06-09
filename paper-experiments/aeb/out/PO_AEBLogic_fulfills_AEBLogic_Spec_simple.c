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

int TTC;
int FCWtime;
int PB1time;
int PB2time;
int FBtime;
bool stop;
int FCWactivate;
int decel;
int AEBstatus;
bool sTANDBY;
bool WARN;
bool BREAK;
bool _error_, _final_, _assume_;

void init_AEBLogic_Spec() {
  _error_ = false;
  _final_ = false;
  _assume_ = false;

  sTANDBY = true;
  WARN = false;
  BREAK = false;
}
void next_AEBLogic_Spec() {
  bool pre_contract_trans_sTANDBY_sTANDBY_0 = !(abs(TTC) < FCWtime && TTC >= 0);
  bool post_contract_trans_sTANDBY_sTANDBY_0 =
      AEBstatus == 0 && decel == 0 && FCWactivate == 0;
  bool contract_trans_sTANDBY_sTANDBY_0 =
      pre_contract_trans_sTANDBY_sTANDBY_0 &&
      post_contract_trans_sTANDBY_sTANDBY_0;
  bool pre_contract_trans_sTANDBY_WARN_1 = abs(TTC) < FCWtime && TTC >= 0;
  bool post_contract_trans_sTANDBY_WARN_1 =
      AEBstatus == 0 && decel == 0 && FCWactivate == 1;
  bool contract_trans_sTANDBY_WARN_1 =
      pre_contract_trans_sTANDBY_WARN_1 && post_contract_trans_sTANDBY_WARN_1;
  bool pre_contract_trans_WARN_sTANDBY_2 = abs(TTC) >= (2 * FCWtime);
  bool post_contract_trans_WARN_sTANDBY_2 =
      AEBstatus == 0 && decel == 0 && FCWactivate == 0;
  bool contract_trans_WARN_sTANDBY_2 =
      pre_contract_trans_WARN_sTANDBY_2 && post_contract_trans_WARN_sTANDBY_2;
  bool pre_contract_trans_WARN_BREAK_3 = abs(TTC) < PB1time && TTC >= 0;
  bool post_contract_trans_WARN_BREAK_3 =
      AEBstatus > 0 && decel > 0 && FCWactivate == 1;
  bool contract_trans_WARN_BREAK_3 =
      pre_contract_trans_WARN_BREAK_3 && post_contract_trans_WARN_BREAK_3;
  bool pre_contract_trans_WARN_WARN_4 = !(abs(TTC) < PB1time && TTC >= 0);
  bool post_contract_trans_WARN_WARN_4 =
      AEBstatus == 0 && decel == 0 && FCWactivate == 1;
  bool contract_trans_WARN_WARN_4 =
      pre_contract_trans_WARN_WARN_4 && post_contract_trans_WARN_WARN_4;
  bool pre_contract_trans_BREAK_BREAK_5 = !stop && TTC >= 0;
  bool post_contract_trans_BREAK_BREAK_5 =
      AEBstatus > 0 && decel > 0 && FCWactivate == 1;
  bool contract_trans_BREAK_BREAK_5 =
      pre_contract_trans_BREAK_BREAK_5 && post_contract_trans_BREAK_BREAK_5;
  bool pre_contract_trans_BREAK_sTANDBY_6 = stop && TTC < 0;
  bool post_contract_trans_BREAK_sTANDBY_6 =
      AEBstatus == 0 && decel == 0 && FCWactivate == 1;
  bool contract_trans_BREAK_sTANDBY_6 =
      pre_contract_trans_BREAK_sTANDBY_6 && post_contract_trans_BREAK_sTANDBY_6;
  bool t_26 = sTANDBY && contract_trans_sTANDBY_sTANDBY_0;
  bool t_27 = sTANDBY && contract_trans_sTANDBY_WARN_1;
  bool t_28 = WARN && contract_trans_WARN_sTANDBY_2;
  bool t_29 = WARN && contract_trans_WARN_BREAK_3;
  bool t_30 = WARN && contract_trans_WARN_WARN_4;
  bool t_31 = BREAK && contract_trans_BREAK_BREAK_5;
  bool t_32 = BREAK && contract_trans_BREAK_sTANDBY_6;
  bool VALID_PRE_COND = (sTANDBY && pre_contract_trans_sTANDBY_sTANDBY_0) ||
                        (sTANDBY && pre_contract_trans_sTANDBY_WARN_1) ||
                        (WARN && pre_contract_trans_WARN_sTANDBY_2) ||
                        (WARN && pre_contract_trans_WARN_BREAK_3) ||
                        (WARN && pre_contract_trans_WARN_WARN_4) ||
                        (BREAK && pre_contract_trans_BREAK_BREAK_5) ||
                        (BREAK && pre_contract_trans_BREAK_sTANDBY_6);
  bool VALID_POST_COND = (sTANDBY && t_26) || (sTANDBY && t_27) ||
                         (WARN && t_28) || (WARN && t_29) || (WARN && t_30) ||
                         (BREAK && t_31) || (BREAK && t_32);
  sTANDBY = t_26 || t_28 || t_32;
  WARN = t_27 || t_30;
  BREAK = t_29 || t_31;
  bool STATE_IN_NEXT = (sTANDBY || WARN || BREAK);
  _error_ = _error_ || (!STATE_IN_NEXT && VALID_PRE_COND);
  _assume_ = _assume_ || (!STATE_IN_NEXT && !VALID_PRE_COND);
}
int sys_TTC;
int sys_FCWtime;
int sys_PB1time;
int sys_PB2time;
int sys_FBtime;
bool sys_stop;
int sys_FCWactivate;
int sys_decel;
int sys_AEBstatus;
int sys_mode;
void init_sys_AEBLogic() {
  sys_TTC = 0;
  sys_FCWtime = 0;
  sys_PB1time = 0;
  sys_PB2time = 0;
  sys_FBtime = 0;
  sys_stop = 0;
  sys_FCWactivate = 0;
  sys_decel = 0;
  sys_AEBstatus = 0;
  sys_mode = 0;
}
void next_sys_AEBLogic() {
  int TTC = sys_TTC;
  int FCWtime = sys_FCWtime;
  int PB1time = sys_PB1time;
  int PB2time = sys_PB2time;
  int FBtime = sys_FBtime;
  bool stop = sys_stop;
  int FCWactivate = sys_FCWactivate;
  int decel = sys_decel;
  int AEBstatus = sys_AEBstatus;
  int mode = sys_mode;

  if (mode == M_DEFAULT && (abs(TTC) < FCWtime && TTC >= 0))
    mode = M_FCW;
  else if (mode == M_FCW) {
    if (abs(TTC) < PB1time && TTC >= 0) {
      mode = M_PARTIAL_BREAKING_1;
    } else if (abs(TTC) >= (2 * FCWtime)) {
      mode = M_DEFAULT;
    }
  } else if (mode == M_PARTIAL_BREAKING_1) {
    if (abs(TTC) < PB2time && TTC >= 0) {
      mode = M_PARTIAL_BREAKING_2;
    } else if (stop) {
      mode = M_DEFAULT;
    }
  } else if (mode == M_PARTIAL_BREAKING_2) {
    if (abs(TTC) < FBtime && TTC >= 0) {
      mode = M_FULL_BREAKING;
    } else if (stop) {
      mode = M_DEFAULT;
    }
  }
  if (mode == M_FULL_BREAKING && stop) {
    mode = M_DEFAULT;
  }

  switch (mode) {
  case 0: // M_DEFAULT:
    AEBstatus = 0;
    FCWactivate = 0;
    decel = 0;
    break;
  case 1: // M_FCW:
    AEBstatus = 0;
    FCWactivate = 1;
    decel = 0;
    break;
  case 2: // M_PARTIAL_BREAKING_1:
    AEBstatus = 1;
    FCWactivate = 1;
    decel = PB1_DECEL;
    break;
  case 3: // M_PARTIAL_BREAKING_2:
    AEBstatus = 2;
    FCWactivate = 1;
    decel = PB2_DECEL;
    break;
  case 4: // M_FULL_BREAKING:
    AEBstatus = 3;
    FCWactivate = 1;
    decel = FB_DECEL;
    break;
  default:
    assert(false);
  }

  sys_TTC = TTC;
  sys_FCWtime = FCWtime;
  sys_PB1time = PB1time;
  sys_PB2time = PB2time;
  sys_FBtime = FBtime;
  sys_stop = stop;
  sys_FCWactivate = FCWactivate;
  sys_decel = decel;
  sys_AEBstatus = AEBstatus;
  sys_mode = mode;
}
void main() {
  init_sys_AEBLogic();
  init_AEBLogic_Spec();
  while (true) {
    sys_TTC = nondet_int();
    sys_FCWtime = nondet_int();
    sys_PB1time = nondet_int();
    sys_PB2time = nondet_int();
    sys_FBtime = nondet_int();
    sys_stop = nondet_bool();
    next_sys_AEBLogic();
    TTC = sys_TTC;
    FCWtime = sys_FCWtime;
    PB1time = sys_PB1time;
    PB2time = sys_PB2time;
    FBtime = sys_FBtime;
    stop = sys_stop;
    FCWactivate = sys_FCWactivate;
    decel = sys_decel;
    AEBstatus = sys_AEBstatus;
    next_AEBLogic_Spec();
#ifdef SEAHORN
    sassert(!_error_);
#else
    assert(!_error_);
#endif
  }
}
