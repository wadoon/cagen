#pragma once

#include <stdbool.h>
#define TRUE true
#define FALSE false

typedef struct Gt_Spec_state {
  int a;
  bool v;
  
  
  bool s1;
  bool _error_, _final_, _assume_;
  
             
  
  
} Gt_Spec_state;

void init_Gt_Spec(Gt_Spec_state* state);
void next_Gt_Spec(Gt_Spec_state* state);           