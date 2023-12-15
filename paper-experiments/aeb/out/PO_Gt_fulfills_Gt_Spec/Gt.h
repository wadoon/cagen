#pragma once
#include <stdbool.h>            
#define TRUE true
#define FALSE false



typedef struct Gt_state {
  // Inputs
  int a;
  // Outputs
  bool v;
  // Internals
  
} Gt_state;

void init_Gt(Gt_state* state);
void next_Gt(Gt_state* state);           