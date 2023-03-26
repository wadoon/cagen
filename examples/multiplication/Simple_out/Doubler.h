#pragma once

#include <stdbool.h>


typedef struct Doubler_state {
  // Inputs
  int x;
  // Outputs
  int y;

  // Internals

} Doubler_state;

void init_Doubler(Doubler_state* state);
void next_Doubler(Doubler_state* state);