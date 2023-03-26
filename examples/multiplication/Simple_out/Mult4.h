#pragma once

#include "Doubler.h";#include "Doubler.h";

typedef struct Mult4_state {
  // Inputs
  int x;
  // Outputs
  int y;

  // Internals
  Doubler a;Doubler b;

} Mult4_state;

void init_Mult4name>_state* state);
void next_Mult4(Mult4_state* state);