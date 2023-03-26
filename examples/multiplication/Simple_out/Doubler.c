#include "Doubler.h"

void init_Doubler(Doubler_state* state) {
    // Inputs
    state->x = 0;
    // Outputs
    state->y = 0;
    // Internals
}

void next_Doubler(Doubler_state* state) {
  // Inputs
  int x = state->x;
  // Outputs
  int y = state->y;
  // Internals


      y = 2 * x;
    
  // Inputs
  state->x = x;
  // Outputs
  state->y = y;
  // Internals

}