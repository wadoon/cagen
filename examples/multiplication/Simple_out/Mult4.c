#include "Mult4.h";

void init_Mult4(Mult4_state* state) {
    // Inputs
    state->x = 0;
    // Outputs
    state->y = 0;
    // Internals
    init_Doubler(&state->a);init_Doubler(&state->b);
}

void next_Mult4(Mult4_state* state) {
state->a.x =state->x
// call  a of type Doubler
next_Doubler(&state->a);
state->b.x =state->a.y
// call  b of type Doubler
next_Doubler(&state->b);
state->y =state->b.y

}