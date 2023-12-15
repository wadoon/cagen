            #include "Gt.h"

            void init_Gt(Gt_state* state) {
                // Inputs
                state->a = 0;
                // Outputs
                state->v = false;
                // Internals
                
                
            }

            void next_Gt(Gt_state* state) {
            int a = state->a;
bool v = state->v;
 v = a <= C1; 
state->a = a;
state->v = v;
            }
        