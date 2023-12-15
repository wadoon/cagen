            #include "TTCCalculation.h"

            void init_TTCCalculation(TTCCalculation_state* state) {
                // Inputs
                state->mioDistance = 0;
state->mioVelocity = 0;
                // Outputs
                state->collision = false;
state->TTC = 0;
                // Internals
                
                
            }

            void next_TTCCalculation(TTCCalculation_state* state) {
            int mioDistance = state->mioDistance;
int mioVelocity = state->mioVelocity;
bool collision = state->collision;
int TTC = state->TTC;

      int headaway = mioDistance - headawayOffset;
      int abs = mioVelocity < 0 ? -mioVelocity : mioVelocity;
      int clamped = clamp(10, abs, 150);
      TTC = 128 * headaway / clamped;
      TTC = TTC * (mioVelocity < 0 ? -1 : 1);
      collision = headaway < 2;
    
state->mioDistance = mioDistance;
state->mioVelocity = mioVelocity;
state->collision = collision;
state->TTC = TTC;
            }
        