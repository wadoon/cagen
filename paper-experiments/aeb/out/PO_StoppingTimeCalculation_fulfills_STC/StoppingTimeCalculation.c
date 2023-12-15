            #include "StoppingTimeCalculation.h"

            void init_StoppingTimeCalculation(StoppingTimeCalculation_state* state) {
                // Inputs
                state->egoVelocity = 0;
                // Outputs
                state->FCWStoppingTime = 0;
state->PB1StoppingTime = 0;
state->PB2StoppingTime = 0;
state->FBStoppingTime = 0;
                // Internals
                
                
            }

            void next_StoppingTimeCalculation(StoppingTimeCalculation_state* state) {
            int egoVelocity = state->egoVelocity;
int FCWStoppingTime = state->FCWStoppingTime;
int PB1StoppingTime = state->PB1StoppingTime;
int PB2StoppingTime = state->PB2StoppingTime;
int FBStoppingTime = state->FBStoppingTime;

      FBStoppingTime = egoVelocity / FB_DECEL;
      PB1StoppingTime = egoVelocity / PB1_DECEL;
      PB1StoppingTime = egoVelocity / PB2_DECEL;
      FCWStoppingTime = FBStoppingTime + reactTime;
    
state->egoVelocity = egoVelocity;
state->FCWStoppingTime = FCWStoppingTime;
state->PB1StoppingTime = PB1StoppingTime;
state->PB2StoppingTime = PB2StoppingTime;
state->FBStoppingTime = FBStoppingTime;
            }
        