            #include "AEBLogic.h"

            void init_AEBLogic(AEBLogic_state* state) {
                // Inputs
                state->TTC = 0;
state->FCWtime = 0;
state->PB1time = 0;
state->PB2time = 0;
state->FBtime = 0;
state->stop = false;
                // Outputs
                state->FCWactivate = 0;
state->decel = 0;
state->AEBstatus = 0;
                // Internals
                state->mode = 0;
                
            }

            void next_AEBLogic(AEBLogic_state* state) {
            int TTC = state->TTC;
int FCWtime = state->FCWtime;
int PB1time = state->PB1time;
int PB2time = state->PB2time;
int FBtime = state->FBtime;
bool stop = state->stop;
int FCWactivate = state->FCWactivate;
int decel = state->decel;
int AEBstatus = state->AEBstatus;
int mode = state->mode;

        if ( mode == M_DEFAULT &&
                (abs(TTC) < FCWtime && TTC >= 0))
                 mode = M_FCW;
        else if(mode == M_FCW) {
                     if (abs(TTC) < PB1time && TTC >= 0) {
                       mode = M_PARTIAL_BREAKING_1;
                     } else if (abs(TTC) >= (2 * FCWtime)) {
                       mode = M_DEFAULT;
                     }
                     }
        else if(mode == M_PARTIAL_BREAKING_1) {
                     if (abs(TTC) < PB2time && TTC >= 0) {
                       mode = M_PARTIAL_BREAKING_2;
                     } else if (stop) {
                       mode = M_DEFAULT;
                     }
                     }
                   else if(mode == M_PARTIAL_BREAKING_2){
                     if (abs(TTC) < FBtime && TTC >= 0) {
                       mode = M_FULL_BREAKING;
                     } else if (stop) {
                       mode = M_DEFAULT;
                     }
                     }
         if(mode == M_FULL_BREAKING && stop) { mode = M_DEFAULT; }


         switch (mode) {
           case 0://M_DEFAULT:
             AEBstatus = 0;
             FCWactivate = 0;
             decel = 0;
             break;
           case 1://M_FCW:
             AEBstatus = 0;
             FCWactivate = 1;
             decel = 0;
             break;
           case 2://M_PARTIAL_BREAKING_1:
             AEBstatus = 1;
             FCWactivate = 1;
             decel = PB1_DECEL;
             break;
           case 3://M_PARTIAL_BREAKING_2:
             AEBstatus = 2;
             FCWactivate = 1;
             decel = PB2_DECEL;
             break;
           case 4://M_FULL_BREAKING:
             AEBstatus = 3;
             FCWactivate = 1;
             decel = FB_DECEL;
             break;
           default:
             assert(false);
           }
       
state->TTC = TTC;
state->FCWtime = FCWtime;
state->PB1time = PB1time;
state->PB2time = PB2time;
state->FBtime = FBtime;
state->stop = stop;
state->FCWactivate = FCWactivate;
state->decel = decel;
state->AEBstatus = AEBstatus;
state->mode = mode;
            }
        