            #include "STC.h"
            
            void init_STC(STC_state* state) {
                state->s1 = true;
                state->_error_= false;
                state->_final_= false;
                state->_assume_= false;
            };

            void next_STC(STC_state *state) {
                bool ALL_PRE_CONDITIONS_VIOLATED = true;
                bool ALL_POST_CONDITIONS_VIOLATED = true;
                bool EXISTS_APPLICABLE_CONTRACT = false;
            
                
                           
                bool pre_t_137 = 0 <= PB1_DECEL && PB1_DECEL <= PB2_DECEL
                               && PB2_DECEL <= FB_DECEL
                               && 0 <= state->egoVelocity;
bool post_t_137 = reactTime <= state->FCWStoppingTime      &&
                     0 <= state->FBStoppingTime          &&
                     state->FBStoppingTime <= state->PB1StoppingTime &&
                     state->PB1StoppingTime <= state->PB2StoppingTime;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_137;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_137;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_137 & post_t_137);

                state->s1 = state->s1 & pre_t_137 & post_t_137;

                bool STATE_IN_NEXT = !( state->s1 );
                state->_error_ = !STATE_IN_NEXT && !ALL_PRE_CONDITIONS_VIOLATED;        
                state->_final_ = false; //        
                state->_assume_ = !STATE_IN_NEXT && ALL_PRE_CONDITIONS_VIOLATED;
                
                }