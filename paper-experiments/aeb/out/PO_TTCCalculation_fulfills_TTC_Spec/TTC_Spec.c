            #include "TTC_Spec.h"
            
            void init_TTC_Spec(TTC_Spec_state* state) {
                state->s1 = true;
                state->_error_= false;
                state->_final_= false;
                state->_assume_= false;
            };

            void next_TTC_Spec(TTC_Spec_state *state) {
                bool ALL_PRE_CONDITIONS_VIOLATED = true;
                bool ALL_POST_CONDITIONS_VIOLATED = true;
                bool EXISTS_APPLICABLE_CONTRACT = false;
            
                
                           
                bool pre_t_109 =  0 <= state->mioDistance
                    &&            state->mioDistance <= 1024
                    && -1024 <= state->mioVelocity
                    &&                state->mioVelocity <= 1024 ;
bool post_t_109 =  (state->collision == ((state->mioDistance - headawayOffset) < 2));
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_109;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_109;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_109 & post_t_109);

                state->s1 = state->s1 & pre_t_109 & post_t_109;

                bool STATE_IN_NEXT = !( state->s1 );
                state->_error_ = !STATE_IN_NEXT && !ALL_PRE_CONDITIONS_VIOLATED;        
                state->_final_ = false; //        
                state->_assume_ = !STATE_IN_NEXT && ALL_PRE_CONDITIONS_VIOLATED;
                
                }