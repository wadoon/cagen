            #include "AEBLogic_Spec.h"
            
            void init_AEBLogic_Spec(AEBLogic_Spec_state* state) {
                state->sTANDBY = true;
state->WARN = true;
state->BREAK = true;
                state->_error_= false;
                state->_final_= false;
                state->_assume_= false;
            };

            void next_AEBLogic_Spec(AEBLogic_Spec_state *state) {
                bool ALL_PRE_CONDITIONS_VIOLATED = true;
                bool ALL_POST_CONDITIONS_VIOLATED = true;
                bool EXISTS_APPLICABLE_CONTRACT = false;
            
                
                           
                bool pre_t_26 = !(abs(state->TTC) < state->FCWtime && state->TTC >= 0);
bool post_t_26 = state->AEBstatus == 0 && state->decel == 0 && state->FCWactivate == 0;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_26;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_26;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_26 & post_t_26);

bool pre_t_27 = abs(state->TTC) < state->FCWtime && state->TTC >= 0;
bool post_t_27 = state->AEBstatus == 0 && state->decel == 0 && state->FCWactivate == 1;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_27;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_27;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_27 & post_t_27);

bool pre_t_28 = abs(state->TTC) >= (2 * state->FCWtime);
bool post_t_28 = state->AEBstatus == 0 && state->decel == 0 && state->FCWactivate == 0;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_28;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_28;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_28 & post_t_28);

bool pre_t_29 = abs(state->TTC) < state->PB1time && state->TTC >= 0;
bool post_t_29 = state->AEBstatus > 0 && state->decel > 0 && state->FCWactivate == 1;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_29;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_29;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_29 & post_t_29);

bool pre_t_30 = !(abs(state->TTC) < state->PB1time && state->TTC >= 0);
bool post_t_30 = state->AEBstatus == 0 && state->decel == 0 && state->FCWactivate == 1;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_30;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_30;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_30 & post_t_30);

bool pre_t_31 = !state->stop && state->TTC>=0;
bool post_t_31 = state->AEBstatus > 0 && state->decel > 0 && state->FCWactivate == 1;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_31;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_31;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_31 & post_t_31);

bool pre_t_32 = state->stop  && state->TTC<0;
bool post_t_32 = state->AEBstatus == 0 && state->decel == 0 && state->FCWactivate == 1;
ALL_PRE_CONDITIONS_VIOLATED = ALL_PRE_CONDITIONS_VIOLATED & !pre_t_32;
ALL_POST_CONDITIONS_VIOLATED = ALL_POST_CONDITIONS_VIOLATED & !post_t_32;
EXISTS_APPLICABLE_CONTRACT = EXISTS_APPLICABLE_CONTRACT | (pre_t_32 & post_t_32);

                state->sTANDBY = state->sTANDBY & pre_t_26 & post_t_26 | state->WARN & pre_t_28 & post_t_28 | state->BREAK & pre_t_32 & post_t_32;
state->WARN = state->sTANDBY & pre_t_27 & post_t_27 | state->WARN & pre_t_30 & post_t_30;
state->BREAK = state->WARN & pre_t_29 & post_t_29 | state->BREAK & pre_t_31 & post_t_31;

                bool STATE_IN_NEXT = !( state->sTANDBY | state->WARN | state->BREAK );
                state->_error_ = !STATE_IN_NEXT && !ALL_PRE_CONDITIONS_VIOLATED;        
                state->_final_ = false; //        
                state->_assume_ = !STATE_IN_NEXT && ALL_PRE_CONDITIONS_VIOLATED;
                
                }