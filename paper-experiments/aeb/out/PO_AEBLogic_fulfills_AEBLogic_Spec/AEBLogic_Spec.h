            #pragma once
            
            #include <stdbool.h>
            #define TRUE true
            #define FALSE false
            
            typedef struct AEBLogic_Spec_state {
              int TTC;
int FCWtime;
int PB1time;
int PB2time;
int FBtime;
bool stop;
              int FCWactivate;
int decel;
int AEBstatus;
              
              
              bool sTANDBY, WARN, BREAK;
              bool _error_, _final_, _assume_;
              
                         
              
              
            } AEBLogic_Spec_state;

            void init_AEBLogic_Spec(AEBLogic_Spec_state* state);
            void next_AEBLogic_Spec(AEBLogic_Spec_state* state);           