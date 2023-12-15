            #pragma once
            
            #include <stdbool.h>
            #define TRUE true
            #define FALSE false
            
            typedef struct TTC_Spec_state {
              int mioDistance;
int mioVelocity;
              bool collision;
int TTC;
              
              
              bool s1;
              bool _error_, _final_, _assume_;
              
                         
              
              
            } TTC_Spec_state;

            void init_TTC_Spec(TTC_Spec_state* state);
            void next_TTC_Spec(TTC_Spec_state* state);           