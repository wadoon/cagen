            #pragma once
            
            #include <stdbool.h>
            #define TRUE true
            #define FALSE false
            
            typedef struct STC_state {
              int egoVelocity;
              int FCWStoppingTime;
int PB1StoppingTime;
int PB2StoppingTime;
int FBStoppingTime;
              
              
              bool s1;
              bool _error_, _final_, _assume_;
              
                         
              
              
            } STC_state;

            void init_STC(STC_state* state);
            void next_STC(STC_state* state);           