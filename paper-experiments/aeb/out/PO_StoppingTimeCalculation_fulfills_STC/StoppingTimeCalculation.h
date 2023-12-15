            #pragma once
            #include <stdbool.h>            
            #define TRUE true
            #define FALSE false
            
            

            typedef struct StoppingTimeCalculation_state {
              // Inputs
              int egoVelocity;
              // Outputs
              int FCWStoppingTime;
int PB1StoppingTime;
int PB2StoppingTime;
int FBStoppingTime;
              // Internals
              
            } StoppingTimeCalculation_state;

            void init_StoppingTimeCalculation(StoppingTimeCalculation_state* state);
            void next_StoppingTimeCalculation(StoppingTimeCalculation_state* state);           