            #pragma once
            #include <stdbool.h>            
            #define TRUE true
            #define FALSE false
            
            

            typedef struct TTCCalculation_state {
              // Inputs
              int mioDistance;
int mioVelocity;
              // Outputs
              bool collision;
int TTC;
              // Internals
              
            } TTCCalculation_state;

            void init_TTCCalculation(TTCCalculation_state* state);
            void next_TTCCalculation(TTCCalculation_state* state);           