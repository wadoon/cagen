            #pragma once
            #include <stdbool.h>            
            #define TRUE true
            #define FALSE false
            
            b

            typedef struct AEBLogic_state {
              // Inputs
              int TTC;
int FCWtime;
int PB1time;
int PB2time;
int FBtime;
bool stop;
              // Outputs
              int FCWactivate;
int decel;
int AEBstatus;
              // Internals
              int mode;
            } AEBLogic_state;

            void init_AEBLogic(AEBLogic_state* state);
            void next_AEBLogic(AEBLogic_state* state);           