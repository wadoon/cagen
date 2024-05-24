                #include <stdlib.h>
                #include <stdio.h>
                #include <string.h>
                #include <stdbool.h>
                #define TRUE true
                #define FALSE false
            
                #include <assert.h>
                #include "UpDown.h"
                #include "Counter.h"

                struct kv {
                    char *key;
                    char *val;
                };

                int NUM_INPUTS = 1;
                
                int main(int argc, char *argv[]) {
                    if (argc <= 1)
                        exit(EXIT_FAILURE);

                    FILE *trace = fopen(argv[1], "r");
                    
                    Counter_state __state; 
                    init_Counter(&__state);
                    
                    UpDown_state __cstate; 
                    init_UpDown(&__cstate);
                    
                    char *line = NULL;
                    size_t n = 0;
                    int l = 0;
                    while(getline(&line, &n, trace) != -1) {
                        l += 1;
                        
                        // Split
                        struct kv *fields = malloc(sizeof(struct kv) * NUM_INPUTS);
                        int i = 0;
                        for (char *field = strtok(line, ",");
                             field != NULL;
                             field = strtok(NULL, ","), ++i) {
                            fields[i].key = strtok(field, "=");
                            fields[i].val = strtok(NULL, "");
                        }
                        
                        bool found_tick = false;
                        
                        for (int i = 0; i < NUM_INPUTS; ++i) {
                            if (strcmp(fields[i].key, "tick") == 0) {
    if (found_tick) {
        exit(EXIT_FAILURE);
    } else {
        __state.tick == atoi(fields[i].val);
        found_tick = true;
    }
} else {
    exit(EXIT_FAILURE);
}
                        }
                        
                        if (!found_tick) { exit(EXIT_FAILURE); }
                        
                        next_Counter(&__state);
                        
                        __cstate.cnt = __state.val;__cstate.tick = __state.tick;
                        
                        next_UpDown(&__cstate);
                        assert(__cstate._error_);
                    }
                }