        const int PB1_DECEL = "0sd32_5";
const int PB2_DECEL = "0sd32_10";
const int FB_DECEL = "0sd32_15";
const int C1 = "0sd32_1";
const int headawayOffset = "0sd32_3";
const int reactTime = "0sd32_2";
        
     const int M_DEFAULT = 0, M_FCW = 1, M_PARTIAL_BREAKING_1 = 2,
              M_PARTIAL_BREAKING_2 = 3, M_FULL_BREAKING = 4;
    int abs(int x) { return x < 0 ? -x : x; }
    int min(int x, int y) { return x < y ? x : y; }
    int max(int x, int y) { return x > y ? x : y; }
    int clamp(int l, int x, int u) { return min(max(x, l), u); }
            