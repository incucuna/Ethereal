#ifndef _PSQT_H
#define _PSQT_H

int PSQTopening[32][64];
int PSQTendgame[32][64];

static int InversionTable[64] = {
    56,  57,  58,  59,  60,  61,  62,  63,
    48,  49,  50,  51,  52,  53,  54,  55,
    40,  41,  42,  43,  44,  45,  46,  47,
    32,  33,  34,  35,  36,  37,  38,  39,
    24,  25,  26,  27,  28,  29,  30,  31,
    16,  17,  18,  19,  20,  21,  22,  23,
     8,   9,  10,  11,  12,  13,  14,  15,
     0,   1,   2,   3,   4,   5,   6,   7
};

static int PawnOpeningMap32[32] = {
  0,   0,   0,   0,
-10,   0,   0,  -5,
-10,   0,   7,  11,
-10,   0,  10,  21,
-10,   0,   6,  10,
-10,   0,   0,   0,
-10,   0,   0,   0,
  0,   0,   0,   0,
};

 static int PawnEndgameMap32[32] = {
 0,   0,   0,   0,
-4,   1,   1,   1,
-4,   1,   5,   7,
-4,   1,   6,  12,
-4,   1,   4,   6,
-4,   1,   1,   1,
-4,   1,   1,   1,
 0,   0,   0,   0,
};

static int KnightOpeningMap32[32] = {
-31, -29, -27, -25,
 -9,  -6,  -2,   0,
 -7,  -2,  19,  19,
 -5,  10,  23,  28,
 -5,  12,  25,  32,
 -7,  10,  23,  29,
 -9,   4,  14,  20,
-41, -29, -27, -15,
};

static int KnightEndgameMap32[32] = {
-31, -29, -27, -25,
 -9,  -6,  -2,   0,
 -7,  -2,  19,  19,
 -5,  10,  23,  28,
 -5,  12,  25,  32,
 -7,  10,  23,  29,
 -9,   4,  14,  20,
-41, -29, -27, -15,
};

static int BishopOpeningMap32[32] = {
-15, -15, -15, -15,
  0,   4,   4,   4,
  0,   4,   8,   8,
  0,   4,   8,  12,
  0,   4,   8,  12,
  0,   4,   8,   8,
  0,   4,   4,   4,
  0,   0,   0,   0,
};

static int BishopEndgameMap32[32] = {
-15, -15, -15, -15, 
  0,   4,   4,   4, 
  0,   4,   8,   8, 
  0,   4,   8,  12, 
  0,   4,   8,  12, 
  0,   4,   8,   8, 
  0,   4,   4,   4, 
  0,   0,   0,   0,
};

static int RookOpeningMap32[32] = {
0,   0,   0,   0,
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0    
};

static int RookEndgameMap32[32] = {
0,   0,   0,   0,
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0
};

static int QueenOpeningMap32[32] = {
0,   0,   0,   0,
0,   0,   4,   4,
0,   4,   4,   6,
0,   4,   6,   8,
0,   4,   6,   8,
0,   4,   4,   6,
0,   0,   4,   4,
0,   0,   0,   0,
};

static int QueenEndgameMap32[32] = {
0,   0,   0,   0,
0,   0,   4,   4,
0,   4,   4,   6,
0,   4,   6,   8,
0,   4,   6,   8,
0,   4,   4,   6,
0,   0,   4,   4,
0,   0,   0,   0,
};

static int KingOpeningMap32[32] = {
0,   0,   0,   0,
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0,   
0,   0,   0,   0    
};

static int KingEndgameMap32[32] = {
0,   0,   0,   0,
0,   0,   0,   0,
0,   0,   5,   5,
0,   0,  10,  10,
0,   0,  15,  15,
0,   0,  15,  15,
0,   0,  10,  10,
0,   0,   0,   0, 
};


void init_psqt();

#endif
