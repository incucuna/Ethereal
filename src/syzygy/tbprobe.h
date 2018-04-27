#ifndef TBPROBE_H
#define TBPROBE_H

#include "../movegen.h"
#include "../types.h"
#include "../piece.h"

extern int TB_MaxCardinality;
extern int TB_MaxCardinalityDTM;

void TB_init(char* path);
void TB_free(void);
int TB_probe_wdl(Board* board, int* success);
int TB_probe_dtz(Board* board, int* success);
int TB_probe_dtm(Board* board, int wdl, int* success);
// int TB_root_probe_wdl(Board* board, RootMoves *rm);
// int TB_root_probe_dtz(Board* board, RootMoves *rm);

// Definitions to try to avoid rewriting large chunks of the probing
// code. These definitions match or mirror those written in CFish

#define pieces_c(c)     (board->colours[(c)])
#define pieces_p(p)     (board->pieces[(p)-1])
#define pieces_cp(c,p)  (pieces_c((c)) & pieces_p((p)))

#endif

