/*
  Copyright (c) 2013-2017 Ronald de Man
  This file may be redistributed and/or modified without restrictions.

  tbprobe.cpp contains the Stockfish-specific routines of the
  tablebase probing code. It should be relatively easy to adapt
  this code to other chess engines.
*/

#include "tbprobe.h"
#include "tbcore.h"

#include "tbcore.c"

extern uint64_t MaterialKeys[32];

int TB_MaxCardinality = 0, TB_MaxCardinalityDTM = 0;
extern int TB_CardinalityDTM;

static void prt_str(Board* board, char* str, int mirror){
    
    int i, piece, colour = !mirror ? WHITE : BLACK;
    
    for (piece = KING; piece >= PAWN; piece--)
        for (i = popcount(boardPiecesOfColour(board, colour, pieces)), i > 0; i--)
            *str++ = pchr[KING - piece];
        
    *str++ = 'v';
    
    for (piece = KING; piece >= PAWN; piece--)
        for (i = popcount(boardPiecesOfColour(board, !colour, pieces)), i > 0; i--)
            *str++ = pchr[KING - piece];
        
    *str++ = 0;
}

static uint64_t calc_key(const Board* board, int mirror){
    
    uint64_t key = 0ull; int piece;
    
    for (piece = PAWN; piece <= KING; piece++)
        key += MaterialKeys[MakePiece(piece, mirror)]
            *  popcount(piecesOfColour(board, WHITE, piece));
            
    for (piece = PAWN; piece <= KING; piece++)
        key += MaterialKeys[MakePiece(piece, !mirror)]
            *  popcount(piecesOfColour(board, BLACK, piece));
            
    // Verify that the above is equivilant to the computeMaterialKey
    // function which is verified during move application. If we are not
    // mirroring we can simple call the function, otherwise we will swap
    // the white and black pieces to achieve the desired material key
            
    #ifndef NDEBUG
    Board copy; memcpy(&copy, board, sizeof(Board));
    if (mirror){
        uint64_t temp = board->colours[WHITE];
        board->colours[WHITE] = board->colours[BLACK];
        board->colours[BLACK] = temp;
    }
    assert(key == computeMaterialKey(&copy));
    #endif
            
    return key;
}

static uint64_t calc_key_from_pcs(int* pieces, int mirror){
    
    uint64_t key = 0ull;
    
    key += MaterialKeys[WHITE_PAWN]   * (mirror ? pieces[9 + PAWN  ] ? pieces[1 + PAWN  ]);
    key += MaterialKeys[WHITE_KNIGHT] * (mirror ? pieces[9 + KNIGHT] ? pieces[1 + KNIGHT]);
    key += MaterialKeys[WHITE_BISHOP] * (mirror ? pieces[9 + BISHOP] ? pieces[1 + BISHOP]);
    key += MaterialKeys[WHITE_ROOK]   * (mirror ? pieces[9 + ROOK  ] ? pieces[1 + ROOK  ]);
    key += MaterialKeys[WHITE_QUEEN]  * (mirror ? pieces[9 + QUEEN ] ? pieces[1 + QUEEN ]);
    key += MaterialKeys[WHITE_KING]   * (mirror ? pieces[9 + KING  ] ? pieces[1 + KING  ]);
    
    key += MaterialKeys[BLACK_PAWN]   * (mirror ? pieces[1 + PAWN  ] ? pieces[9 + PAWN  ]);
    key += MaterialKeys[BLACK_KNIGHT] * (mirror ? pieces[1 + KNIGHT] ? pieces[9 + KNIGHT]);
    key += MaterialKeys[BLACK_BISHOP] * (mirror ? pieces[1 + BISHOP] ? pieces[9 + BISHOP]);
    key += MaterialKeys[BLACK_ROOK]   * (mirror ? pieces[1 + ROOK  ] ? pieces[9 + ROOK  ]);
    key += MaterialKeys[BLACK_QUEEN]  * (mirror ? pieces[1 + QUEEN ] ? pieces[9 + QUEEN ]);
    key += MaterialKeys[BLACK_KING]   * (mirror ? pieces[1 + KING  ] ? pieces[9 + KING  ]);
    
    return key;
    
}

static uint64_t calc_key_from_pieces(uint8_t* pieces, int num, int mirror){
    
    uint64_t key = 0; int i, colour, piece
    
    for (i = 0; i < num; i++){
        
        // Ronald has this condition
        if (!piece[i]) continue;
        
        // Convert from Ronald's piece values to Ethereal's
        
        piece  = (pieces[num] >= 1 && pieces[num] <=  6) ? pieces[num] - 1
               : (pieces[num] >= 9 && pieces[num] <= 14) ? pieces[num] - 9 : -1;
                  
        colour = (pieces[num] >= 1 && pieces[num] <=  6) ? WHITE
                 (pieces[num] >= 9 && pieces[num] <= 14) ? BLACK : -1;
                 
        // Conversion could not be done
        assert(piece != -1 && colour != -1);
        
        // Use the opposite colours Material key if we are mirroring
        key += !mirror ? MaterialKeys[MakePiece(piece, colour)] : MaterialKeys[MakePiece(piece, !colour)];
        
    }
    
    return key;
}

static int probe_wdl_table(Board* board, int* success){
    
    int i, p[TBPIECES];
    uint8_t res;
    
    size_t idx;
    struct TBEntry* ptr;
    struct TBHashEntry* ptr2;
    
    uint64_t key = board->mhash;

    // Test for KvK
    if (key == 2ull) return 0;

    ptr2 = TB_hash[key >> (64 - TBHASHBITS)];
    for (i = 0; i < HSHMAX; i++)
        if (ptr2[i].key == key) break;
    if (i == HSHMAX) {
        *success = 0;
        return 0;
    }

    ptr = ptr2[i].ptr;
    
    // With the help of C11 atomics, we implement double-checked locking correctly
    if (!atomic_load_explicit(&ptr->ready, memory_order_acquire)) {
        
        LOCK(TB_mutex);
        
        if (!atomic_load_explicit(&ptr->ready, memory_order_relaxed)) {
            
            char str[16];
            prt_str(pos, str, ptr->key != key);
            
            if (!init_table(ptr, str, 0)) {
                ptr2[i].key = 0ULL;
                *success = 0;
                UNLOCK(TB_mutex);
                return 0;
            }
            
            atomic_store_explicit(&ptr->ready, 1, memory_order_release);
        }
        
        UNLOCK(TB_mutex);
    }

    int bside, mirror, cmirror;
    if (!ptr->symmetric) {
        if (key != ptr->key) {
            cmirror = 8;
            mirror = 0x38;
            bside = (board->turn == WHITE);
        } else {
            cmirror = mirror = 0;
            bside = !(board->turn == WHITE);
        }
    } else {
        cmirror = board->turn == WHITE ? 0 : 8;
        mirror = board->turn == WHITE ? 0 : 0x38;
        bside = 0;
    }

    // p[i] is to contain the square 0-63 (A1-H8) for a piece of type
    // pc[i] ^ cmirror, where 1 = white pawn, ..., 14 = black king.
    // Pieces of the same type are guaranteed to be consecutive.
    if (!ptr->has_pawns) {
        
        struct TBEntry_piece *entry = (struct TBEntry_piece *)ptr;
        uint8_t *pc = entry->pieces[bside];
        
        for (i = 0; i < entry->num;) {
            uint64_t bb = pieces_cp((pc[i] ^ cmirror) >> 3, pc[i] & 0x07);
            do { p[i++] = poplsb(&bb); } while (bb);
        }
        
        idx = encode_piece(entry, entry->norm[bside], p, entry->factor[bside]);
        res = *decompress_pairs(entry->precomp[bside], idx);
    } 
    
    else {
        
        struct TBEntry_pawn *entry = (struct TBEntry_pawn *)ptr;
        int k = entry->file[0].pieces[0][0] ^ cmirror;
        
        uint64_t bb = pieces_cp(k >> 3, k & 0x07);
        i = 0; do { p[i++] = pop_lsb(&bb) ^ mirror; } while (bb);
        
        int f = pawn_file(entry, p);
        uint8_t *pc = entry->file[f].pieces[bside];
        
        for (; i < entry->num;) {
            bb = pieces_cp((pc[i] ^ cmirror) >> 3, pc[i] & 0x07);
            do { assume(i < TBPIECES); p[i++] = poplsb(&bb) ^ mirror; } while (bb);
        }
        
        idx = encode_pawn(entry, entry->file[f].norm[bside], p, entry->file[f].factor[bside]);
        res = *decompress_pairs(entry->file[f].precomp[bside], idx);
    }

    return res - 2;
}

static int probe_dtm_table(Board* board, int won, int* success){
    
    int i, res, p[TBPIECES];
    
    size_t idx;
    struct TBEntry *ptr;
    struct TBHashEntry *ptr2;
    
    uint64_t key = board->mhash;

    // Test for KvK
    if (key == 2ULL) return 0;

    ptr2 = TB_hash[key >> (64 - TBHASHBITS)];
    for (i = 0; i < HSHMAX; i++)
        if (ptr2[i].key == key) break;
    if (i == HSHMAX) {
        *success = 0;
        return 0;
    }

    ptr = ptr2[i].dtm_ptr;
    if (!ptr) {
        *success = 0;
        return 0;
    }

    // With the help of C11 atomics, we implement double-checked locking correctly
    if (!atomic_load_explicit(&ptr->ready, memory_order_acquire)) {
        
        LOCK(TB_mutex);
        
        if (!atomic_load_explicit(&ptr->ready, memory_order_relaxed)) {
            
            char str[16];
            prt_str(pos, str, ptr->key != key);
            
            if (!init_table(ptr, str, 1)) {
                ptr->data = NULL;
                ptr2[i].dtm_ptr = NULL;
                *success = 0;
                UNLOCK(TB_mutex);
                return 0;
            }
            
            atomic_store_explicit(&ptr->ready, 1, memory_order_release);
        }
        
        UNLOCK(TB_mutex);
    }

    int bside, mirror, cmirror;
    if (!ptr->symmetric) {
        if (key != ptr->key) {
            cmirror = 8;
            mirror = 0x38;
            bside = (board->turn == WHITE);
        } else {
            cmirror = mirror = 0;
            bside = !(board->turn == WHITE);
        }
    } 
    else {
        cmirror = board->turn == WHITE ? 0 : 8;
        mirror = board->turn == WHITE ? 0 : 0x38;
        bside = 0;
    }

    // p[i] is to contain the square 0-63 (A1-H8) for a piece of type
    // pc[i] ^ cmirror, where 1 = white pawn, ..., 14 = black king.
    // Pieces of the same type are guaranteed to be consecutive.
    if (!ptr->has_pawns) {
        
        struct DTMEntry_piece *entry = (struct DTMEntry_piece *)ptr;
        uint8_t *pc = entry->pieces[bside];
        
        for (i = 0; i < entry->num;) {
            uint64_t bb = pieces_cp((pc[i] ^ cmirror) >> 3, pc[i] & 0x07);
            do { p[i++] = poplsb(&bb); } while (bb);
        }
        
        idx = encode_piece((struct TBEntry_piece *)entry, entry->norm[bside], p, entry->factor[bside]);
        uint8_t *w = decompress_pairs(entry->precomp[bside], idx);
        res = ((w[1] & 0x0f) << 8) | w[0];
        if (!entry->loss_only)
            res = entry->map[entry->map_idx[bside][won] + res];
    } 
    
    else {
        
        struct DTMEntry_pawn *entry = (struct DTMEntry_pawn *)ptr;
        int k = entry->rank[0].pieces[0][0] ^ cmirror;
        
        uint64_t bb = pieces_cp(k >> 3, k & 0x07);
        i = 0; do { p[i++] = pop_lsb(&bb) ^ mirror; } while (bb);
        
        int r = pawn_rank((struct TBEntry_pawn2 *)entry, p);
        uint8_t *pc = entry->rank[r].pieces[bside];
        
        for (; i < entry->num;) {
            bb = pieces_cp((pc[i] ^ cmirror) >> 3, pc[i] & 0x07);
            do { assume(i < TBPIECES); p[i++] = pop_lsb(&bb) ^ mirror; } while (bb);
        }
        
        idx = encode_pawn2((struct TBEntry_pawn2 *)entry, entry->rank[r].norm[bside], p, entry->rank[r].factor[bside]);
        uint8_t *w = decompress_pairs(entry->rank[r].precomp[bside], idx);
        res = ((w[1] & 0x0f) << 8) | w[0];
        if (!entry->loss_only)
            res = entry->map[entry->map_idx[r][bside][won] + res];
    }

    return res;
}

static int probe_dtz_table(Board* board, int wdl, int* success){
  
    int i, p[TBPIECES];
    uint32_t res;
  
    size_t idx;  
    struct TBEntry *ptr;

    uint64_t key = board->mhash;

    if (DTZ_table[0].key1 != key && DTZ_table[0].key2 != key) {
        
        for (i = 1; i < DTZ_ENTRIES; i++)
            if (DTZ_table[i].key1 == key || DTZ_table[i].key2 == key) break;
    
        if (i < DTZ_ENTRIES) {
            struct DTZTableEntry table_entry = DTZ_table[i];
            for (; i > 0; i--)
                DTZ_table[i] = DTZ_table[i - 1];
            DTZ_table[0] = table_entry;
        }
        
        else {
            
            struct TBHashEntry *ptr2 = TB_hash[key >> (64 - TBHASHBITS)];
            for (i = 0; i < HSHMAX; i++)
                if (ptr2[i].key == key) break;
            
            if (i == HSHMAX) {
                *success = 0;
                return 0;
            }
            
            ptr = ptr2[i].ptr;
            char str[16];
            int mirror = (ptr->key != key);
            prt_str(board, str, mirror);
            
            if (DTZ_table[DTZ_ENTRIES - 1].entry)
                free_dtz_entry(DTZ_table[DTZ_ENTRIES-1].entry);
            
            for (i = DTZ_ENTRIES - 1; i > 0; i--)
                DTZ_table[i] = DTZ_table[i - 1];
            
            load_dtz_table(str, calc_key(board, mirror), calc_key(board, !mirror));
        }
    }

    ptr = DTZ_table[0].entry;
    if (!ptr) {
        *success = 0;
        return 0;
    }

    int bside, mirror, cmirror;
    if (!ptr->symmetric) {
        if (key != ptr->key) {
            cmirror = 8;
            mirror = 0x38;
            bside = (board->turn == WHITE);
        } else {
            cmirror = mirror = 0;
            bside = !(board->turn == WHITE);
        }
    } else {
        cmirror = board->turn == WHITE ? 0 : 8;
        mirror = board->turn == WHITE ? 0 : 0x38;
        bside = 0;
    }

    if (!ptr->has_pawns) {
        
        struct DTZEntry_piece *entry = (struct DTZEntry_piece *)ptr;
        if ((entry->flags & 1) != bside && !entry->symmetric) {
            *success = -1;
            return 0;
        }
        
        uint8_t *pc = entry->pieces;
        for (i = 0; i < entry->num;) {
            uint64_t bb = pieces_cp((pc[i] ^ cmirror) >> 3, pc[i] & 0x07);
            do { p[i++] = poplsb(&bb); } while (bb);
        }
        
        idx = encode_piece((struct TBEntry_piece *)entry, entry->norm, p, entry->factor);
        uint8_t *w = decompress_pairs(entry->precomp, idx);
        res = ((w[1] & 0x0f) << 8) | w[0];

        if (entry->flags & 2) {
            if (!(entry->flags & 16))
                res = entry->map[entry->map_idx[wdl_to_map[wdl + 2]] + res];
            else
                res = ((uint16_t *)entry->map)[entry->map_idx[wdl_to_map[wdl + 2]] + res];
        }

        if (!(entry->flags & pa_flags[wdl + 2]) || (wdl & 1))
            res *= 2;
    }
  
    else {
        
      struct DTZEntry_pawn *entry = (struct DTZEntry_pawn *)ptr;
      int k = entry->file[0].pieces[0] ^ cmirror;
      
      Bitboard bb = pieces_cp(k >> 3, k & 0x07);
      i = 0; do { p[i++] = pop_lsb(&bb) ^ mirror; } while (bb);
      
      int f = pawn_file((struct TBEntry_pawn *)entry, p);
      if ((entry->flags[f] & 1) != bside) {
          *success = -1;
          return 0;
      }
      
      uint8_t *pc = entry->file[f].pieces;
      for (; i < entry->num;) {
          bb = pieces_cp((pc[i] ^ cmirror) >> 3, pc[i] & 0x07);
          do { assume(i < TBPIECES); p[i++] = pop_lsb(&bb) ^ mirror; } while (bb); 
      }
      
      idx = encode_pawn((struct TBEntry_pawn *)entry, entry->file[f].norm, p, entry->file[f].factor);
      uint8_t *w = decompress_pairs(entry->file[f].precomp, idx);
      res = ((w[1] & 0x0f) << 8) | w[0];
    
      if (entry->flags[f] & 2) {
          if (!(entry->flags[f] & 16))
              res = entry->map[entry->map_idx[f][wdl_to_map[wdl + 2]] + res];
          else
              res = ((uint16_t *)entry->map)[entry->map_idx[f][wdl_to_map[wdl + 2]] + res];
      }
    
      if (!(entry->flags[f] & pa_flags[wdl + 2]) || (wdl & 1))
          res *= 2;
    }
    
    return res;
}

static int probe_ab(Board* board, int alpha, int beta, int* success){
  
    // No probe_ab when the position has an enpass move
    assert(board->epSquare == -1);
  
    Undo undo[1];
    int i, v, size = 0;
    uint16_t move, moves[MAX_MOVES];
    genAllNoisyMoves(board, moves, &size);

    for (i = 0; i < size; i++){
        
        move = moves[i];
        
        // Skip over non-captures (non-capture promotions)
        if (board->squares[MoveTo(move)] == EMPTY)
            continue;
        
        // Apply the move, and verify legality
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }
        
        v = -probe_ab(pos, -beta, -alpha, success);
        revertMove(board, move, undo);
        if (*success == 0) return 0;
        
        if (v > alpha) {
            if (v >= beta)
                return v;
            alpha = v;
        }
    }
    
    v = probe_wdl_table(pos, success);

    return alpha >= v ? alpha : v;    
}

int TB_probe_wdl(Board* board, int* success){
    
    *success = 1;

    Undo undo[1];
    int i, v, size = 0;
    uint16_t move, moves[MAX_MOVES];
    genAllNoisyMoves(board, moves, &size);

    int best_cap = -3, best_ep = -3;

    // We do capture resolution, letting best_cap keep track of the best
    // capture without ep rights and letting best_ep keep track of still
    // better ep captures if they exist.
    
    for (i = 0; i < size; i++){
        
        move = moves[i];
        
        // Skip over non-captures (non-capture promotions)
        if (   MoveType(move) != ENPASS_MOVE
            && board->squares[MoveTo(move)] == EMPTY)
            continue;
        
        // Apply the move, and verify legality
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }
        
        v = -probe_ab(pos, -2, -best_cap, success);
        revertMove(board, move, undo);
        if (*success == 0) return 0;
        
        if (v > best_cap) {
            
            if (v == 2) {
                *success = 2;
                return 2;
            }
            
            if (type_of_m(move) != ENPASSANT)
                best_cap = v;
            
            else if (v > best_ep)
                best_ep = v;
        }
        
    }

    v = probe_wdl_table(pos, success);
    if (*success == 0) return 0;

    // Now max(v, best_cap) is the WDL value of the position without ep rights.
    // If the position without ep rights is not stalemate or no ep captures
    // exist, then the value of the position is max(v, best_cap, best_ep).
    // If the position without ep rights is stalemate and best_ep > -3,
    // then the value of the position is best_ep (and we will have v == 0).

    if (best_ep > best_cap) {
        
        if (best_ep > v) { // ep capture (possibly cursed losing) is best.
            *success = 2;
            return best_ep;
        }
        
        best_cap = best_ep;
    }

  // Now max(v, best_cap) is the WDL value of the position unless
  // the position without ep rights is stalemate and best_ep > -3.

  if (best_cap >= v) {
    // No need to test for the stalemate case here: either there are
    // non-ep captures, or best_cap == best_ep >= v anyway.
    *success = 1 + (best_cap > 0);
    return best_cap;
  }

    // Now handle the stalemate case.
    if (best_ep > -3 && v == 0) {

    
        // Check for stalemate in the position with ep captures.
        
        for (i = 0; i < size; i++){
            
            move = Moves[i];
            
            if (MoveType(move) == ENPASS_MOVE) continue;
            
            applyMove(board, move, undo);
            if (!isNotInCheck(board, !board->turn)){
                revertMove(board, move, undo);
                continue;
            }
            
            revertMove(board, move, undo);
            break;
            
        }
        
        if (i == size && !board->kingAttackers){
            
            size = 0;
            generateAllQuietMoves(board, moves, &size);
            
            for (i = 0; i < size; i++){
                
                applyMove(board, move, undo);
                if (!isNotInCheck(board, !board->turn)){
                    revertMove(board, move, undo);
                    continue;
                }
                
                revertMove(board, move, undo);
                break;
            }
        }
        
        if (i == size) { // Stalemate detected.
            *success = 2;
            return best_ep;
        }
    }

    // Stalemate / en passant not an issue, so v is the correct value.

    return v;
}

static int probe_dtm_win(Board* board, int* success);

static int probe_dtm_loss(Board* board, int* success){
    
    int v, best = -MATE, num_ep = 0;

    Undo undo[1];
    int size = 0;
    uint16_t move, moves[MAX_MOVES];
    genAllNoisyMoves(board, moves, &size);

    for (i = 0; i < size; i++){

        move = Moves[i];

        // Skip over non-captures (non-capture promotions)
        if (board->squares[MoveTo(move)] == EMPTY)
            continue;

        // Apply the move, and verify legality
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }

        if (MoveType(move) == ENPASS_MOVE)
            num_ep++;

        v = -probe_dtm_win(pos, success) + 1;
        revertMove(board, move, undo);
        best = max(best, v);
        if (*success == 0)
            return 0;
    }
    
    if (num_ep != 0){
        
        size = 0;
        generateAllLegalMoves(board, moves, &size);
        
        if (size == num_ep)
            return best;
        
    }
    
    v = -MATE + 2 * probe_dtm_table(pos, 0, success);
    return max(best, v);
}

static int probe_dtm_win(Board* board, int* success){
    
    int v, best = -MATE;
    
    Undo undo[1];
    int size = 0;
    uint16_t move, moves[MAX_MOVES];
    genAllMoves(board, moves, &size);
    
    for (i = 0; i < size; i++){
        
        move = Moves[i];
        
        // Apply the move, and verify legality
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }
        
        if (   (board->epSquare != -1 ? TB_probe_wdl(pos, success)
                                      : probe_ab(pos, -1, 0, success)) < 0
            && *success)
            v = -probe_dtm_loss(pos, success) - 1;
        else
            v = -VALUE_INFINITE;
        
        revertMove(board, move, undo);
        best = max(best, v);
        if (*success == 0) return 0;
    }
    
    return best;
}

int TB_probe_dtm(Board* board, int wdl, int *success){
    
  assert(wdl != 0);

  *success = 1;

  return wdl > 0 ? probe_dtm_win(pos, success)
                 : probe_dtm_loss(pos, success);
}

static int wdl_to_dtz[] = {
  -1, -101, 0, 101, 1
};

// Probe the DTZ table for a particular position.
// If *success != 0, the probe was successful.
// The return value is from the point of view of the side to move:
//         n < -100 : loss, but draw under 50-move rule
// -100 <= n < -1   : loss in n ply (assuming 50-move counter == 0)
//         0        : draw
//     1 < n <= 100 : win in n ply (assuming 50-move counter == 0)
//   100 < n        : win, but draw under 50-move rule
//
// If the position mate, -1 is returned instead of 0.
//
// The return value n can be off by 1: a return value -n can mean a loss
// in n+1 ply and a return value +n can mean a win in n+1 ply. This
// cannot happen for tables with positions exactly on the "edge" of
// the 50-move rule.
//
// This means that if dtz > 0 is returned, the position is certainly
// a win if dtz + 50-move-counter <= 99. Care must be taken that the engine
// picks moves that preserve dtz + 50-move-counter <= 99.
//
// If n = 100 immediately after a capture or pawn move, then the position
// is also certainly a win, and during the whole phase until the next
// capture or pawn move, the inequality to be preserved is
// dtz + 50-movecounter <= 100.
//
// In short, if a move is available resulting in dtz + 50-move-counter <= 99,
// then do not accept moves leading to dtz + 50-move-counter == 100.
//
int TB_probe_dtz(Pos *pos, int *success)
{
  int wdl = TB_probe_wdl(pos, success);
  if (*success == 0) return 0;

  // If draw, then dtz = 0.
  if (wdl == 0) return 0;

  // Check for winning capture or en passant capture as only best move.
  if (*success == 2)
    return wdl_to_dtz[wdl + 2];

  ExtMove *end, *m = (pos->st-1)->endMoves;

  // If winning, check for a winning pawn move.
  if (wdl > 0) {
    // Generate at least all legal non-capturing pawn moves
    // including non-capturing promotions.
    // (The following calls in fact generate all moves.)
    if (!pos_checkers())
      end = generate_non_evasions(pos, m);
    else
      end = generate_evasions(pos, m);
    pos->st->endMoves = end;

    for (; m < end; m++) {
      Move move = m->move;
      if (type_of_p(moved_piece(move)) != PAWN || is_capture(pos, move)
                || !is_legal(pos, move))
        continue;
      do_move(pos, move, gives_check(pos, pos->st, move));
      int v = -TB_probe_wdl(pos, success);
      undo_move(pos, move);
      if (*success == 0) return 0;
      if (v == wdl)
        return wdl_to_dtz[wdl + 2];
    }
  }

  // If we are here, we know that the best move is not an ep capture.
  // In other words, the value of wdl corresponds to the WDL value of
  // the position without ep rights. It is therefore safe to probe the
  // DTZ table with the current value of wdl.

  int dtz = probe_dtz_table(pos, wdl, success);
  if (*success >= 0)
    return wdl_to_dtz[wdl + 2] + ((wdl > 0) ? dtz : -dtz);

  // *success < 0 means we need to probe DTZ for the other side to move.
  int best;
  if (wdl > 0) {
    best = INT32_MAX;
    // If wdl > 0, we have already generated all moves.
    m = (pos->st-1)->endMoves;
  } else {
    // If (cursed) loss, the worst case is a losing capture or pawn move
    // as the "best" move, leading to dtz of -1 or -101.
    // In case of mate, this will cause -1 to be returned.
    best = wdl_to_dtz[wdl + 2];
    // If wdl < 0, we still have to generate all moves.
    if (!pos_checkers())
      end = generate_non_evasions(pos, m);
    else
      end = generate_evasions(pos, m);
    pos->st->endMoves = end;
  }

  for (; m < end; m++) {
    Move move = m->move;
    // We can skip pawn moves and captures.
    // If wdl > 0, we already caught them. If wdl < 0, the initial value
    // of best already takes account of them.
    if (is_capture(pos, move) || type_of_p(moved_piece(move)) == PAWN
              || !is_legal(pos, move))
      continue;
    do_move(pos, move, gives_check(pos, pos->st, move));
    int v = -TB_probe_dtz(pos, success);
    if (   v == 1
        && pos_checkers()
        && generate_legal(pos, (pos->st-1)->endMoves) == (pos->st-1)->endMoves)
      best = 1;
    else if (wdl > 0) {
      if (v > 0 && v + 1 < best)
        best = v + 1;
    } else {
      if (v - 1 < best)
        best = v - 1;
    }
    undo_move(pos, move);
    if (*success == 0) return 0;
  }
  return best;
}

// Use the DTZ tables to rank and score all root moves in the list.
// A return value of 0 means that not all probes were successful.
int TB_root_probe_dtz(Pos *pos, RootMoves *rm)
{
  int v, success;

  // Obtain 50-move counter for the root position.
  int cnt50 = pos_rule50_count();

  // Check whether a position was repeated since the last zeroing move.
  // In that case, we need to be careful and play DTZ-optimal moves if
  // winning.
  int rep = pos->hasRepeated;

  // The border between draw and win lies at rank 1 or rank 900, depending
  // on whether the 50-move rule is used.
  int bound = option_value(OPT_SYZ_50_MOVE) ? 900 : 1;

  // Probe, rank and score each move.
  pos->st->endMoves = (pos->st-1)->endMoves;
  for (int i = 0; i < rm->size; i++) {
    RootMove *m = &rm->move[i];
    do_move(pos, m->pv[0], gives_check(pos, pos->st, m->pv[0]));

    // Calculate dtz for the current move counting from the root position.
    if (pos_rule50_count() == 0) {
      // If the move resets the 50-move counter, dtz is -101/-1/0/1/101.
      v = -TB_probe_wdl(pos, &success);
      v = wdl_to_dtz[v + 2];
    } else {
      // Otherwise, take dtz for the new position and correct by 1 ply.
      v = -TB_probe_dtz(pos, &success);
      if (v > 0) v++;
      else if (v < 0) v--;
    }
    // Make sure that a mating move gets value 1.
    if (pos_checkers() && v == 2) {
      if (generate_legal(pos, (pos->st-1)->endMoves) == (pos->st-1)->endMoves)
        v = 1;
    }

    undo_move(pos, m->pv[0]);
    if (!success) return 0;

    // Better moves are ranked higher. Guaranteed wins are ranked equally.
    // Losing moves are ranked equally unless a 50-move draw is in sight.
    // Note that moves ranked 900 have dtz + cnt50 == 100, which in rare
    // cases may be insufficient to win as dtz may be one off (see the
    // comments before TB_probe_dtz()).
    int r =  v > 0 ? (v + cnt50 <= 99 && !rep ? 1000 : 1000 - (v + cnt50))
           : v < 0 ? (-v * 2 + cnt50 < 100 ? -1000 : -1000 + (-v + cnt50))
           : 0;
    m->TBRank = r;

    // Determine the score to be displayed for this move. Assign at least
    // 1 cp to cursed wins and let it grow to 49 cp as the position gets
    // closer to a real win.
    m->TBScore =  r >= bound ? VALUE_MATE - MAX_MATE_PLY - 1
                : r >  0     ? max( 3, r - 800) * PawnValueEg / 200
                : r == 0     ? VALUE_DRAW
                : r > -bound ? min(-3, r + 800) * PawnValueEg / 200
                :             -VALUE_MATE + MAX_MATE_PLY + 1;
  }

  return 1;
}

// Use the WDL tables to rank all root moves in the list.
// This is a fallback for the case that some or all DTZ tables are missing.
// A return value of 0 means that not all probes were successful.
int TB_root_probe_wdl(Pos *pos, RootMoves *rm)
{
  static int wdl_to_rank[] = { -1000, -899, 0, 899, 1000 };
  static Value wdl_to_Value[] = {
    -VALUE_MATE + MAX_MATE_PLY + 1,
    VALUE_DRAW - 2,
    VALUE_DRAW,
    VALUE_DRAW + 2,
    VALUE_MATE - MAX_MATE_PLY - 1
  };

  int v, success;
  int move50 = option_value(OPT_SYZ_50_MOVE);

  // Probe, rank and score each move.
  pos->st->endMoves = (pos->st-1)->endMoves;
  for (int i = 0; i < rm->size; i++) {
    RootMove *m = &rm->move[i];
    do_move(pos, m->pv[0], gives_check(pos, pos->st, m->pv[0]));
    v = -TB_probe_wdl(pos, &success);
    undo_move(pos, m->pv[0]);
    if (!success) return 0;
    if (!move50)
      v = v > 0 ? 2 : v < 0 ? -2 : 0;
    m->TBRank = wdl_to_rank[v + 2];
    m->TBScore = wdl_to_Value[v + 2];
  }

  return 1;
}