/*
  Ethereal is a UCI chess playing engine authored by Andrew Grant.
  <https://github.com/AndyGrant/Ethereal>     <andrew@grantnet.us>
  
  Ethereal is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  
  Ethereal is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <assert.h>
#include <inttypes.h>
#include <pthread.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "bitutils.h"
#include "bitboards.h"
#include "board.h"
#include "castle.h"
#include "evaluate.h"
#include "history.h"
#include "piece.h"
#include "psqt.h"
#include "search.h"
#include "thread.h"
#include "transposition.h"
#include "types.h"
#include "time.h"
#include "move.h"
#include "movegen.h"
#include "movepicker.h"
#include "uci.h"

pthread_mutex_t LOCK = PTHREAD_MUTEX_INITIALIZER;

extern TransTable Table;

uint16_t getBestMove(Thread* threads, Board* board, Limits* limits, double start, double time, double mtg, double inc){
    
    int i, nthreads = threads[0].nthreads;
    
    SearchInfo info; memset(&info, 0, sizeof(SearchInfo));
    
    pthread_t* pthreads = malloc(sizeof(pthread_t) * nthreads);
    
    
    // Some initialization for time management
    info.starttime = start;
    info.bestMoveChanges = 0;
    
    // Ethereal is responsible for choosing how much time to spend searching
    if (limits->limitedBySelf){
        
        if (mtg >= 0){
            info.idealusage =  0.75 * time / (mtg +  5) + inc;
            info.maxalloc   =  4.00 * time / (mtg +  7) + inc;
            info.maxusage   = 10.00 * time / (mtg + 10) + inc;
        }
        
        else {
            info.idealusage =  0.52 * (time + 23 * inc) / 25;
            info.maxalloc   =  4.00 * (time + 23 * inc) / 25;
            info.maxusage   = 10.00 * (time + 23 * inc) / 25;
        }
        
        info.idealusage = MIN(info.idealusage, time - 100);
        info.maxalloc   = MIN(info.maxalloc,   time - 100);
        info.maxusage   = MIN(info.maxusage,   time - 100);
    }
    
    // UCI command told us to look for exactly X seconds
    if (limits->limitedByTime){
        info.idealusage = limits->timeLimit;
        info.maxalloc   = limits->timeLimit;
        info.maxusage   = limits->timeLimit;
    }
    
    // Setup the thread pool for a new search with these parameters
    newSearchThreadPool(threads, board, limits, &info);
    
    // Launch all of the threads
    for (i = 1; i < nthreads; i++)
        pthread_create(&pthreads[i], NULL, &iterativeDeepening, &threads[i]);
    iterativeDeepening((void*) &threads[0]);
    
    // Wait for all (helper) threads to finish
    for (i = 1; i < nthreads; i++)
        pthread_join(pthreads[i], NULL);
    
    // Cleanup pthreads
    free(pthreads);
    
    // Return highest depth best move
    return info.bestmoves[info.depth];
}

void* iterativeDeepening(void* vthread){
    
    Thread* const thread   = (Thread*) vthread;
    
    SearchInfo* const info = thread->info;
    
    Limits* const limits   = thread->limits;
   
    const int mainThread   = thread == &thread->threads[0];
    
    int i, count, value, depth, abort;
    
    
    for (depth = 1; depth < MAX_PLY; depth++){
        
        // Always acquire the lock before setting thread->depth. thread->depth
        // is needed by others to determine when to skip certain search iterations
        pthread_mutex_lock(&LOCK);
        
        thread->depth = depth;
        
        // Helper threads are subject to skipping depths in order to better help
        // the main thread, based on the number of threads already on some depths
        if (!mainThread){
        
            for (count = 0, i = 1; i < thread->nthreads; i++)
                count += thread != &thread->threads[i] && thread->threads[i].depth >= depth;

            if (depth > 1 && thread->nthreads > 1 && count >= thread->nthreads / 2){
                thread->depth = depth + 1;
                pthread_mutex_unlock(&LOCK);
                continue;
            }
        }
        
        // Drop the lock as we have finished depth scheduling
        pthread_mutex_unlock(&LOCK);
        
        // Set the abort location. If we exit the search unnaturally (very likely)
        // we will know by abort being set, and can therefore indicate an exit
        abort = setjmp(thread->jbuffer);
        if (abort) return NULL;
        
            
        // Perform the actual search for the current depth
        value = aspirationWindow(thread, depth);
        
        // Helper threads need not worry about time and search info updates
        if (!mainThread) continue;
        
        // Update the Search Info structure for the main thread
        info->depth = depth;
        info->values[depth] = value;
        info->bestmoves[depth] = thread->pv.line[0];
        info->timeUsage[depth] = getRealTime() - info->starttime - info->timeUsage[depth-1];
        
        // Send information about this search to the interface
        uciReport(thread->threads, -MATE, MATE, value);
        
        // If Ethereal is managing the clock, determine if we should be spending
        // more time on this search, based on the score difference between iterations
        // and any changes in the principle variation since the last iteration
        if (limits->limitedBySelf && depth >= 4){
            
            // Increase our time if the score suddently dropped by eight centipawns
            if (info->values[depth-1] > value + 10)
                info->idealusage *= 1.050;
            
            // Decrease our time if the score suddently jumped by eight centipawns
            if (info->values[depth-1] < value - 10)
                info->idealusage *= 0.975;
            
            if (info->bestmoves[depth] == info->bestmoves[depth-1]){
                
                // If we still have remaining increments from best move
                // changes reduce our ideal time usage by a factor, such that
                // after we deplete bestMoveChanges, we are near the original time
                info->idealusage *= info->bestMoveChanges ? 0.935 : 1.000;
                
                // We have recovered one best move change
                info->bestMoveChanges = MAX(0, info->bestMoveChanges - 1);
            }
            
            else {
                
                // Increase our time by based on our best move debt. If this is the
                // first PV change in some time, we increase our time by 48%. If we
                // have recently changed best moves, we will only adjust our usage
                // to get back to the initial 48% time allocation by the first change
                info->idealusage *= 1.000 + 0.080 * (6 - info->bestMoveChanges);
                
                // Set out counter back to six as the best move has changed
                info->bestMoveChanges = 6;
            }
            
            // Cap our ideal usage using our maximum allocation
            info->idealusage = MIN(info->idealusage, info->maxalloc);
        }
        
        // Check for termination by any of the possible limits
        if (   (limits->limitedByDepth && depth >= limits->depthLimit)
            || (limits->limitedByTime  && getRealTime() - info->starttime > limits->timeLimit)
            || (limits->limitedBySelf  && getRealTime() - info->starttime > info->maxusage)
            || (limits->limitedBySelf  && getRealTime() - info->starttime > info->idealusage)){
            
            // Terminate all helper threads
            for (i = 0; i < thread->nthreads; i++)
                thread->threads[i].abort = 1;
            return NULL;
        }
        
        // Check to see if we expect to be able to complete the next depth
        if (thread->limits->limitedBySelf){
            double timeFactor = info->timeUsage[depth] / MAX(1, info->timeUsage[depth-1]);
            double estimatedUsage = info->timeUsage[depth] * (timeFactor + .40);
            double estiamtedEndtime = getRealTime() + estimatedUsage - info->starttime;
            
            if (estiamtedEndtime > info->maxusage){
                
                // Terminate all helper threads
                for (i = 0; i < thread->nthreads; i++)
                    thread->threads[i].abort = 1;
                return NULL;
            }
        }
    }
    
    return NULL;
}

int aspirationWindow(Thread* thread, int depth){
    
    int* const values = thread->info->values;
    
    const int mainThread = thread == &thread->threads[0];
    
    int alpha, beta, value, upper, lower;
    
    int mainDepth = MAX(5, 1 + thread->info->depth);
    
    // Without at least a few searches, we cannot guess a good search window
    if (depth <= 4) return search(thread, &thread->pv, -MATE, MATE, depth, 0);

    // Dynamically compute the upper margin based on previous scores
    upper = MAX(   12,  1.6 * (values[mainDepth-1] - values[mainDepth-2]));
    upper = MAX(upper,  1.3 * (values[mainDepth-2] - values[mainDepth-3]));
    upper = MAX(upper,  1.0 * (values[mainDepth-3] - values[mainDepth-4]));
    
    // Dynamically compute the lower margin based on previous scores
    lower = MAX(   12, -1.6 * (values[mainDepth-1] - values[mainDepth-2]));
    lower = MAX(lower, -1.3 * (values[mainDepth-2] - values[mainDepth-3]));
    lower = MAX(lower, -1.0 * (values[mainDepth-3] - values[mainDepth-4])); 
    
    // Create the aspiration window
    alpha = MAX(-MATE, values[mainDepth-1] - lower);
    beta  = MIN( MATE, values[mainDepth-1] + upper);
    
    // Keep trying larger windows until one works
    for (;; lower *= 2, upper *= 2){
        
        // If we are nearing a mate, force a full search
        if (abs(alpha) >= MATE / 4) alpha = -MATE, beta = MATE;
        if (abs(beta ) >= MATE / 4) alpha = -MATE, beta = MATE;
        
        // Perform the search on the modified window
        value = search(thread, &thread->pv, alpha, beta, depth, 0);
        
        // Result was within our window
        if (value > alpha && value < beta) return value;
        
        // Report lower and upper bounds after at least 5 seconds
        if (mainThread && getRealTime() - thread->info->starttime >= 5000)
            uciReport(thread->threads, alpha, beta, value);
        
        // Search failed low
        if (value <= alpha) alpha = MAX(-MATE, alpha - 2 * lower);
        
        // Search failed high
        if (value >= beta)  beta  = MIN( MATE,  beta + 2 * upper);
    }
}

int search(Thread* thread, PVariation* pv, int alpha, int beta, int depth, int height){
    
    const int PvNode   = (alpha != beta - 1);
    const int RootNode = (height == 0);
    
    Board* const board = &thread->board;
    
    int i, repetitions, quiets = 0, played = 0, hist = 0;
    int R, newDepth, rAlpha, rBeta, ttValue, oldAlpha = alpha;
    int eval, value = -MATE, best = -MATE, futilityMargin = -MATE;
    int inCheck, isQuiet, improving, checkExtended, extension, bestWasQuiet = 0;
    
    uint16_t move, ttMove = NONE_MOVE, bestMove = NONE_MOVE, quietsTried[MAX_MOVES];
    
    Undo undo[1];
    EvalInfo ei;
    PVariation lpv;
    TransEntry ttEntry;
    MovePicker movePicker;
    
    lpv.length = 0;
    pv->length = 0;
    
    // Increment nodes counter for this Thread
    thread->nodes++;
    
    // Update longest searched line for this Thread
    thread->seldepth = RootNode ? 0 : MAX(thread->seldepth, height);
    
    // Step 1A. Check to see if search time has expired. We will force the search
    // to continue after the search time has been used in the event that we have
    // not yet completed our depth one search, and therefore would have no best move
    if (   (thread->limits->limitedBySelf || thread->limits->limitedByTime)
        && (thread->nodes & 1023) == 1023
        &&  getRealTime() >= thread->info->starttime + thread->info->maxusage
        &&  thread->depth > 1)
        longjmp(thread->jbuffer, 1);
        
    // Step 1B. Check to see if the master thread finished
    if (thread->abort) longjmp(thread->jbuffer, 1);
        
    // Step 2. Check for early exit conditions, including the fifty move rule,
    // mate distance pruning, max depth exceeded, or drawn by repitition. We
    // will not take any of these exits in the Root Node, or else we would not
    // have any move saved into the principle variation to send to the GUI
    if (!RootNode){
        
        // Check to see if we have exceeded the maxiumum search draft
        if (height >= MAX_PLY)
            return evaluateBoard(board, &ei, &thread->pktable);
        
        // Mate Distance Pruning. Check to see if this line is so
        // good, or so bad, that being mated in the ply, or  mating in 
        // the next one, would still not create a more extreme line
        rAlpha = alpha > -MATE + height     ? alpha : -MATE + height;
        rBeta  =  beta <  MATE - height - 1 ?  beta :  MATE - height - 1;
        if (rAlpha >= rBeta) return rAlpha;
        
        // Check for the Fifty Move Rule
        if (board->fiftyMoveRule > 100)
            return 0;
        
        // Check for three fold repetition. If the repetition occurs since
        // the root move of this search, we will exit early as if it was a draw.
        // Otherwise, we will look for an actual three fold repetition draw.
        for (repetitions = 0, i = board->numMoves - 2; i >= 0; i -= 2){
            
            // We can't have repeated positions before the most recent
            // move which triggered a reset of the fifty move rule counter
            if (i < board->numMoves - board->fiftyMoveRule) break;
            
            if (board->history[i] == board->hash){
                
                // Repetition occured after the root
                if (i > board->numMoves - height)
                    return 0;
                
                // An actual three fold repetition
                if (++repetitions == 2)
                    return 0;
            }
        }
    }
    
    // Step 3. Probe the Transposition Table for an entry
    if (getTranspositionEntry(&Table, board->hash, &ttEntry)){
        
        // Entry move may be good in this position
        ttMove = ttEntry.bestMove;
        
        // Step 3A. Check to see if this entry allows us to exit this
        // node early. We choose not to do this in the PV line, not because
        // we can't, but because don't want truncated PV lines. Except in
        // the case where we would otherwise fall into a qsearch. A table
        // entry is going to provide a better return value than qsearch
        if (   (depth == 0 || !PvNode)
            &&  ttEntry.depth >= depth){

            // Adjust if the table has a mate score
            ttValue = valueFromTT(ttEntry.value, height);
            
            // Saved score and bound allows a beta cutoff
            if (    ttValue >= beta
                && (ttEntry.type == PVNODE || ttEntry.type == CUTNODE))
                return beta;
                
            // Saved score and bound allows an alpha cutoff
            if (    ttValue <= alpha
                && (ttEntry.type == PVNODE || ttEntry.type == ALLNODE))
                return alpha;
                
            // Saved score is within our window and is an exact result,
            // allowing us to return ttValue instead of searching again
            if (ttEntry.type == PVNODE){
                assert(ttValue > alpha && ttValue < beta);
                return ttValue;
            }
        }
    }
    
    // Step 4. Go into the Quiescence Search if we have reached
    // the search horizon and are not currently in check
    if (depth <= 0){
        
        // No king attackers indicates we are not checked. We reduce the
        // node count here, in order to avoid counting this node twice
        if (!board->kingAttackers)
            return thread->nodes--, qsearch(thread, pv, alpha, beta, height);

        // Search expects depth to be greater than or equal to 0
        depth = 0; 
    }
    
    // Step 5. Initialize flags and values used by pruning and search methods
    
    // We can grab in check based on the already computed king attackers bitboard
    inCheck = !!board->kingAttackers;
    
    // Here we perform our check extension, for non-root pvnodes, or for non-root
    // nodes near depth zero. Note that when we bypass the qsearch as a result of
    // being in check, we set depth to zero. This step adjusts depth back to one.
    checkExtended = inCheck && !RootNode && depth <= 8;
    depth += inCheck && !RootNode && depth <= 8;
    
    // Compute and save off a static evaluation. Also, compute our futilityMargin
    eval = thread->evalStack[height] = evaluateBoard(board, &ei, &thread->pktable);
    futilityMargin = eval + FutilityMargin * depth;
    
    // Finally, we define a node to be improving if the last two moves have increased
    // the static eval. To have two last moves, we must have a height of at least 4.
    improving =    height >= 4
               &&  thread->evalStack[height-0] > thread->evalStack[height-2]
               &&  thread->evalStack[height-2] > thread->evalStack[height-4];
    
    // Step 6. Razoring. If a Quiescence Search for the current position
    // still falls way below alpha, we will assume that the score from
    // the Quiescence search was sufficient. For depth 1, we will just
    // return a Quiescence Search score because it is unlikely a quiet
    // move would close the massive gap between the evaluation and alpha
    if (   !PvNode
        && !inCheck
        &&  depth <= RazorDepth
        &&  eval + RazorMargins[depth] < alpha){
            
        if (depth <= 1)
            return qsearch(thread, pv, alpha, beta, height);
        
        rAlpha = alpha - RazorMargins[depth];
        value = qsearch(thread, pv, rAlpha, rAlpha + 1, height);
        if (value <= rAlpha) return alpha;
    }
    
    // Step 7. Beta Pruning / Reverse Futility Pruning / Static Null
    // Move Pruning. If the eval is few pawns above beta then exit early
    if (   !PvNode
        && !inCheck
        &&  depth <= BetaPruningDepth
        &&  eval - BetaMargin * depth > beta)
        return beta;

    // Step 8. Null Move Pruning. If our position is so good that
    // giving our opponent back-to-back moves is still not enough
    // for them to gain control of the game, we can be somewhat safe
    // in saying that our position is too good to be true
    if (   !PvNode
        && !inCheck
        &&  depth >= NullMovePruningDepth
        &&  eval >= beta
        &&  hasNonPawnMaterial(board, board->turn)
        &&  board->history[board->numMoves-1] != NULL_MOVE){
            
        R = 4 + depth / 6 + (eval - beta + 200) / 400;
            
        applyNullMove(board, undo);
        
        value = -search(thread, &lpv, -beta, -beta + 1, depth - R, height + 1);
        
        revertNullMove(board, undo);
        
        if (value >= beta) return beta;
    }
    
    // Step 9. ProbCut. If we have a good capture that causes a beta cutoff
    // with a slightly reduced depth search it is likely that this capture is
    // likely going to be good at a full depth. To save some work we will prune
    // captures that won't exceed rbeta or captures that fail at a low depth
    if (   !PvNode
        && !inCheck
        &&  abs(beta) < MATE_IN_MAX
        &&  depth >= ProbCutDepth
        &&  eval + bestTacticalMoveValue(board, &ei) >= beta + ProbCutMargin){
            
        rBeta = MIN(beta + ProbCutMargin, MATE - MAX_PLY - 1);
            
        initializeMovePicker(&movePicker, thread, NONE_MOVE, height, 1);
        
        while ((move = selectNextMove(&movePicker, board)) != NONE_MOVE){
            
            // Even if we keep the capture piece and or the promotion piece
            // we will fail to exceed rBeta, then we will skip this move
            if (eval + thisTacticalMoveValue(board, move) < rBeta)
                continue;
            
            // Apply and validate move before searching
            applyMove(board, move, undo);
            if (!isNotInCheck(board, !board->turn)){
                revertMove(board, move, undo);
                continue;
            }
            
            // Verify the move is good with a depth zero search (qsearch, unless in check)
            // and then with a slightly reduced search. If both searches still exceed rBeta,
            // we will prune this node's subtree with resonable assurance that we made no error
            if (   -search(thread, &lpv, -rBeta, -rBeta+1,       0, height+1) >= rBeta
                && -search(thread, &lpv, -rBeta, -rBeta+1, depth-4, height+1) >= rBeta){
                    
                revertMove(board, move, undo);
                return beta;
            }
             
            // Revert the board state
            revertMove(board, move, undo);
        }
    }
    
    // Step 10. Internal Iterative Deepening. Searching PV nodes without
    // a known good move can be expensive, so a reduced search first
    if (    PvNode
        &&  ttMove == NONE_MOVE
        &&  depth >= InternalIterativeDeepeningDepth){
        
        // Search with a reduced depth
        value = search(thread, &lpv, alpha, beta, depth-2, height);
        
        // Probe for the newly found move, and update ttMove
        if (getTranspositionEntry(&Table, board->hash, &ttEntry))
            ttMove = ttEntry.bestMove;
    }
    
    // Step 11. Initialize the Move Picker and being searching through each
    // move one at a time, until we run out or a move generates a cutoff
    initializeMovePicker(&movePicker, thread, ttMove, height, 0);
    while ((move = selectNextMove(&movePicker, board)) != NONE_MOVE){
        
        // If this move is quiet we will save it to a list of attemped quiets.
        // Also lookup the history score, as we will in most cases need it.
        if ((isQuiet = !moveIsTactical(board, move))){
            quietsTried[quiets++] = move;
            hist = getHistoryScore(thread->history, move, board->turn);
        }
        
        // Step 12. Futility Pruning. If our score is far below alpha,
        // and we don't expect anything from this move, we can skip this
        // one, and also skip all other quiet moves from this position
        if (   !PvNode
            &&  isQuiet
            &&  best > MATED_IN_MAX
            && (hist < 4096 || !improving)
            &&  futilityMargin <= alpha
            &&  depth <= FutilityPruningDepth)
            break;
            
        // Step 13. Weak Capture Pruning. Prune this capture if it is capturing
        // a weaker piece which is protected, so long as we do not have any 
        // additional support for the attacker. This is done for only some depths
        if (    !PvNode
            &&  !isQuiet
            &&  !inCheck
            &&   best > MATED_IN_MAX
            &&   captureIsWeak(board, &ei, move, depth))
            continue;
        
        // Step 14. Late Move Pruning / Move Count Pruning. If we have
        // tried many quiets in this position already, and we don't expect
        // anything from this move, we can undo it and skip all remaining quiets
        if (   !PvNode
            &&  isQuiet
            &&  best > MATED_IN_MAX
            && (hist < 4096 || !improving)
            &&  depth <= LateMovePruningDepth
            &&  quiets > LateMovePruningCounts[depth])
            break;
        
        // Apply the move, and verify legality
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }
        
        // Update counter of moves actually played
        played += 1;
    
        // Step 15. Late Move Reductions. We will search some moves at a
        // lower depth. If they look poor at a lower depth, then we will
        // move on. If they look good, we will search with a full depth.
        if (    played >= 4
            &&  depth >= 3
            &&  isQuiet){
            
            // Baseline R based on number of moves played and current depth
            R = 2 + (played - 4) / 8 + (depth - 6) / 4;
            
            // Increase R by an additional two ply for non PvNodes
            R += 2 * !PvNode;
            
            // Decrease R by an additional ply if we have a quiet move as our best
            // move, or we are looking at an early quiet move in a situation where
            // we either have no table move, or the table move is not the best so far
            R -= bestWasQuiet || (ttMove != bestMove && quiets <= 2);
            
            // Adjust R based on history score. We will not allow history to increase
            // R by more than 1. History scores are within [-16384, 16384], so we can
            // expect an adjustment on the bounds of [+1, -6], with 6 being very rare
            R -= MAX(-1, ((hist + 8192) / 4096) - (hist <= -8192));
            
            // Do not allow the reduction to take us directly into a quiescence search
            // and also ensure that R is at least one, therefore avoiding extensions
            R  = MIN(depth - 1, MAX(R, 1));
            
        } else R = 1;
        
        // Step 16A. Singular Move Extensions. If we are looking at a table move,
        // and it seems that under some conditions, the table move is better than
        // all other possible moves, we will extend the search of the table move
        extension =  !RootNode
                  && !checkExtended
                  &&  depth >= 10
                  &&  move == ttMove
                  &&  ttEntry.depth >= depth - 3
                  && (ttEntry.type == PVNODE || ttEntry.type == CUTNODE)
                  &&  moveIsSingular(thread, board, &ttEntry, undo, depth, height);
                  
        // Step 16B. Check Extensions. If we are in a PvNode and we have not already
        // extended the depth before the move loop, and this move is not singular,
        // then we will extend it if we have a capture of a quiet with a good history,
        // or if the node is improving, ie we expect something to beat alpha
        extension +=   PvNode
                   &&  inCheck
                   && !extension
                   && !checkExtended
                   && (improving || !isQuiet || hist >= 2048);
            
        // New depth is what our search depth would be, assuming that we do no LMR
        newDepth = depth + extension;
        
        // Step 17A. If we triggered the LMR conditions (which we know by the value of R),
        // then we will perform a reduced search on the null alpha window, as we have no
        // expectation that this move will be worth looking into deeper
        if (R != 1) value = -search(thread, &lpv, -alpha-1, -alpha, newDepth-R, height+1);
        
        // Step 17B. There are two situations in which we will search again on a null window,
        // but without a depth reduction R. First, if the LMR search happened, and failed
        // high, secondly, if we did not try an LMR search, and this is not the first move
        // we have tried in a PvNode, we will research with the normally reduced depth
        if ((R != 1 && value > alpha) || (R == 1 && !(PvNode && played == 1)))
            value = -search(thread, &lpv, -alpha-1, -alpha, newDepth-1, height+1);
        
        // Step 17C. Finally, if we are in a PvNode and a move beat alpha while being
        // search on a reduced depth, we will search again on the normal window. Also,
        // if we did not perform Step 18B, we will search for the first time on the
        // normal window. This happens only for the first move in a PvNode
        if (PvNode && (played == 1 || value > alpha))
            value = -search(thread, &lpv, -beta, -alpha, newDepth-1, height+1);

        // Revert the board state
        revertMove(board, move, undo);
        
        // Step 18. Update search stats for the best move and its value. Update
        // our lower bound (alpha) if exceeded, and also update the PV in that case
        if (value > best){
            
            best = value;
            bestMove = move;
            bestWasQuiet = isQuiet;
            
            if (value > alpha){
                alpha = value;
                
                // Copy our child's PV and prepend this move to it
                pv->length = 1 + lpv.length;
                pv->line[0] = move;
                memcpy(pv->line + 1, lpv.line, sizeof(uint16_t) * lpv.length);
            }
        }
        
        // Step 21. Search has failed high. Update Killer Moves and exit search
        if (alpha >= beta){
            
            if (isQuiet && thread->killers[height][0] != move){
                thread->killers[height][1] = thread->killers[height][0];
                thread->killers[height][0] = move;
            }
            
            break;
        }
    }
    
    // Step 20. Stalemate and Checkmate detection. If no moves were found to
    // be legal (search makes sure to play at least one legal move, if any),
    // then we are either mated or stalemated, which we can tell by the inCheck
    // flag. For mates, return a score based on the distance from root, so we
    // can differentiate between close mates and far away mates from the root
    if (played == 0) return inCheck ? -MATE + height : 0;
    
    // Step 21. Update History counters on a fail high for a quiet move
    if (best >= beta && !moveIsTactical(board, bestMove)){
        updateHistory(thread->history, bestMove, board->turn, depth*depth);
        for (i = 0; i < quiets - 1; i++)
            updateHistory(thread->history, quietsTried[i], board->turn, -depth*depth);
    }
    
    // Step 22. Store the results of the search in the transposition table.
    // We must determine a bound for the result based on alpha and beta, and
    // must also convert the search value to a tt value, which handles mates
    storeTranspositionEntry(&Table, depth, (best > oldAlpha && best < beta)
                            ? PVNODE : best >= beta ? CUTNODE : ALLNODE,
                            valueToTT(best, height), bestMove, board->hash);
                            
    return best;
}

int qsearch(Thread* thread, PVariation* pv, int alpha, int beta, int height){
    
    Board* const board = &thread->board;
    
    int eval, value, best;
    uint16_t move;
    Undo undo[1];
    MovePicker movePicker;
    EvalInfo ei;
    
    PVariation lpv;
    lpv.length = 0;
    pv->length = 0;
    
    // Increment nodes counter for this Thread
    thread->nodes++;
    
    // Update longest searched line for this Thread
    thread->seldepth = MAX(thread->seldepth, height);
    
    // Step 1A. Check to see if search time has expired. We will force the search
    // to continue after the search time has been used in the event that we have
    // not yet completed our depth one search, and therefore would have no best move
    if (   (thread->limits->limitedBySelf || thread->limits->limitedByTime)
        && (thread->nodes & 1023) == 1023
        &&  getRealTime() >= thread->info->starttime + thread->info->maxusage
        &&  thread->depth > 1)
        longjmp(thread->jbuffer, 1);
        
    // Step 1B. Check to see if the master thread finished
    if (thread->abort) longjmp(thread->jbuffer, 1);
    
    // Step 2. Max Draft Cutoff. If we are at the maximum search draft,
    // then end the search here with a static eval of the current board
    if (height >= MAX_PLY)
        return evaluateBoard(board, &ei, &thread->pktable);
    
    // Step 3. Eval Pruning. If a static evaluation of the board will
    // exceed beta, then we can stop the search here. Also, if the static
    // eval exceeds alpha, we can call our static eval the new alpha
    best = value = eval = evaluateBoard(board, &ei, &thread->pktable);
    alpha = MAX(alpha, value);
    if (alpha >= beta) return value;
    
    // Step 4. Delta Pruning. Even the best possible capture and or promotion
    // combo with the additional of the futility margin would still fall below alpha
    if (value + QFutilityMargin + bestTacticalMoveValue(board, &ei) < alpha)
        return eval;
    
    // Step 5. Move Generation and Looping. Generate all tactical moves for this
    // position (includes Captures, Promotions, and Enpass) and try them
    initializeMovePicker(&movePicker, thread, NONE_MOVE, height, 1);
    while ((move = selectNextMove(&movePicker, board)) != NONE_MOVE){
        
        // Step 6. Futility Pruning. Similar to Delta Pruning, if this capture in the
        // best case would still fail to beat alpha minus some margin, we can skip it
        if (eval + QFutilityMargin + thisTacticalMoveValue(board, move) < alpha)
            continue;
        
        // Step 7. Weak Capture Pruning. If we are trying to capture a piece which
        // is protected, and we are the sole attacker, then we can be somewhat safe
        // in skipping this move so long as we are capturing a weaker piece
        if (captureIsWeak(board, &ei, move, 0))
            continue;
        
        // Apply and validate move before searching
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }
        
        // Search next depth
        value = -qsearch(thread, &lpv, -beta, -alpha, height+1);
        
        // Revert move from board
        revertMove(board, move, undo);
        
        // Improved current value
        if (value > best){
            best = value;
            
            // Improved current lower bound
            if (value > alpha){
                alpha = value;
                
                // Update the Principle Variation
                pv->length = 1 + lpv.length;
                pv->line[0] = move;
                memcpy(pv->line + 1, lpv.line, sizeof(uint16_t) * lpv.length);
            }
        }
        
        // Search has failed high
        if (alpha >= beta)
            return best;
    }
    
    return best;
}

int moveIsTactical(Board* board, uint16_t move){
    return board->squares[MoveTo(move)] != EMPTY
        || MoveType(move) == PROMOTION_MOVE
        || MoveType(move) == ENPASS_MOVE;
}

int hasNonPawnMaterial(Board* board, int turn){
    uint64_t friendly = board->colours[turn];
    uint64_t kings = board->pieces[KING];
    uint64_t pawns = board->pieces[PAWN];
    return (friendly & (kings | pawns)) != friendly;
}

int valueFromTT(int value, int height){
    return value >=  MATE_IN_MAX ? value - height
         : value <= MATED_IN_MAX ? value + height
         : value;
}

int valueToTT(int value, int height){
    return value >=  MATE_IN_MAX ? value + height
         : value <= MATED_IN_MAX ? value - height
         : value;
}

int thisTacticalMoveValue(Board* board, uint16_t move){
    
    int value = PieceValues[PieceType(board->squares[MoveTo(move)])][EG];
    
    if (MoveType(move) == PROMOTION_MOVE)
        value += PieceValues[MovePromoPiece(move)][EG] - PieceValues[PAWN][EG];
    
    if (MoveType(move) == ENPASS_MOVE)
        value += PieceValues[PAWN][EG];
    
    return value;
}

int bestTacticalMoveValue(Board* board, EvalInfo* ei){
    
    int value = 0;
    
    // Look at enemy pieces we attacked to get a best value for our
    // moves. If the board is a known draw then we have not computed
    // any attack information, so we just look at all enemy pieces
    uint64_t targets =  board->colours[!board->turn]
                     & (ei->positionIsDrawn ? ~0ull : ei->attacked[board->turn]);
    
    // We may have a queen capture
    if (targets & board->pieces[QUEEN]) 
        value += PieceValues[QUEEN][EG];
    
    // We may have a rook capture
    else if (targets & board->pieces[ROOK])
        value += PieceValues[ROOK][EG];
    
    // We may have a minor capture
    else if (targets & (board->pieces[KNIGHT] | board->pieces[BISHOP]))
        value += MAX(
            !!(targets & board->pieces[KNIGHT]) * PieceValues[KNIGHT][EG],
            !!(targets & board->pieces[BISHOP]) * PieceValues[BISHOP][EG]
        );
        
    // We may have a pawn capture
    else if (targets & board->pieces[PAWN])
        value += PieceValues[PAWN][EG];
    
    // We may have an enpass capture
    else if (board->epSquare != -1)
        value += PieceValues[PAWN][EG];
        
    
    // See if we have any pawns on promoting ranks. If so, assume that
    // we can promote one of our pawns to at least a queen
    if (   board->pieces[PAWN] 
        &  board->colours[board->turn]
        & (board->turn == WHITE ? RANK_7 : RANK_2))
        value += PieceValues[QUEEN][EG] - PieceValues[PAWN][EG];
            
    return value;
}

int captureIsWeak(Board* board, EvalInfo* ei, uint16_t move, int depth){
    
    // If we lack the sufficient depth, the position was drawn and thus
    // no attackers were computed, or the capture we are looking at is
    // supported by another piece, then this capture is not a weak one
    if (    depth > WeakCaptureTwoAttackersDepth
        ||  ei->positionIsDrawn
        || (ei->attackedBy2[board->turn] & (1ull << MoveTo(move))))
        return 0;
        
    // Determine how valuable our attacking piece is
    int attackerValue = PieceValues[PieceType(board->squares[MoveFrom(move)])][EG];
        
    // This capture is not weak if we are attacking an equal or greater valued piece, 
    if (thisTacticalMoveValue(board, move) >= attackerValue)
        return 0;
    
    // Thus, the capture is weak if there are sufficient attackers for a given depth
    return (   (depth <= WeakCaptureTwoAttackersDepth
            &&  ei->attackedBy2[!board->turn] & (1ull << MoveTo(move)))
            || (depth <= WeakCaptureOneAttackersDepth
            &&  ei->attacked[!board->turn] & (1ull << MoveTo(move))));
}

int moveIsSingular(Thread* thread, Board* board, TransEntry* ttEntry, Undo* undo, int depth, int height){
    
    uint16_t move;
    MovePicker movePicker;
    int value = -MATE;
    int rBeta = MAX(ttEntry->value - 2 * depth, -MATE);
    
    // Use a dummy lpv, as we will throw it away
    PVariation lpv; lpv.length = 0;
    
    // We check for move singularity after we have already applied the move.
    // Thus we must revert the move, check for singularity, and reapply it
    revertMove(board, ttEntry->bestMove, undo);
    
    // Search over each move, we will skip the ttMove inside the loop
    initializeMovePicker(&movePicker, thread, NONE_MOVE, height, 0);
    while ((move = selectNextMove(&movePicker, board)) != NONE_MOVE){
        
        // Don't search the move we are checking for singularity
        if (move == ttEntry->bestMove) continue;
        
        // Make the move, and verify legality before searching
        // Verify legality before searching
        applyMove(board, move, undo);
        if (!isNotInCheck(board, !board->turn)){
            revertMove(board, move, undo);
            continue;
        }
        
        // Perform a reduced depth search on a null rbeta window
        value = -search(thread, &lpv, -rBeta-1, -rBeta, depth / 2 - 1, height+1);
        
        // Set the board state to what it was initially
        revertMove(board, move, undo);
        
        // Move failed high, thus ttMove is not singular
        if (value > rBeta) break;
    }
    
    // Fix the board state to what it was initially
    applyMove(board, ttEntry->bestMove, undo);

    // Move in singular if all evals failed low
    return value <= rBeta;    
}