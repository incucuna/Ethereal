#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <time.h>

#include "board.h"
#include "castle.h"
#include "evaluate.h"
#include "magics.h"
#include "piece.h"
#include "search.h"
#include "transposition.h"
#include "types.h"
#include "move.h"
#include "movegen.h"
#include "movegentest.h"
#include "zorbist.h"


time_t StartTime;
time_t EndTime;

long NodesSearched;
int EvaluatingPlayer;

uint16_t KillerMoves[MaxHeight][MaxKillers];

TranspositionTable Table;

uint16_t get_best_move(Board * board, int seconds){
	
	int value, depth, i, size=0;
	
	StartTime = time(NULL);
	EndTime = StartTime + seconds;
	
	NodesSearched = 0;
	EvaluatingPlayer = board->turn;
	
	init_transposition_table(&Table, 24);
	
	clock_t start = clock();
	
	printf("Starting Search, alloted_time=%d\n",seconds);
	printf("Initial Value = %d",evaluate_board(board));
	print_board(board);
	
	for (depth = 1; depth < MaxDepth; depth++){
		value = alpha_beta_prune(board,-Mate,Mate,depth,0);
		
		
		printf("depth %d score %d Nodes %d Seconds %d\n",depth,value,NodesSearched,time(NULL)-StartTime);
		
		
		if (time(NULL) - StartTime > seconds)
			break;
	}
	
	uint16_t best_move = (get_transposition_entry(&Table, board->hash))->best_move;	
	dump_transposition_table(&Table);
	
	return best_move;
}

int alpha_beta_prune(Board * board, int alpha, int beta, int depth, int height){
	
	// Alloted Time has Expired
	if (EndTime < time(NULL))
		return board->turn == EvaluatingPlayer ? -Mate : Mate;
	
	// Max Depth Reached
	if (depth == 0)
		//return quiescence_search(board,alpha,beta,height);
		return evaluate_board(board);
	
	// Max Height Reached
	if (height >= MaxHeight)
		return quiescence_search(board,alpha,beta,height);
	
	// Updated Node Counter
	NodesSearched += 1;
	
	// For Transposition Table
	uint16_t best_move = NoneMove;
	int used_table_entry = 0;	
	
	/*TranspositionEntry * entry = get_transposition_entry(&Table, board->hash);
	if (entry != NULL && entry->depth >= depth && board->turn == entry->turn){
		if (entry->type == PVNODE)
			return entry->value;
		else if (entry->type == CUTNODE && entry->value > alpha)
			alpha = entry->value;
		else if (entry->type == ALLNODE && entry->value < beta)
			beta = entry->value;
		
		if (alpha >= beta)
			return entry->value;
		
		used_table_entry = 1;
	}
	
	int initial_alpha = alpha;*/

	// Storage to use moves
	Undo undo[1];
	int i, size = 0;
	uint16_t moves[256];
	
	// Storage for search outputs
	int value, best = -Mate;
	
	gen_all_moves(board,moves,&size);
	
	// Use heuristic to sort moves
	//sort_moves(board,moves,size,depth,height,entry);
	
	for (i = 0; i < size; i++){
		apply_move(board,moves[i],undo);
		
		// Ensure move is Legal
		if (!is_not_in_check(board,!board->turn)){
			revert_move(board,moves[i],undo);
			continue;
		}
		
		//if (i < 4)
			value = -alpha_beta_prune(board,-beta,-alpha,depth-1,height+1);
		//else {
		//	value = -alpha_beta_prune(board,-alpha-1,-alpha,depth-1,height+1);
		//	if (value > alpha)
		//		value = -alpha_beta_prune(board,-beta,-value,depth-1,height+1);
		//}
		
		revert_move(board,moves[i],undo);
		
		// Update Search Bounds
		if (value > best){				
			best = value;
			best_move = moves[i];
	
			if (best > alpha){
				alpha = best;	
			}
		}
		
		if (alpha > beta){
			KillerMoves[height][2] = KillerMoves[height][1];
			KillerMoves[height][1] = KillerMoves[height][0];
			KillerMoves[height][0] = moves[i];
			break;
		}
	}
	
	/*if (!used_table_entry && EndTime > time(NULL)){
		if (best > initial_alpha && best < beta)
			store_transposition_entry(&Table, depth, board->turn,  PVNODE, best, best_move, board->hash);
		else if (best >= beta)
			store_transposition_entry(&Table, depth, board->turn, CUTNODE, best, best_move, board->hash);
		else if (best <= initial_alpha)
			store_transposition_entry(&Table, depth, board->turn, ALLNODE, best, best_move, board->hash);
	}*/
	
	if (height == 0)
		print_move(best_move);
	
	return best;
}

int quiescence_search(Board * board, int alpha, int beta, int height){
	if (height >= MaxHeight)
		return evaluate_board(board);
	
	int value = evaluate_board(board);
	
	if (value > alpha)
		alpha = value;
	
	if (alpha > beta)
		return value;
	
	NodesSearched += 1;
	
	Undo undo[1];
	int i, size = 0;
	uint16_t moves[256];
	
	int best = value;
	
	gen_all_moves(board,moves,&size);
	
	sort_moves(board,moves,size,0,height,NULL);
	
	uint64_t enemy = board->colourBitBoards[!board->turn];
	
	for(i = 0; i < size; i++){
		if (MOVE_TYPE(moves[i]) == NormalMove){
			if (enemy & (1ull << (MOVE_TO(moves[i])))){
				apply_move(board,moves[i],undo);
				
				if (!is_not_in_check(board,!board->turn)){
					revert_move(board,moves[i],undo);
					continue;
				}
				
				value = -quiescence_search(board,-beta,-alpha,height+1);
				
				revert_move(board,moves[i],undo);
				
				if (value > best)
					best = value;
				if (best > alpha)
					alpha = best;
				if (alpha > beta){
					KillerMoves[height][2] = KillerMoves[height][1];
					KillerMoves[height][1] = KillerMoves[height][0];
					KillerMoves[height][0] = moves[i];
					break;
				}
			}
		}
	}
	
	return best;
}

void sort_moves(Board * board, uint16_t * moves, int size, int depth, int height, TranspositionEntry * entry){
	int values[size], value;
	int i, j;
	
	int temp_value;
	uint16_t temp_move;
	
	uint16_t entry_move = NoneMove;
	uint16_t killer1 = KillerMoves[height][0];
	uint16_t killer2 = KillerMoves[height][2];
	uint16_t killer3 = KillerMoves[height][3];
	
	if (entry != NULL)
		entry_move = entry->best_move;
	
	for (i = 0; i < size; i++){
		value  = 8196 * (entry_move == moves[i]);
		value += 4096 * (   killer1 == moves[i]);
		value += 2048 * (   killer2 == moves[i]);
		value += 1024 * (   killer3 == moves[i]);
		value += PieceValues[PIECE_TYPE(board->squares[MOVE_TO(moves[i])])];
		value -= PieceValues[PIECE_TYPE(board->squares[MOVE_FROM(moves[i])])];
		values[i] = value;
	}
	
	for (i = 0; i < size; i++){
		for (j = i + 1; j < size; j++){
			if (values[j] > values[i]){
				temp_value = values[j];
				temp_move = moves[j];
				
				values[j] = values[i];
				moves[j] = moves[i];
				
				values[i] = temp_value;
				moves[i] = temp_move;
			}
		}
	}
}

int evaluate_board(Board * board){
	int value = board->opening;
	return board->turn == ColourWhite ? value : -value;
}