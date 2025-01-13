package ss.pentago.model.player.strategy;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;

import java.util.ArrayList;
import java.util.List;

/**
 * {@code MinMaxStrategy} is a type of {@code Strategy} that determines its moves
 * using a min-max algorithm. By default it looks 3 moves ahead.
 */
public class MinMaxStrategy implements Strategy {

    private final Boolean[] bools = {true, false};

    /**
     * How far ahead the AI looks.
     */
    private static final int HEAD = 3;

    private int startHead;
    private List<Integer> ratio;

    /**
     * @return the name of the strategy
     */
    //@ pure
    @Override
    public String getName() {
        return "Min Max";
    }

    /**
     * Determines a move according to the min max algorithm.
     * Get best move from looking {@code HEAD} moves ahead.
     *
     * @param board  the current game board
     * @param marble the player's marble
     * @return a strategical move
     */
    /*@
        requires board != null && marble != Marble.EMPTY;
        ensures board.isEmptyField(\result.getPosition());
    */
    //@ pure
    @Override
    public Move determineMove(Board board, Marble marble) {
        Marble opponentMarble = Marble.getOppositeOf(marble);
        startHead = Math.min(board.getNumberOfEmptySpots(), HEAD);
        ratio = calculateRatio(startHead - 1, board.getNumberOfEmptySpots() - 1);
        return makeFirstBranch(board, marble, opponentMarble, startHead);
    }

    /**
     * Make first branch that going to calculate all number of wins and loses at each branch
     * and output the best branch.
     * Wins is + and loses is - and it calculate as ratio which mean if loses or wins happen
     * earlier in the branch the ratio would be higher.
     *
     * @param board the board
     * @param ahead number of move calculated ahead
     * @return the best Move
     */
    //@ requires board != null;
    private Move makeFirstBranch(Board board, Marble marble, Marble opponentMarble, int ahead) {
        int emptySpot = board.getNumberOfEmptySpots();
        if (emptySpot >= 34) {
            return randomMove(board);
        }

        List<Move> moves = new ArrayList<>();
        List<Integer> wins = new ArrayList<>();

        for (int i = 0; i < Board.DIM * Board.DIM && board.isEmptyField(i); i++) {
            Board positionBoard = board.deepCopy();
            positionBoard.setField(i, marble);

            for (Quadrant q : Quadrant.values()) {
                for (Boolean bool : bools) {

                    Board fullMoveBoard = positionBoard.deepCopy();
                    Rotation rotation = new Rotation(q, bool);
                    Move move = new Move(i, rotation);
                    fullMoveBoard.rotate(rotation);

                    if (fullMoveBoard.hasWinner() == marble) {
                        // If this move is a win for us, return it
                        return move;
                    } else if (fullMoveBoard.hasWinner() != opponentMarble) {
                        // If we don't win and the opponent doesn't win either, consider it
                        moves.add(move);
                        // get possibility of win on each branch
                        wins.add(getBranchNrWins(fullMoveBoard, marble, opponentMarble,
                                ahead - 1, emptySpot - 1));
                    }
                }
            }
        }

        if (!wins.isEmpty()) {
            int bestWin = wins.get(0);
            Move bestMove = moves.get(0);
            for (int i = 0; i < wins.size(); i++) {
                int win = wins.get(i);
                if (bestWin < win) {
                    bestMove = moves.get(i);
                    bestWin = win;
                }
            }

            return bestMove;
        } else {
            return randomMove(board);
        }
    }

    /**
     * Calculate ratio of the branch by the number of empty spot.
     *
     * @param calculateTime the number move looking ahead
     * @param emptySpot     the number of empty spot in the field
     * @return list of ratio for each subBranch
     */
    private List<Integer> calculateRatio(int calculateTime, int emptySpot) {
        int num = 1;
        int empty = emptySpot - calculateTime;

        List<Integer> result = new ArrayList<>();
        for (int i = 0; i < calculateTime; i++) {
            empty++;
            result.add(num);
            num = result.get(i) * empty;
        }

        return result;
    }

    /**
     * Get number of wins bases on the ratio on that branch by using recursion.
     *
     * @param board     the board
     * @param ahead     number of move looking ahead
     * @param emptySpot the number of empty spot in the field
     * @return number of win (negative for more losses than wins)
     */
    private int getBranchNrWins(
            Board board, Marble marble, Marble opponentMarble, int ahead, int emptySpot) {
        int wins = 0;

        if (ahead < 1) {
            return 0;
        } else if (ahead % 2 == 1) {
            // Look into our marble case
            for (int i = 0; i < Board.DIM * Board.DIM && board.isEmptyField(i); i++) {
                Board positionBoard = board.deepCopy();
                positionBoard.setField(i, marble);

                for (Quadrant q : Quadrant.values()) {
                    for (Boolean bool : bools) {
                        Board fullMoveBoard = positionBoard.deepCopy();
                        Rotation rotation = new Rotation(q, bool);
                        fullMoveBoard.rotate(rotation);

                        // If this move make AI wins then return this move
                        if (fullMoveBoard.hasWinner() == marble) {
                            wins += ratio.get(startHead - ahead - 1);
                        } else if (fullMoveBoard.hasWinner() == opponentMarble) {
                            wins -= getBranchNrWins(fullMoveBoard, marble, opponentMarble,
                                    ahead - 1, emptySpot - 1);
                        }
                    }
                }
            }
            return wins;
        } else {
            // Look into enemy case
            for (int i = 0; i < Board.DIM * Board.DIM && board.isEmptyField(i); i++) {
                Board positionBoard = board.deepCopy();
                positionBoard.setField(i, marble);

                for (Quadrant q : Quadrant.values()) {
                    for (Boolean bool : bools) {
                        Board fullMoveBoard = positionBoard.deepCopy();
                        Rotation rotation = new Rotation(q, bool);
                        fullMoveBoard.rotate(rotation);

                        // If this move make AI wins then return this move
                        if (fullMoveBoard.hasWinner() == opponentMarble) {
                            wins -= ratio.get(startHead - ahead - 1);
                        } else if (fullMoveBoard.hasWinner() == marble) {
                            wins += getBranchNrWins(fullMoveBoard, marble, opponentMarble,
                                    ahead - 1, emptySpot - 1);
                        }
                    }
                }
            }
            return wins;
        }
    }
}
