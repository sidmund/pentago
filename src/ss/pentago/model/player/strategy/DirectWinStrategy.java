package ss.pentago.model.player.strategy;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;

/**
 * {@code DirectWinStrategy} is a type of {@code Strategy} that plays randomly,
 * unless it can block an opponents win or win directly itself (in essence looking ahead 1 step).
 */
public class DirectWinStrategy implements Strategy {

    /**
     * @return the name of the strategy
     */
    //@ pure
    @Override
    public String getName() {
        return "Direct Win";
    }

    /**
     * Find Move that will either win AI the game or block enemy (try it best) from winning
     * If there is no such move exist then it plays random move.
     *
     * @param board  the current game board
     * @param marble the player's marble
     * @return a move that will win directly or directly block the opponent's win,
     * a random move otherwise
     */
    /*@
        requires board != null && marble != Marble.EMPTY;
        ensures (\exists int i; i >= 0 && i < Quadrant.values().length;
            \result.getRotation().getQuadrant() == Quadrant.values()[i]);
        ensures board.isEmptyField(\result.getPosition());
        ensures \result == findWinningMove(board, marble)
                        && findWinningMove(board, marble)
                        != null
             || \result == findMoveThatBlocksOpponentWin(board, Marble.getOppositeOf(marble))
                        && findMoveThatBlocksOpponentWin(board, Marble.getOppositeOf(marble))
                        != null
             || \result == randomMove(board);
    */
    //@ pure
    @Override
    public Move determineMove(Board board, Marble marble) {
        Move myBest = findWinningMove(board, marble);
        Move blockMove = findMoveThatBlocksOpponentWin(
                board, Marble.getOppositeOf(marble));

        if (myBest != null) {
            return myBest;
        } else if (blockMove != null) {
            return blockMove;
        } else {
            return randomMove(board);
        }
    }

    /**
     * Find move which will stop opponent from winning by next move.
     *
     * @param board          the board
     * @param opponentMarble the opponent's marble
     * @return the move that will stop enemy winning by next move
     */
    //@ requires board != null && opponentMarble != Marble.EMPTY;
    //@ pure
    private Move findMoveThatBlocksOpponentWin(Board board, Marble opponentMarble) {
        Board test = board.deepCopy();

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (test.isEmptyField(i)) {
                test.setField(i, opponentMarble);
                Rotation rotation = findWinningRotation(test, opponentMarble);

                if (rotation != null) {
                    rotation = new Rotation(rotation.getQuadrant(), !rotation.getClockwise());
                    return new Move(i, rotation);
                } else {
                    test.setField(i, Marble.EMPTY);
                }
            }
        }

        return null;
    }

    /**
     * Find move will make AI win by next move.
     *
     * @param board  the board
     * @param marble the player's marble
     * @return the move
     */
    //@ requires board != null && marble != Marble.EMPTY;
    //@ pure
    private Move findWinningMove(Board board, Marble marble) {
        Board test = board.deepCopy();

        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (test.isEmptyField(i)) {
                test.setField(i, marble);
                Rotation rotation = findWinningRotation(test, marble);
                if (rotation != null) {
                    return new Move(i, rotation);
                } else {
                    test.setField(i, Marble.EMPTY);
                }
            }
        }

        return null;
    }

    /**
     * Find rotation that will make checkMarble win by next move.
     *
     * @param board       the board
     * @param checkMarble checking Marble
     * @return the rotation
     */
    //@ requires board != null && checkMarble != Marble.EMPTY;
    //@ pure
    private Rotation findWinningRotation(Board board, Marble checkMarble) {
        // try to rotate board on every quadrant
        for (int j = 0; j < Quadrant.values().length; j++) {
            Quadrant quadrant = Quadrant.values()[j];

            // try to rotate board clockwise at that quadrant
            board.rotate(quadrant, true);
            if (board.hasWinner() == checkMarble) {
                return new Rotation(quadrant, true);
            }

            // fix the board to original state
            board.rotate(quadrant, false);
            board.rotate(quadrant, false);
            if (board.hasWinner() == checkMarble) {
                return new Rotation(quadrant, false);
            }

            // fix the board
            board.rotate(quadrant, true);
        }

        return null;
    }
}
