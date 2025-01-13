package ss.pentago.model.player.strategy;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.move.Move;

/**
 * NaiveStrategy is a Strategy that uses randomly generated moves.
 */
public class NaiveStrategy implements Strategy {

    /**
     * @return the name of the strategy
     */
    //@ pure
    @Override
    public String getName() {
        return "Naive";
    }

    /**
     * Determines a random move.
     *
     * @param board  the current game board
     * @param marble the player's marble
     * @return a random move
     */
    /*@
        requires board != null && marble != Marble.EMPTY;
        ensures board.isEmptyField(\result.getPosition());
    */
    //@ pure
    @Override
    public Move determineMove(Board board, Marble marble) {
        return randomMove(board);
    }
}
