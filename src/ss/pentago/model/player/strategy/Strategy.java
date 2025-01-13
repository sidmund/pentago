package ss.pentago.model.player.strategy;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;
import ss.pentago.util.Randomizer;

/**
 * Strategy describes a gameplay Strategy.
 * Different kinds of strategies are meant
 * to implement the {@link #determineMove(Board, Marble)} method.
 */
public interface Strategy {

    /**
     * @return the name of the strategy
     */
    //@ pure
    String getName();

    /**
     * Determines a move according to a strategy.
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
    Move determineMove(Board board, Marble marble);

    /**
     * Default implementation of determining a move, is to return a random move.
     *
     * @param board the current game board
     * @return a random move
     */
    /*@
        requires board != null;
        ensures (\exists int i; i >= 0 && i < Quadrant.values().length;
            \result.getRotation().getQuadrant() == Quadrant.values()[i]);
        ensures board.isEmptyField(\result.getPosition());
    */
    //@ pure
    default Move randomMove(Board board) {
        int index;
        do {
            index = Randomizer.randomInt(Board.DIM * Board.DIM);
        } while (!board.isEmptyField(index));

        return new Move(index,
                new Rotation(
                        Quadrant.values()[Randomizer.randomInt(Quadrant.values().length)],
                        Randomizer.randomBoolean()
                ));
    }
}
