package ss.pentago.model.player;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.move.Move;
import ss.pentago.model.player.strategy.Strategy;

/**
 * Player class to store name and {@code Marble} attributes.
 * It also provides a default function for determining moves.
 */
public abstract class Player {

    /*@
        protected invariant name != null
                         && marble != Marble.EMPTY
                         && strategy != null;
    */

    protected String name;
    protected Marble marble;

    protected Strategy strategy;

    /**
     * Create a Player. The Marble is meant to be set up when actually starting a game.
     *
     * @param name the player name
     * @param strategy the strategy to use for AI play or to use for hints
     */
    //@ requires name != null && strategy != null;
    //@ ensures getName() == name && getStrategy() != null;
    protected Player(String name, Strategy strategy) {
        this.name = name;
        this.strategy = strategy;
    }

    /**
     * Determines a full move on the board according to a strategy.
     *
     * @param board  the current game board
     * @return the move
     */
    /*@
        requires board != null && marble != Marble.EMPTY;
        ensures board.isField(\result.getPosition())
             && board.getField(\result.getPosition()) == Marble.EMPTY
             && \result.getRotation().getQuadrant() != null;
    */
    //@ pure
    public Move determineMove(Board board) {
        return strategy.determineMove(board, marble);
    }

    /**
     * @return this player's name
     */
    //@ pure
    public String getName() {
        return name;
    }

    /**
     * Set the player name.
     *
     * @param name the new name
     */
    //@ requires name != null;
    //@ ensures this.name.equals(name);
    public void setName(String name) {
        this.name = name;
    }

    /**
     * Sets this player's marble.
     *
     * @param marble the marble to play with
     */
    public void setMarble(Marble marble) {
        this.marble = marble;
    }

    /**
     * @return this player's marble
     */
    //@ pure
    public Marble getMarble() {
        return marble;
    }

    /**
     * @return the strategy this AI is using
     */
    //@ pure
    public Strategy getStrategy() {
        return strategy;
    }

    /**
     * Set the strategy this AI uses.
     *
     * @param strategy the new strategy
     */
    //@ requires strategy != null;
    //@ ensures getStrategy() == strategy;
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    /**
     * Represents the player by name and marble.
     *
     * @return a string to represent the player by their name and marble type
     */
    //@ pure
    @Override
    public String toString() {
        return String.format("%s (%s)", getName(), getMarble());
    }
}
