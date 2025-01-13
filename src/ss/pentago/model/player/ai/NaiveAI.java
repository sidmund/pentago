package ss.pentago.model.player.ai;

import ss.pentago.model.player.PlayerFactory;

/**
 * A Naive implementation of an AIPlayer, i.e. random move generation.
 * AIPlayer defaults to random moves, so this class does not override any methods.
 */
public class NaiveAI extends AIPlayer {

    /**
     * Creates an AI player using a naive strategy, i.e. selecting random valid moves.
     */
    public NaiveAI() {
        super("NaiveAI", PlayerFactory.makeNaiveStrategy());
    }

}
