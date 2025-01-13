package ss.pentago.model.player.ai;

import ss.pentago.model.player.PlayerFactory;

/**
 * HardAI is a type of AI that uses min-maxing with smarter heuristics.
 */
public class HardAI extends AIPlayer {

    /**
     * Creates an AIPlayer.
     */
    public HardAI() {
        super("Hard AI", PlayerFactory.makeHardStrategy());
    }

}
