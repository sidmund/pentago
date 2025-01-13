package ss.pentago.model.player.ai;

import ss.pentago.model.player.Player;
import ss.pentago.model.player.strategy.Strategy;

/**
 * Player class for an AI player.
 */
public class AIPlayer extends Player {

    /**
     * Creates an AIPlayer.
     *
     * @param name     the player name
     * @param strategy the strategy to use
     */
    //@ requires name != null && strategy != null;
    //@ ensures getName() == name && getStrategy() != null;
    public AIPlayer(String name, Strategy strategy) {
        super(name, strategy);
    }

}
