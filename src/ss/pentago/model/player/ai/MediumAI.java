package ss.pentago.model.player.ai;

import ss.pentago.model.player.PlayerFactory;

/**
 * {@code MediumAI} is a type of {@code AIPlayer} that determines its strategy
 * using a min-max algorithm. By default it looks 3 moves ahead.
 */
public class MediumAI extends AIPlayer {

    /**
     * Creates a new {@code MediumAI} player, a player that uses a min-max strategy.
     */
    public MediumAI() {
        super("Medium AI", PlayerFactory.makeMediumStrategy());
    }

}
