package ss.pentago.model.player.ai;

import ss.pentago.model.player.PlayerFactory;

/**
 * {@code EasyAI} is a type of {@code AIPlayer} that plays randomly,
 * unless it can block an opponents win or win directly itself (in essence looking ahead 1 step).
 */
public class EasyAI extends AIPlayer {

    /**
     * Creates a new {@code EasyAI} player, a player that plays randomly,
     * unless it can directly guarantee it's own win or blocking the win of the opponent.
     */
    public EasyAI() {
        super("Easy AI", PlayerFactory.makeEasyStrategy());
    }

}
