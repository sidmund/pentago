package ss.pentago.test.gameplay;

import ss.pentago.model.Game;
import ss.pentago.model.exception.BoardPositionException;
import ss.pentago.model.player.Player;
import ss.pentago.model.move.Move;

/**
 * AutomatedGame runs through the motions of playing the Game, without any kind of feedback.
 * Just the board is updated for each player turn, eventually resulting in a game over.
 */
public class AutomatedGame extends Game {

    public AutomatedGame(Player s0, Player s1) {
        super(s0, s1);
    }

    /**
     * Game loop without any kind of feedback, just pure playing,
     * which is only useful for testing.
     */
    public void play() {
        while (!isGameOver()) {
            Move move = getCurrentPlayer().determineMove(getBoard());
            try {
                if (update(move)) {
                    return;
                }
            } catch (BoardPositionException e) {
                System.out.println("Invalid move during automated play");
                break;
            }
        }
    }
}
