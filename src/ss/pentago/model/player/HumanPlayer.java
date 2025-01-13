package ss.pentago.model.player;

import ss.pentago.model.board.Board;
import ss.pentago.model.player.strategy.Strategy;

/**
 * Representation of a human player, a kind of player that has an associated {@code AIPlayer}
 * to provide a maximum number of hints during gameplay.
 * Calling this class's {@link #determineMove(Board)} method will result in
 * an AI generated move. Moves from human player input are handled by an {@code InputHandler}.
 */
public class HumanPlayer extends Player {

    //@ private invariant hintCount >= 0;

    private int hintCount;

    /**
     * Creates a HumanPlayer, with specified hint AI strategy, and amount of hints available.
     *
     * @param name      the player name
     * @param hinter    the hint AI strategy
     * @param hintCount the number of hints allowed
     */
    /*@
        requires name != null;
        ensures getName().equals(name)
                 && this.hintCount == hintCount
                 && this.strategy == hinter;
    */
    public HumanPlayer(String name, Strategy hinter, int hintCount) {
        super(name, hinter);
        this.hintCount = hintCount;
    }

    /**
     * Checks if there are still hints left, and reduces the amount of hints available.
     *
     * @return true if the player has a hint left, false otherwise
     */
    /*@
        ensures \result ==> \old(hintCount) > 0 && hintCount == \old(hintCount) - 1;
        ensures !\result ==> hintCount == 0;
        assignable hintCount;
    */
    public boolean hasHintsLeft() {
        if (hintCount > 0) {
            hintCount--;
            return true;
        } else {
            return false;
        }
    }
}
