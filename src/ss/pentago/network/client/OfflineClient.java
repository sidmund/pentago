package ss.pentago.network.client;

import ss.pentago.file.Config;
import ss.pentago.model.Game;
import ss.pentago.model.exception.BoardPositionException;
import ss.pentago.model.player.HumanPlayer;
import ss.pentago.model.player.Player;
import ss.pentago.model.player.ai.AIPlayer;
import ss.pentago.model.move.Move;
import ss.pentago.util.Logger;

/**
 * An offline client to play the game.
 */
public class OfflineClient extends Client {

    /**
     * After creating a new instance of {@code OfflineClient},
     * the intended use is to call {@link #addListener(ClientListener)} and
     * {@link #setInputHandler(InputHandler)}.
     *
     * @param player1      the first player
     * @param player2      the second player
     * @param shuffleOrder whether to randomly shuffle the starting player
     */
    /*@
        ensures getCurrentGame() != null;
        ensures getCurrentGame().getFirstPlayer() == player1
                || getCurrentGame().getFirstPlayer() == player2;
        ensures getCurrentGame().getSecondPlayer() == player1
                || getCurrentGame().getSecondPlayer() == player2;
    */
    public OfflineClient(Player player1, Player player2, boolean shuffleOrder) {
        super();

        currentGame = new Game(player1, player2);
        if (shuffleOrder) {
            currentGame.shuffle();
        }
    }

    /**
     * Return the move the current player would make, for an AIPlayer it's their move,
     * for a HumanPlayer, this method returns the move their hint AI would play.
     *
     * @return null when not in a game or a HumanPlayer has no hints left, the move otherwise
     */
    /*@
        ensures \result == null <==> getCurrentGame() == null;
        ensures getCurrentGame().getCurrentPlayer() instanceof AIPlayer ==> \result != null;
        ensures getCurrentGame().getCurrentPlayer() instanceof HumanPlayer
                    && ((HumanPlayer) getCurrentGame().getCurrentPlayer()).hasHintsLeft()
                    ==> \result != null;
    */
    // CheckStyle complains about this JML, but there is no way around it.
    //@ pure
    @Override
    public synchronized Move getMove() {
        Move move = null;

        if (currentGame != null) {
            Player currentPlayer = currentGame.getCurrentPlayer();
            if (currentPlayer instanceof HumanPlayer) {
                if (((HumanPlayer) currentPlayer).hasHintsLeft()) {
                    move = currentPlayer.determineMove(currentGame.getBoard());
                } else {
                    inform("You have no hints left!");
                }
            } else {
                move = currentPlayer.determineMove(currentGame.getBoard());
            }
        }

        return move;
    }

    /**
     * Update the game and inform the listeners of the board change.
     * This method is synchronized for the OfflineClient, since the thread
     * running the OfflineTextInputHandler also access this method,
     * while trying to modify the game.
     *
     * @param move the move to update the game with
     */
    //@ requires move != null;
    @Override
    public synchronized void updateGame(Move move) {
        try {
            currentGame.update(move);
            informBoard(currentGame.getBoard());
        } catch (BoardPositionException e) {
            // ignore
        }
    }

    /**
     * Delay this thread for an amount specified by
     * <code>Config.getResponseDelaySinglePlayer</code>.
     * This method should be called before an AI performs a move.
     */
    public void delayAI() {
        try {
            Thread.sleep(Config.getResponseDelaySinglePlayer());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            // ignore
        }
    }

    /**
     * Announce the game over event.
     */
    //@ pure
    private void announceGameOver() {
        if (currentGame != null && currentGame.isGameOver()) {
            inform("Winning board:");
            informBoard(currentGame.getBoard());

            if (currentGame.isDraw()) {
                inform("Draw. There is no winner!");
            } else {
                inform("Player " + currentGame.getWinningPlayer() + " has won!");
            }
        } else {
            inform("No game over, game ended prematurely!");
        }
    }

    /**
     * Starts the pentago game main loop. <br>
     * First the (still empty) board is shown. Then the game is played
     * until it is over. Players can make a move when it's their turn.
     * In every change in board (including placing marble and rotating the board)
     * , the changed game situation is printed.
     */
    @Override
    public void run() {
        if (inputHandler != null) {
            inputHandler.start();
        }

        informBoard(currentGame.getBoard());
        inform(String.format("1. %s vs 2. %s!",
                currentGame.getFirstPlayer(), currentGame.getSecondPlayer()));

        inform("    Try to be the first to get 5-in-any-row!");
        inform("    Place your marble with 'p', and rotate a board with 'r' " +
                "(type 'help' for more info)");

        inform(String.format("%s, it's your turn!",
                getCurrentGame().getFirstPlayer()));

        /*
         * This loop is only here to keep the game running, HumanPlayer input
         * is handled by an InputHandler, and if there is an AI, it is updated
         * in this loop. If both players are AI, then this loop just runs the game between them.
         * Note that if two HumanPlayers are playing a single player game, essentially the
         * InputHandler handles both their turns, as if one player is inputting moves
         * for both players.
         */
        while (getCurrentGame() != null && !getCurrentGame().isGameOver()) {
            try {
                if (getCurrentGame().getCurrentPlayer() instanceof AIPlayer) {
                    Move move = getMove();

                    delayAI();
                    informMove(getCurrentGame().getCurrentPlayer(), move);
                    getCurrentGame().update(move.getPosition());
                    informBoard(getCurrentGame().getBoard());

                    delayAI();
                    // this call to update also updates the current player
                    getCurrentGame().update(move.getRotation());
                    informBoard(getCurrentGame().getBoard());

                    inform(String.format("%s, it's your turn!",
                            getCurrentGame().getCurrentPlayer()));
                }
            } catch (BoardPositionException e) {
                // ignore, determineMove is guaranteed to return a valid move
            } catch (NullPointerException e) {
                // sometimes when quitting there is a null pointer,
                // this will ensure it terminates cleanly
                Logger.error(this, "null pointer");
                break;
            }
        }

        announceGameOver();

        stop();
    }

    /**
     * Perform a clean up when this Client shuts down.
     * By default this clears the ClientListeners associated with this Client,
     * and sets the game to null.
     * This method is synchronized for the OfflineClient, since the thread
     * running the OfflineTextInputHandler also access this method,
     * while trying to modify the game.<br>
     * This method is overridden to provide clearer documentation specific to this class,
     * but the functionality is exactly the same as Client's close method.
     */
    @Override
    public synchronized void close() {
        super.close();
    }

    /**
     * @return the game that is currently being played,
     * null if no game is played right now
     */
    //@ ensures \result == null <==> getMove() == null;
    //@ pure
    @Override
    public synchronized Game getCurrentGame() {
        return currentGame;
    }

    /**
     * @return String "OfflineClient"
     */
    @Override
    public String toString() {
        return "OfflineClient";
    }
}
