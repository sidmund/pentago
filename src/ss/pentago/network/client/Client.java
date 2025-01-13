package ss.pentago.network.client;

import ss.pentago.model.Game;
import ss.pentago.model.board.Board;
import ss.pentago.model.move.Move;
import ss.pentago.model.player.Player;
import ss.pentago.util.Logger;

import java.util.ArrayList;
import java.util.List;

/**
 * The {@code Client} maintains a list of listeners to update whenever something
 * noteworthy happens. It also has an {@code InputHandler} to obtain user input and
 * which tells the {@code Client} what to do.
 */
public abstract class Client implements Runnable {

    /*@
        protected invariant listeners != null;
    */

    /**
     * The Client forwards output (like messages, game states) to its listeners,
     * who could do anything with it.
     */
    protected final List<ClientListener> listeners;

    /**
     * The Client receives commands from the InputHandler, which deals
     * with user input (e.g. through reading from System.in).
     */
    protected InputHandler inputHandler;

    /**
     * The Game that this Client is currently playing,
     * {@code null} if no game is being played right now.
     */
    protected Game currentGame;

    /**
     * Create a new Client. The player parameter is used for the username,
     * and to be able to request hints (in case of a HumanPlayer),
     * or be able to call AI moves (in case of an AIPlayer). <br><br>
     * After creating a new instance of {@code Client},
     * the intended use is to call {@link #addListener(ClientListener)} and
     * {@link #setInputHandler(InputHandler)}.
     */
    //@ ensures listeners != null && listeners.isEmpty();
    protected Client() {
        listeners = new ArrayList<>();
    }

    /**
     * Inform this Client to notify its listeners with the message.
     *
     * @param message the message
     */
    //@ requires message != null;
    public void inform(String message) {
        for (ClientListener listener : listeners) {
            listener.messageReceived(message);
        }
    }

    /**
     * Inform this Client to notify its listeners with the error message.
     *
     * @param error the error message
     */
    //@ requires error != null;
    public void informError(String error) {
        for (ClientListener listener : listeners) {
            listener.errorReceived(error);
        }
    }

    /**
     * Inform this Client to notify its listeners about the board state.
     *
     * @param board the board
     */
    //@ requires board != null;
    public void informBoard(Board board) {
        for (ClientListener listener : listeners) {
            listener.boardReceived(board);
        }
    }

    /**
     * Inform this Client to notify its listeners about a move.
     *
     * @param p the player who made the move,
     *               leave null for only displaying the move
     * @param move   the move
     */
    //@ requires move != null;
    public void informMove(Player p, Move move) {
        for (ClientListener listener : listeners) {
            listener.moveReceived(p, move);
        }
    }

    /**
     * Sets the InputHandler associated with this Client.
     * The InputHandler forwards user input to this Client.
     *
     * @param inputHandler the inputhandler
     */
    //@ requires inputHandler != null;
    //@ ensures this.inputHandler == inputHandler;
    public void setInputHandler(InputHandler inputHandler) {
        this.inputHandler = inputHandler;
    }

    /**
     * Subscribe a new ClientListener to this Client.
     *
     * @param listener the listener to add
     */
    /*@
        requires listener != null;
        ensures \old(listeners.size()) + 1 == listeners.size();
        ensures (\forall int i; i >= 0 && i < \old(listeners.size());
                    \old(listeners.get(i)) == listeners.get(i));
        ensures listeners.get(listeners.size() - 1) == listener;
    */
    public void addListener(ClientListener listener) {
        listeners.add(listener);
    }

    /**
     * Unsubscribe the ClientListener from this Client.
     *
     * @param listener the listener to remove
     */
    /*@
        requires listener != null;
        ensures \old(listeners.size()) - 1 == listeners.size();
        ensures (\forall ClientListener l; !\old(listeners.contains(l));
                    \old(listeners.contains(l)) && listeners.contains(l));
        ensures \old(listeners.contains(listener)) ==> !listeners.contains(listener);
    */
    public void removeListener(ClientListener listener) {
        listeners.remove(listener);
    }

    /**
     * If this Client has a HumanPlayer, this function can be used to return a "hint".
     * If this Client has an AIPlayer, this can be used to return the move the AI would make.
     *
     * @return null when not in a game, the move otherwise
     */
    //@ ensures \result == null <==> getCurrentGame() == null;
    //@ pure
    public abstract Move getMove();

    /**
     * Update the game and inform the listeners of the board change.
     *
     * @param move the move to update the game with
     */
    //@ requires move != null;
    public abstract void updateGame(Move move);

    /**
     * @return the game that is currently being played,
     * null if no game is played right now
     */
    //@ ensures \result == null <==> getMove() == null;
    //@ pure
    public Game getCurrentGame() {
        return currentGame;
    }

    /**
     * Starts this Client in a new thread.
     */
    public void start() {
        Logger.info(this, "starting thread...");
        Thread thread = new Thread(this, "Client");
        thread.start();

        // wait for it to stop
        try {
            thread.join();
            Logger.info(this, "thread is joined: " + !thread.isAlive());
        } catch (InterruptedException e) {
            // restore interrupted status
            thread.interrupt();
            Logger.info(this, "thread interrupted");
        }
    }

    /**
     * Perform a clean up when this Client shuts down.
     * By default this clears the ClientListeners associated with this Client,
     * and sets the game to null.
     */
    //@ ensures getCurrentGame() == null && listeners.isEmpty();
    public void close() {
        currentGame = null;
        listeners.clear();
    }

    /**
     * This should be called after this Client has exited the main run loop.
     * This method will call {@link #close()} and stop the InputHandler thread.
     */
    public void stop() {
        close();
        Logger.info(this, "no longer running");
        inputHandler.stop();
    }
}
