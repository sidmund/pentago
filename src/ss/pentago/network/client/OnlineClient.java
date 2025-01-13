package ss.pentago.network.client;

import ss.pentago.file.Config;
import ss.pentago.model.Game;
import ss.pentago.model.board.Board;
import ss.pentago.model.exception.BoardPositionException;
import ss.pentago.model.player.Player;
import ss.pentago.model.move.Move;
import ss.pentago.model.player.strategy.Strategy;
import ss.pentago.network.protocol.ClientProtocolHandler;
import ss.pentago.util.Logger;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.Map;

/**
 * The {@code OnlineClient} maintains a list of listeners to update whenever something
 * noteworthy happens. It also has an {@code InputHandler} to obtain user input and
 * tells the {@code OnlineClient} what to do. Furthermore, the {@code OnlineClient} communicates
 * with the server by means of a {@code ProtocolHandler}, this communication may also be forwarded
 * to its listeners.
 */
public class OnlineClient extends Client {

    protected Socket socket;
    protected BufferedReader socketIn;
    protected PrintWriter socketOut;

    protected ClientProtocolHandler protocol;

    protected final Player player;

    // Gameplay variables
    protected boolean isLoggedIn;
    protected boolean isQueued;
    protected boolean isInGame;
    protected boolean isMoveConfirmed;
    protected boolean gotOpponentMove;

    private boolean showGameplay;

    private boolean isRankEnabled = false;
    private boolean isChatEnabled = false;

    /**
     * Create a new Client. The player parameter is used for the username,
     * and to be able to request hints (in case of a HumanPlayer),
     * or be able to call AI moves (in case of an AIPlayer).
     * <br><br>
     * After creating a new instance of {@code OnlineClient},
     * the intended use is to call
     * {@link #addListener(ClientListener)},
     * {@link #setInputHandler(InputHandler)} and
     * {@link #setProtocolHandler(ClientProtocolHandler)}.
     *
     * @param player the player
     */
    //@ ensures this.player == player;
    public OnlineClient(Player player) {
        super();

        this.player = player;
        isLoggedIn = false;
        isQueued = false;
        isInGame = false;
        showGameplay = true;
    }

    /**
     * Establishes a connection to a server with specified address and port.
     *
     * @param address server address
     * @param port    server port, between 0 and 65535 (inclusive)
     * @return true when the connection is established
     */
    //@ requires address != null && port >= 0 && port < 65536;
    //@ ensures \result ==> socket != null && socketIn != null && socketOut != null;
    public boolean connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            socketOut = new PrintWriter(socket.getOutputStream(), true);
            socketIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));

            return true;
        } catch (IOException e) {
            return false;
        }
    }

    /**
     * Sends specified message to the socket output stream.
     * This method should be called by a ClientProtocolHandler
     * after formatting the message accordingly.
     * When a writing error occurs, the socket is closed.
     *
     * @param message the message
     * @return false when a writing error occurred, true otherwise
     */
    //@ requires message != null;
    public boolean send(String message) {
        if (!socket.isClosed()) {
            if (message == null) {
                return false;
            }

            socketOut.println(message);

            if (socketOut.checkError()) {
                close();
                return false;
            } else {
                return true;
            }
        } else {
            Logger.warn(this, "socket closed, can't send message");
            return false;
        }
    }

    /**
     * Continually receive server messages.
     */
    @Override
    public void run() {
        boolean run = true;

        if (inputHandler != null) {
            inputHandler.start();
        }

        while (run) {
            try {
                String msg = socketIn.readLine();

                if (msg == null) {
                    run = false;
                } else {
                    protocol.receive(msg);
                }
            } catch (IOException e) {
                // connection closed
                run = false;
            }
        }

        disconnect();
    }

    /**
     * Disconnect this OnlineClient by calling {@link #close()} to close the Socket,
     * stopping the InputHandler and cleaning up the listeners.
     */
    public void disconnect() {
        close();
        super.stop();
    }

    /**
     * End the game if it's playing, clear the listeners, and close the socket.
     */
    //@ ensures getCurrentGame() == null;
    @Override
    public void close() {
        try {
            if (!socket.isClosed()) {
                Logger.info(this, "socket closed");
                inform("You are disconnected from the server.");

                currentGame = null;
                socket.close();
            }

            super.close();
        } catch (IOException e) {
            Logger.info(this, "blocked I/O thread while socket is closing");
        }
    }

    /**
     * If this Client has a HumanPlayer, this function can be used to return a "hint".
     * If this Client has an AIPlayer, this can be used to return the move the AI would make.
     *
     * @return null when not in a game, the move otherwise
     */
    //@ ensures \result == null <==> getCurrentGame() == null;
    //@ pure
    @Override
    public Move getMove() {
        return currentGame == null ? null : player.determineMove(currentGame.getBoard());
    }

    /**
     * Inform this Client to notify its listeners with a list of online players.
     *
     * @param players the online players
     */
    public void informList(String[] players) {
        for (ClientListener listener : listeners) {
            listener.listReceived(players);
        }
    }

    /**
     * Inform listeners about the board only if {@link #showGameplay} is enabled.
     *
     * @param board the board
     */
    @Override
    public void informBoard(Board board) {
        if (showGameplay) {
            super.informBoard(board);
        }
    }

    /**
     * Inform listeners about the move only if {@link #showGameplay} is enabled.
     *
     * @param p    the player who made the move
     * @param move the move
     */
    @Override
    public void informMove(Player p, Move move) {
        if (showGameplay) {
            super.informMove(p, move);
        }
    }

    /**
     * Inform this Client to notify its listeners with a chat message from a sender.
     *
     * @param sender  the sender of the message
     * @param message the message
     */
    //@ requires sender != null && message != null;
    public void informChat(String sender, String message) {
        for (ClientListener listener : listeners) {
            listener.chatReceived(sender, message);
        }
    }

    /**
     * Inform this Client to notify its listeners with a private chat message from a sender.
     *
     * @param sender  the sender of the message
     * @param message the message
     */
    //@ requires sender != null && message != null;
    public void informWhisper(String sender, String message) {
        for (ClientListener listener : listeners) {
            listener.whisperReceived(sender, message);
        }
    }

    /**
     * Inform this Client to notify its listeners with the server ranking.
     *
     * @param rankings the Leaderboard rankings as a map of usernames and ELO score
     */
    //@ requires rankings != null;
    public void informRankings(Map<String, Integer> rankings) {
        for (ClientListener listener : listeners) {
            listener.rankingsReceived(rankings);
        }
    }

    /**
     * This method should be invoked after the ClientProtocolHandler receives a new game event
     * from the server. This method will then keep a local copy of the game
     * to perform various queries and commands on the game state.<br>
     * What type of Player player1 and player2 are doesn't really matter,
     * since they are just used as containers for player names and marbles,
     * as Game expects Player objects.
     * After all, human/bot input is handled by the InputHandler, not the Player,
     * and the opponent's moves are received from the server.
     *
     * @param player1 the first player
     * @param player2 the second player
     */
    //@ requires player1 != null && player2 != null;
    //@ ensures getCurrentGame() != null;
    public void startGame(Player player1, Player player2) {
        isInGame = true;

        // if we start, pretend the opponent already played,
        // so we know we can send our move
        // if they start, make sure we can't send a move
        // (since the server will kick us then)
        gotOpponentMove = getUsername().equals(player1.getName());
        isMoveConfirmed = true;

        currentGame = new Game(player1, player2);

        inform(String.format("Playing %s vs %s!", player1, player2));

        inform("    Try to be the first to get 5-in-any-row!");
        inform("    Place your marble with 'p', and rotate a board with 'r' " +
                "(type 'help' for more info)");

        informBoard(currentGame.getBoard());


        if (showGameplay) {
            if (player1.getName().equals(getUsername())) {
                inform("You go first!");
            } else {
                inform("Opponent goes first");
            }
        }
    }

    /**
     * End the game by announcing the last board and the game over message.
     * The current game is also set to null.
     *
     * @param message the game over message
     */
    //@ requires message != null;
    //@ ensures getCurrentGame() == null;
    private void endGame(String message) {
        if (showGameplay) {
            informBoard(currentGame.getBoard());
        }
        inform(message);
        currentGame = null;
    }

    /**
     * Ends the game, announcing it was a draw.
     */
    //@ requires getCurrentGame().isDraw();
    public void endGameDraw() {
        endGame("It was a draw!");
    }

    /**
     * Ends the game, announcing the victorious player.
     *
     * @param winner the winning player
     */
    //@ requires winner != null && getCurrentGame().getWinningPlayer().getName().equals(winner);
    public void endGameVictory(String winner) {
        endGame(String.format("%s won!", winner));
    }

    /**
     * Ends the game, announcing the winning player, who won because the other disconnected.
     *
     * @param winner the winning player
     */
    //@ requires winner != null;
    public void endGameDisconnect(String winner) {
        endGame(String.format("%s won! (opponent disconnected)", winner));
    }

    /**
     * Update the game and inform the listeners of the board change.
     * Called when the opponent plays.
     *
     * @param move the move to update the game with
     */
    //@ requires move != null;
    @Override
    public void updateGame(Move move) {
        try {
            boolean isGameOver = currentGame.update(move);
            informBoard(currentGame.getBoard());

            if (isGameOver && showGameplay) {
                inform("Seems to be game over, wait for server to confirm...");
            }
        } catch (BoardPositionException e) {
            // ignore
        }
    }

    /**
     * @return the player's name
     */
    //@ pure
    public String getUsername() {
        return player.getName();
    }

    /**
     * Sets the client's username by updating the associated player's name.
     *
     * @param username the name
     */
    //@ requires username != null;
    //@ ensures player.getName().equals(username);
    public void setUsername(String username) {
        player.setName(username);
    }

    /**
     * Set this Client's player's strategy to a specific AI strategy.
     *
     * @param strategy the AI strategy
     */
    //@ requires strategy != null;
    //@ ensures player.getStrategy() == strategy;
    public void setStrategy(Strategy strategy) {
        player.setStrategy(strategy);
    }

    /**
     * Set this Client's ProtocolHandler to handle server communication.
     *
     * @param ph the ClientProtocolHandler
     */
    //@ requires ph != null;
    //@ ensures getProtocolHandler() == ph;
    public void setProtocolHandler(ClientProtocolHandler ph) {
        this.protocol = ph;
    }

    /**
     * @return the ClientProtocolHandler for this Client
     */
    //@ pure
    public ClientProtocolHandler getProtocolHandler() {
        return protocol;
    }

    /**
     * Set this Client to logged in status.
     */
    //@ ensures isLoggedIn();
    public void login() {
        isLoggedIn = true;
    }

    /**
     * @return whether this client is logged in
     */
    //@ pure
    public boolean isLoggedIn() {
        return isLoggedIn;
    }

    /**
     * Reset the game play status fields for a new match.
     */
    public void resetMatch() {
        isQueued = false;
        isInGame = false;
        isMoveConfirmed = true;
        gotOpponentMove = true;
    }

    public boolean isInGame() {
        return isInGame;
    }

    public void toggleQueue() {
        isQueued = !isQueued;
    }

    public boolean isQueued() {
        return isQueued;
    }

    public boolean hasOpponentMoved() {
        return gotOpponentMove;
    }

    public boolean isMoveConfirmed() {
        return isMoveConfirmed;
    }

    public void setIsMoveConfirmed(boolean confirmed) {
        isMoveConfirmed = confirmed;
    }

    public void setHasOpponentMoved(boolean moved) {
        gotOpponentMove = moved;
    }

    /**
     * Enable or disable showing the board and moves.
     *
     * @param show whether to show gameplay or not
     */
    //@ ensures showGameplay == show;
    public void setShowGameplay(boolean show) {
        showGameplay = show;
    }

    /**
     * @return whether to show gameplay or not
     */
    //@ pure
    public boolean showGameplay() {
        return showGameplay;
    }

    /**
     * Crypt cannot be enabled, because it is not implemented.
     */
    public void enableCrypt() {
        // isCryptEnabled = Config.doesClientSupportCrypt();
    }

    /**
     * Auth cannot be enabled, because it is not implemented.
     */
    public void enableAuth() {
        // isAuthEnabled = Config.doesClientSupportAuth();
    }

    public void enableRank() {
        isRankEnabled = Config.doesClientSupportRank();
    }

    public void enableChat() {
        isChatEnabled = Config.doesClientSupportChat();
    }

    public boolean isChatEnabled() {
        return isChatEnabled;
    }

    public boolean isRankEnabled() {
        return isRankEnabled;
    }

    /**
     * @return String "OnlineClient" + username
     */
    @Override
    public String toString() {
        return "OnlineClient:" + getUsername();
    }

    // just for testing
    public BufferedReader getSocketIn() {
        return socketIn;
    }

    // just for testing
    public PrintWriter getSocketOut() {
        return socketOut;
    }
}
