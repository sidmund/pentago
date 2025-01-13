package ss.pentago.network.server;

import ss.pentago.file.Config;
import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.exception.RotationFormatException;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;
import ss.pentago.util.Logger;

import java.util.*;

/**
 * GameManager continually matches the first two players that enter the game queue.
 * Furthermore, it keeps track of current matches being played and provides methods
 * for updating current games. This class also takes care of sending the appropriate
 * commands to both players before, during, and after a match.
 */
public class GameManager implements Runnable {

    private final Server server;

    /**
     * Queue object to add new users to the end and remove them from the front.
     */
    private final List<ClientHandler> queue;

    /**
     * Map object holding as keys the two players in a match,
     * and as values the boards belonging to those matches.
     */
    private final Map<List<ClientHandler>, Board> currentMatches;
    private int matchCounter;

    private boolean running;

    /**
     * Create a new GameManager object. The GameManager matches queued players and keeps
     * track of their matches.
     *
     * @param server the server
     */
    //@ ensures this.server == server && queue != null && currentMatches != null;
    public GameManager(Server server) {
        this.server = server;

        queue = new ArrayList<>();
        currentMatches = new HashMap<>();
    }

    /**
     * While running, continually tries to match the two front most players in the queue.
     * This happens on a configurable interval.
     */
    @Override
    public void run() {
        Logger.info(this, "starting...");
        running = true;

        long startTime = System.currentTimeMillis();

        while (running) {

            long elapsed = System.currentTimeMillis() - startTime;
            if (elapsed > Config.getGameManagerTickRate()) {

                // every 'tick' try to match the front most players in the queue
                if (queue.size() >= 2) {
                    addNewMatch(queue.remove(0), queue.remove(0));
                }

                startTime = System.currentTimeMillis();
            }
        }
    }

    /**
     * Stop the GameManager. This will ensure this GameManager thread will terminate.
     */
    //@ ensures !running;
    public void stop() {
        running = false;
    }

    /**
     * Queue the user if they are not in the game queue.
     * Dequeue them if they are in the queue.
     *
     * @param user the user to (de)queue
     * @return true when the user was queued, false when they were dequeued
     */
    //@ requires user != null;
    //@ ensures \result ==> !\old(queue).contains(user) && queue.contains(user);
    //@ ensures !\result ==> \old(queue).contains(user) && !queue.contains(user);
    public synchronized boolean queue(ClientHandler user) {
        if (queue.contains(user)) {
            queue.remove(user);
            return false;

        } else {
            queue.add(user);
            return true;
        }
    }

    /**
     * Start a match between two users. This removes them from the queue,
     * and sets up the new game.
     *
     * @param player1 the first player
     * @param player2 the second player
     */
    /*@
        requires player1 != null && player2 != null;
        ensures !queue.contains(player1) && !queue.contains(player2)
              && player1.isInGame() && player2.isInGame() && player1.canMove() && !player2.canMove()
              && getEntryByPlayer(player1) != null && getEntryByPlayer(player2) != null;
    */
    public synchronized void addNewMatch(ClientHandler player1, ClientHandler player2) {
        // update both user's status
        player1.setInGame(true);
        player2.setInGame(true);
        player1.setCanMove(true);
        player2.setCanMove(false);

        // add both users to the currently playing matches
        List<ClientHandler> users = new ArrayList<>();
        users.add(player1);
        users.add(player2);
        currentMatches.put(users, new Board());

        // send both users the new game command
        player1.getProtocolHandler().sendNewGame(player1.getUsername(), player2.getUsername());
        player2.getProtocolHandler().sendNewGame(player1.getUsername(), player2.getUsername());
    }

    /**
     * Check whether there is a game over. It returns one of the following states:<br>
     * -1, no winner (still ongoing)<br>
     * 0, the first player won<br>
     * 1, the second player won<br>
     * 2, it was a draw<br>
     *
     * @param board the board
     * @return the match condition as described above
     */
    /*@
        requires board != null;
        ensures \result == -1 && !board.isGameOver()
             || \result == 0  && board.hasWinner() == Marble.BLACK
             || \result == 1  && board.hasWinner() == Marble.WHITE
             || \result == 2  && board.isDraw();
    */
    //@ pure
    private synchronized int checkMatchCondition(Board board) {
        if (!board.isGameOver()) {
            return -1;
        }

        if (board.isDraw()) {
            return 2;
        } else if (board.hasWinner() == Marble.BLACK) {
            return 0;
        } else {
            return 1;
        }
    }

    /**
     * Get a match entry by player.
     *
     * @param player the player to find
     * @return the entry mapping the players in the match and the board,<br>
     * null if there is no match for that player
     */
    /*@
        requires player != null;
        ensures \result.getKey().get(0) == player
             || \result.getKey().get(1) == player
             || \result == null;
    */
    //@ pure
    private Map.Entry<List<ClientHandler>, Board> getEntryByPlayer(ClientHandler player) {
        for (Map.Entry<List<ClientHandler>, Board> entry : currentMatches.entrySet()) {
            if (entry.getKey().get(0) == player || entry.getKey().get(1) == player) {
                return entry;
            }
        }

        return null;
    }

    /**
     * Validate the move received by the Server.
     *
     * @param board    the board to use for checking the position
     * @param position the position index
     * @param rotation the rotation index
     * @return if valid, the move as a {@code Move} object, null otherwise
     */
    //@ requires board != null;
    //@ ensures position >= 0 && position < 36 && rotation >= 0 && rotation < 8 ==> \result != null;
    private Move validateMove(Board board, int position, int rotation) {
        Rotation rot;
        try {
            rot = Rotation.parseRotation(rotation);
        } catch (RotationFormatException e) {
            return null;
        }

        if (!board.isField(position) || !board.isEmptyField(position)) {
            return null;
        }

        return new Move(position, rot);
    }

    /**
     * Update the board of the match the specified player is playing in.
     *
     * @param player   the player
     * @param position the position index
     * @param rotation the rotation index
     * @return false when the move was invalid or no match was found, true otherwise
     */
    //@ requires player != null;
    public synchronized boolean updateMatchOf(ClientHandler player, int position, int rotation) {
        if (!player.isInGame()) {
            player.getProtocolHandler().sendError("This player is not found in current match");
            return true;

        } else if (!player.canMove()) {
            player.getProtocolHandler().sendError("It's not this player's turn");
            return true;

        }

        Map.Entry<List<ClientHandler>, Board> entry = getEntryByPlayer(player);
        if (entry == null) {
            player.getProtocolHandler().sendError("Player should be in a match, but isn't");
            return false;
        }

        Board matchBoard = entry.getValue();
        List<ClientHandler> players = entry.getKey();

        // validate the move
        Move move = validateMove(matchBoard, position, rotation);
        if (move == null) {
            player.getProtocolHandler().sendError("Move is invalid");
            return false;
        }

        // update whose turn it is, update the game board, and send the move to both players
        int current = players.get(0) == player ? 0 : 1;
        Marble marble = current == 0 ? Marble.BLACK : Marble.WHITE;

        players.get(current).setCanMove(false);
        players.get((current + 1) % 2).setCanMove(true);

        matchBoard.perform(move, marble);

        players.get(0).getProtocolHandler().sendMove(position, rotation);
        players.get(1).getProtocolHandler().sendMove(position, rotation);

        // check game over
        int matchCondition = checkMatchCondition(matchBoard);
        ClientHandler p1;
        ClientHandler p2;

        if (matchCondition == 0 || matchCondition == 1) {
            // there is a game over with a single winner
            p1 = players.get(matchCondition);
            p2 = players.get((matchCondition + 1) % 2);
            server.updateMatch(p1.getUsername(), p2.getUsername(), false);
            p1.getProtocolHandler().sendGameOverWinner(
                    players.get(matchCondition).getUsername());
            p2.getProtocolHandler().sendGameOverWinner(
                    players.get(matchCondition).getUsername());

        } else if (matchCondition == 2) {
            // there is a draw
            p1 = players.get(0);
            p2 = players.get(1);
            server.updateMatch(p1.getUsername(), p2.getUsername(), true);
            p1.getProtocolHandler().sendGameOverDraw();
            p2.getProtocolHandler().sendGameOverDraw();
        }

        if (matchCondition >= 0) {
            resetStatus(players);
        }

        return true;
    }

    /**
     * Checks if the user who disconnected was in a match,
     * if so, that match is removed, and both players
     * receive a game over due to disconnection message.
     * Furthermore, this will reset the still connected player's game status.
     * This will also increment the match counter. Does not require that player is
     * actually in game or not. It will double check again.
     *
     * @param disconnectedUser the user that disconnected during the match
     */
    //@ requires disconnectedUser != null;
    public synchronized void endMatchIfPresent(ClientHandler disconnectedUser) {
        Map.Entry<List<ClientHandler>, Board> entry = getEntryByPlayer(disconnectedUser);
        if (entry == null) {
            return;
        }

        List<ClientHandler> players = entry.getKey();
        ClientHandler p1 = players.get(0);
        ClientHandler p2 = players.get(1);
        resetStatus(players);


        // Send disconnect and updated match result
        if (disconnectedUser == p1) {
            p1.getProtocolHandler().sendGameOverDisconnect(disconnectedUser.getUsername(), true);
            p2.getProtocolHandler().sendGameOverDisconnect(disconnectedUser.getUsername(), false);
            server.updateMatch(p1.getUsername(), p2.getUsername(), false);
        } else {
            p1.getProtocolHandler().sendGameOverDisconnect(disconnectedUser.getUsername(), false);
            p2.getProtocolHandler().sendGameOverDisconnect(disconnectedUser.getUsername(), true);
            server.updateMatch(p2.getUsername(), p1.getUsername(), false);
        }
    }

    /**
     * Reset both players' game status and removes them from the current matches Map.
     * The match counter is incremented.
     *
     * @param players players who finish the game
     */
    //@ requires players != null;
    private synchronized void resetStatus(List<ClientHandler> players) {
        players.get(0).reset();
        players.get(1).reset();

        currentMatches.remove(players);
        matchCounter++;
    }

    /**
     * Retrieve the number of matches player on the Server, a match is counted when either
     * it resulted in a victory, a draw, or a disconnect.
     *
     * @return the number of matches played
     */
    //@ ensures \result >= 0;
    public int getNrMatchesPlayed() {
        return matchCounter;
    }

    @Override
    public String toString() {
        return "GameManager";
    }

    // for test
    public Map<List<ClientHandler>, Board> getCurrentMatches() {
        return currentMatches;
    }
    // for test
    public List<ClientHandler> getQueue() {
        return queue;
    }
}
