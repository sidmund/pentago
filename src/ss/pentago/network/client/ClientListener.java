package ss.pentago.network.client;

import ss.pentago.model.board.Board;
import ss.pentago.model.move.Move;
import ss.pentago.model.player.Player;

import java.util.Map;

/**
 * The listener interface for receiving "interesting" client events,
 * such as a message, a move, etc.
 * <br>
 * The class that is interested in processing a client event implements this interface.
 * <br>
 * The listener object created from that class is then registered with the {@code Client}
 * using the {@code Client}'s {@code addClientListener} method. A client event
 * is generated when the client receives a message from the server. When a client event
 * occurs, the relevant method in the listener object is invoked,
 * and the client event is passed to it.
 */
public interface ClientListener {

    /**
     * Invoked when a message has been received.
     *
     * @param message the message
     */
    //@ requires message != null;
    void messageReceived(String message);

    /**
     * Invoked when an error message has been received.
     *
     * @param error the error message
     */
    //@ requires error != null;
    void errorReceived(String error);

    /**
     * Invoked when a move has been received.
     *
     * @param player the player who made the move,
     *               leave null to only display the move
     * @param move   the move to be processed
     */
    //@ requires move != null;
    void moveReceived(Player player, Move move);

    /**
     * Invoked when a new board state has been received.
     *
     * @param board the board
     */
    //@ requires board != null;
    void boardReceived(Board board);

    /**
     * Invoked when a list of players has been received.
     *
     * @param players the online players
     */
    void listReceived(String[] players);

    /**
     * Invoked when a chat message has been received from a sender.
     *
     * @param sender  the sender of the message
     * @param message the message
     */
    //@ requires sender != null && message != null;
    void chatReceived(String sender, String message);

    /**
     * Invoked when a private chat message has been received from a sender.
     *
     * @param sender  the sender of the message
     * @param message the message
     */
    //@ requires sender != null && message != null;
    void whisperReceived(String sender, String message);

    /**
     * Invoked when the Leaderboard rankings have been requested.
     *
     * @param rankings the list of players on the Leaderboard along with a score stat
     */
    //@ requires rankings != null;
    void rankingsReceived(Map<String, Integer> rankings);

}
