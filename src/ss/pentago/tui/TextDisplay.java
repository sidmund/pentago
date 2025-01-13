package ss.pentago.tui;

import ss.pentago.file.Config;
import ss.pentago.model.board.Board;
import ss.pentago.model.exception.ChessNotationFormatException;
import ss.pentago.model.move.Move;
import ss.pentago.model.player.Player;
import ss.pentago.network.client.ClientListener;
import ss.pentago.util.ChessNotation;

import java.io.PrintStream;
import java.util.Map;

/**
 * TextDisplay displays events from the Client on System.out.
 */
public class TextDisplay implements ClientListener {

    /*@
        private invariant display == System.out;
     */

    private final PrintStream display;

    /**
     * Creates a new TextDisplay configured to print to System.out.
     */
    //@ ensures display == System.out;
    public TextDisplay() {
        display = System.out;
    }

    /**
     * Simply print the message.
     *
     * @param message the message
     */
    //@ requires message != null;
    @Override
    public void messageReceived(String message) {
        display.println(message);
    }

    /**
     * Print the error to System.out.
     *
     * @param error the error message
     */
    //@ requires error != null;
    @Override
    public void errorReceived(String error) {
        display.printf("Error: %s%n", error);
    }

    /**
     * Display a move to System.out in a human readable format.
     *
     * @param player the player who made the move,
     *               leave null to only display the move
     * @param move   the move to be processed
     */
    //@ requires move != null;
    @Override
    public void moveReceived(Player player, Move move) {
        try {
            String hintDirection = move.getRotation().getClockwise()
                    ? "clockwise" : "counterclockwise";
            String notated = ChessNotation.parseIndex(move.getPosition());
            String moveString = String.format("%s %s %s%n",
                    notated, move.getRotation().getQuadrant(), hintDirection);

            if (player == null) {
                display.printf("Move: %s%n", moveString);
            } else {
                display.printf("%s's move (%s): %s%n",
                        player.getName(), player.getMarble(), moveString);
            }
        } catch (ChessNotationFormatException e) {
            // ignore
        }
    }

    /**
     * Print the board to System.out using the current {@code BoardSkin}.
     *
     * @param board the board
     */
    //@ requires board != null;
    @Override
    public void boardReceived(Board board) {
        display.printf("%n%s%n%n", Config.BOARD_SKIN.render(board, 3));
    }

    /**
     * Invoked when a list of players has been received.
     *
     * @param players the online players
     */
    public void listReceived(String[] players) {
        StringBuilder online = new StringBuilder();
        online.append("Online players: ");

        if (players == null || players.length == 0) {
            online.append("none");
        } else {
            for (int i = 0; i < players.length; i++) {
                online.append(players[i]);
                if (i < players.length - 1) {
                    online.append(", ");
                }
            }
        }

        display.println(online);
    }

    /**
     * Simply print the chat message from the sender.
     *
     * @param sender  the sender of the message
     * @param message the message
     */
    //@ requires sender != null && message != null;
    @Override
    public void chatReceived(String sender, String message) {
        display.printf("%s[GLOBAL CHAT] %s : %s%s%n",
                Colors.CYAN, sender, message, Colors.RESET);
    }

    /**
     * Simply print the private chat message from the sender.
     *
     * @param sender  the sender of the message
     * @param message the message
     */
    //@ requires sender != null && message != null;
    @Override
    public void whisperReceived(String sender, String message) {
        display.printf("%s[DIRECT MESSAGE] %s : %s%s%n",
                Colors.BLUE, sender, message, Colors.RESET);
    }

    /**
     * Print the top 20 Leaderboard rankings to the screen, as a nicely formatted table.
     *
     * @param rankings the list of players on the Leaderboard by their ELO stat
     */
    //@ requires rankings != null;
    @Override
    public void rankingsReceived(Map<String, Integer> rankings) {
        StringBuilder sb = new StringBuilder();

        sb.append(String.format("%n| %-30s | %-15s |%n", "username", "ELO score"));
        sb.append(String.format("| %s | %s |%n", "-".repeat(30), "-".repeat(15)));

        int nrPlayers = 20;
        for (Map.Entry<String, Integer> entry : rankings.entrySet()) {
            sb.append(String.format("| %s%-30s%s | %s%-15d%s |%n",
                    Colors.YELLOW, entry.getKey(), Colors.RESET,
                    Colors.YELLOW, entry.getValue(), Colors.RESET));

            nrPlayers--;
            if (nrPlayers <= 0) {
                break;
            }
        }

        display.println(sb);
    }
}
