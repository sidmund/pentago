package ss.pentago.tui;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.exception.BoardPositionException;
import ss.pentago.model.exception.ChessNotationFormatException;
import ss.pentago.model.exception.QuadrantFormatException;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;
import ss.pentago.network.client.Client;
import ss.pentago.network.client.InputHandler;
import ss.pentago.network.client.OfflineClient;
import ss.pentago.util.ChessNotation;
import ss.pentago.util.Logger;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * TextInputHandler handles player input through the command line (System.in).
 * It tells the Client what to do with this input.
 * Note that this type of InputHandler does not have connectivity and
 * therefore does not use a Protocol.
 */
public class OfflineTextInputHandler extends InputHandler {

    /*@
        protected invariant inputReader != null;
        protected invariant position >= -1 && position < Board.DIM * Board.DIM;
     */

    protected static final String INVALID_COMMAND_USAGE_HELP_MESSAGE
            = "Invalid command usage, see 'help'";

    protected final BufferedReader inputReader;

    /**
     * Since the move is split in position and rotation,
     * this value keeps track of whether the position has been set
     * (-1 when it hasn't been set),
     * so the full move can be sent after the rotation has been specified.
     */
    protected int position;

    /**
     * Creates a new {@code OfflineTextInputHandler} object.
     *
     * @param client the client to send input to
     */
    /*@
        requires client != null;
        ensures this.client == client && inputReader != null && position == -1;
    */
    public OfflineTextInputHandler(Client client) {
        super(client);

        inputReader = new BufferedReader(new InputStreamReader(System.in));
        position = -1;
    }

    /**
     * Try to parse the position as supplied in {@code arg},
     * and set {@link #position} to {@code arg} parsed to int if it is valid.
     * This way the position is remembered, when we send the full move later,
     * after rotating.
     *
     * @param arg          the position information
     * @param checkQuietly whether to suppress error messages
     * @return true when position was updated (it was a valid move)
     */
    //@ requires arg != null;
    //@ ensures \result ==> position != -1;
    protected boolean parsePosition(String arg, boolean checkQuietly) {
        try {
            int index = ChessNotation.parseString(arg);

            // Make a copy just to display the intermediate position,
            // only update the client's board once the full move has been made
            Board copy = client.getCurrentGame().getBoard().deepCopy();
            if (copy.isEmptyField(index)) {
                copy.setField(index, client.getCurrentGame().getCurrentPlayer().getMarble());
                client.informBoard(copy);
                client.inform("Please specify rotation");
                position = index;
                return true;
            } else {
                if (!checkQuietly) {
                    client.informError("That field was not empty");
                }
                return false;
            }
        } catch (ChessNotationFormatException e) {
            if (!checkQuietly) {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
            }
            return false;
        }
    }

    /**
     * Try to parse the rotation and return the full move.
     *
     * @param args         the arguments containing the rotation information
     * @param checkQuietly whether to suppress error messages
     * @return true if it is a valid move, false otherwise
     */
    //@ requires position != -1 && args != null;
    //@ ensures client.getCurrentGame() == null || position == -1 ==> \result == null;
    protected Move parseMove(String[] args, boolean checkQuietly) {
        if (client.getCurrentGame() == null) {
            if (!checkQuietly) {
                client.informError("You're not currently in a game");
            }
            return null;
        } else if (position == -1) {
            if (!checkQuietly) {
                client.informError("Please place a stone first");
            }
            return null;
        }

        // offset to compensate for a 'rotate' command without the prefix
        int offset = args[0].equals("r") || args[0].equals("rot") || args[0].equals("rotate")
                ? 0 : 1;

        if (args.length != 3 - offset
                || !args[2 - offset].equals("c") && !args[2 - offset].equals("cc")) {
            if (!checkQuietly) {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
            }
            return null;
        }

        // try to parse
        try {
            return new Move(position, new Rotation(Quadrant.parseQuadrant(args[1 - offset]),
                    args[2 - offset].equals("c")));
        } catch (QuadrantFormatException e) {
            if (!checkQuietly) {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
            }
            return null;
        }
    }

    /**
     * Parses the supplied command, and tells the Client what to do.
     *
     * @param command the command
     * @return false if the client needs to be stopped,
     * true otherwise
     */
    //@ requires command != null && command != "";
    protected boolean parseCommand(String command) {
        String[] args = command.split(" ");

        switch (args[0].toLowerCase()) {
            // GENERAL
            case "quit":
                return false;
            case "help":
                client.inform(getHelpMessage());
                return true;
            // GAMEPLAY
            case "h":
            case "hint":
                Move hint = client.getMove();
                if (hint != null) {
                    client.inform("Hint:");
                    client.informMove(null, hint);

                    if (args.length == 2 && (args[1].equals("s") || args[1].equals("send"))) {
                        try {
                            client.inform("You make the hint as your move");
                            client.getCurrentGame().update(hint.getPosition());
                            client.informBoard(client.getCurrentGame().getBoard());

                            ((OfflineClient) client).delayAI();
                            client.getCurrentGame().update(hint.getRotation());
                            client.informBoard(client.getCurrentGame().getBoard());

                            client.inform(String.format("%s, it's your turn!",
                                    client.getCurrentGame().getCurrentPlayer()));
                        } catch (BoardPositionException e) {
                            return false;
                        }
                        return true;
                    }
                }
                return true;
            case "p":
            case "place":
                if (client.getCurrentGame() != null) {
                    if (args.length != 2) {
                        client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
                    } else {
                        // try to update the position on the board
                        parsePosition(args[1], false);
                    }
                } else {
                    client.informError("You are not currently in a game");
                }
                return true;
            case "r":
            case "rot":
            case "rotate":
                Move move = parseMove(args, false);
                if (move != null) {
                    client.updateGame(move);
                    // we can reset it, because the move was updated
                    position = -1;
                    client.inform(String.format("%s, it's your turn!",
                            client.getCurrentGame().getCurrentPlayer()));
                    return true;
                }
                return true;
            default:
                // try to parse it as a 'place' command without the prefix
                if (client.getCurrentGame() != null && parsePosition(args[0], true)) {
                    return true;
                }

                // try to parse it as a 'rotate' command without the prefix
                Move temp = parseMove(args, true);
                if (temp != null) {
                    client.updateGame(temp);
                    // we can reset it, because the move was updated
                    position = -1;
                    client.inform(String.format("%s, it's your turn!",
                            client.getCurrentGame().getCurrentPlayer()));
                    return true;
                }
                // if it's null, it wasn't a move, so continue to next line

                client.informError("That's not a command");
                return true;
        }
    }

    /**
     * While running, obtain user commands and process them.
     * On exit, call the associated Client's {@code close()}.
     */
    @Override
    public void run() {
        while (running) {
            try {
                while (inputReader.ready()) {
                    String input = inputReader.readLine();

                    if (!input.equals("") && !parseCommand(input)) {
                        running = false;
                    }
                }
            } catch (IOException e) {
                Logger.info(this, "reader closed");
                running = false;
            }
        }

        client.close();

        Logger.info(this, "no longer running");
    }

    /**
     * Get the full help message of allowed commands for this input handler.
     *
     * @return the help message
     */
    //@ pure
    protected String getHelpMessage() {
        return "" +
                "---- ALLOWED COMMANDS --------------------------------------------------------\n" +
                " help                     show this help menu\n" +
                " quit                     quit the application\n" +
                "---- in-game -----------------------------------------------------------------\n" +
                " [p, place] <a-f1-6>      place your marble at an empty spot\n" +
                "                              first part can be omitted (smart parsing)\n" +
                "\n" +
                " [r, rot, rotate] <tl,tr,bl,br> <c,cc>\n" +
                "                          rotate sub board (counter) clockwise\n" +
                "                              first part can be omitted (smart parsing)\n" +
                "                              quadrants are 'tl' for 'top left' and so on\n" +
                "                              'c' is clockwise, 'cc' counterclockwise\n" +
                "\n" +
                " h, hint [s, send]        get a hint, optionally send as your move\n" +
                "------------------------------------------------------------------------------";
    }

    @Override
    public String toString() {
        return "OfflineTextInputHandler";
    }
}
