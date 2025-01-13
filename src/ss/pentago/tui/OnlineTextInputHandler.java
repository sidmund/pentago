package ss.pentago.tui;

import ss.pentago.file.Config;
import ss.pentago.model.move.Move;
import ss.pentago.model.player.PlayerFactory;
import ss.pentago.network.client.OnlineClient;
import ss.pentago.network.protocol.ClientProtocolHandler;
import ss.pentago.util.Logger;

import java.io.IOException;

/**
 * The {@code OnlineTextInputHandler} processes user input from {@code System.in} and
 * tells the {@code Client} what to do with it.
 * The {@code OnlineTextInputHandler} extends {@code OfflineTextInputHandler}
 * by using a {@code Protocol} to send the user input to a server.
 */
public class OnlineTextInputHandler extends OfflineTextInputHandler {

    /**
     * Keep track of the associated Client's ProtocolHandler to
     * circumvent excessive casting.
     */
    protected final ClientProtocolHandler protocol;

    /**
     * For autoMode or BotInputHandlers:
     * After we make our move, record the time to determine how long the opponent is taking.
     */
    protected long opponentStartTime;

    private boolean autoMode;

    /**
     * Creates a new {@code TextInputHandler} object.
     *
     * @param client the client to send input to
     */
    /*@
        requires client != null;
        ensures this.client == client && this.client instanceof OnlineClient;
    */
    public OnlineTextInputHandler(OnlineClient client) {
        super(client);
        protocol = client.getProtocolHandler();
    }

    /**
     * Try to set the position. This only updates a copy of the local board,
     * and doesn't send anything to the Server.
     *
     * @param args the arguments
     */
    //@ requires args != null;
    private void setPosition(String[] args) {
        if (((OnlineClient) client).hasOpponentMoved()) {
            if (args.length != 2) {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
            } else {
                parsePosition(args[1], false);
            }
        } else {
            client.informError("Please wait your turn");
        }
    }

    /**
     * Try to send the parsed full move and send to the server.
     *
     * @param move         move
     * @param checkQuietly whether to suppress error messages
     * @return false if the message couldn't be send due to closed socket, true otherwise
     */
    //@ requires move != null;
    private boolean sendMove(Move move, boolean checkQuietly) {
        if (((OnlineClient) client).hasOpponentMoved()) {
            if (!protocol.sendMove(move)) {
                return false;
            }

            // we can reset it, because the move was sent
            position = -1;
        } else if (!checkQuietly) {
            client.informError("Please wait your turn");
        }
        return true;
    }

    /**
     * Get a hint, and optionally send it.
     *
     * @param args the arguments
     * @return false if the message couldn't be send due to closed socket, true otherwise
     */
    //@ requires args != null;
    private boolean getHint(String[] args) {
        Move hint = client.getMove();
        if (hint != null) {
            client.inform(String.format("Hint: %s%n", hint));

            if (args.length == 2 && (args[1].equals("s") || args[1].equals("send"))) {
                client.inform("You sent the hint as your move");
                return protocol.sendMove(hint);
            }
        }
        return true;
    }

    /**
     * Send a chat.
     *
     * @param command the full command
     * @param args    the arguments
     * @return false if the message couldn't be send due to closed socket, true otherwise
     */
    //@ requires command != null && args != null;
    private boolean sendChat(String command, String[] args) {
        if (((OnlineClient) client).isChatEnabled()) {
            if (args.length >= 2) {
                // skip command name
                String msg = command.substring(command.indexOf(" ") + 1);
                return protocol.sendChat(msg);
            } else {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
                return true;
            }
        } else {
            client.informError("Chat is disabled");
            return true;
        }
    }

    /**
     * Send a whisper.
     *
     * @param command the full command
     * @param args    the arguments
     * @return false if the message couldn't be send due to closed socket, true otherwise
     */
    //@ requires command != null && args != null;
    private boolean sendWhisper(String command, String[] args) {
        if (((OnlineClient) client).isChatEnabled()) {
            if (args.length >= 3) {
                // skip command name
                String msg = command.substring(command.indexOf(" ") + 1);

                String recipient;
                String message;
                if (args[1].startsWith("'")) {
                    // a username containing spaces
                    int firstIndex = msg.indexOf("'"); // first '
                    int secondIndex = msg.indexOf("'", firstIndex + 1); // second '
                    recipient = msg.substring(firstIndex + 1, secondIndex);
                    message = msg.substring(secondIndex + 2); // skip "' "
                } else {
                    recipient = args[1];
                    message = msg.substring(msg.indexOf(" ") + 1);
                }
                return protocol.sendWhisper(recipient, message);
            } else {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
                return true;
            }
        } else {
            client.informError("Chat is disabled");
            return true;
        }
    }

    /**
     * Request the ELO ranking.
     *
     * @param args the arguments
     * @return false if the message couldn't be send due to closed socket, true otherwise
     */
    //@ requires args != null;
    private boolean getRanking(String[] args) {
        if (!((OnlineClient) client).isRankEnabled()) {
            client.informError("Rank is disabled");
            return true;
        } else if (args.length != 1) {
            client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
            return true;
        } else {
            return protocol.sendEloRank();
        }
    }

    /**
     * Toggle auto made, i.e. play as a bot of desired difficulty.
     *
     * @param args the arguments
     */
    //@ requires args != null;
    private void autoMode(String[] args) {
        if (args.length == 1) {
            if (autoMode) {
                autoMode = false;
                client.inform("Disabled auto mode");
            } else {
                client.inform("Auto mode is already disabled");
            }
        } else if (args.length == 2) {
            try {
                int difficulty = Integer.parseInt(args[1]);
                if (difficulty < PlayerFactory.MIN_AI_DIFFICULTY
                        || difficulty > PlayerFactory.MAX_AI_DIFFICULTY) {
                    throw new NumberFormatException();
                }

                autoMode = true;
                ((OnlineClient) client).setStrategy(PlayerFactory.makeAIStrategy(difficulty));
                client.inform(String.format("Enabled auto mode at difficulty: %d", difficulty));
            } catch (NumberFormatException e) {
                client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
            }
        } else {
            client.informError(INVALID_COMMAND_USAGE_HELP_MESSAGE);
        }
    }

    /**
     * Parses the supplied command, and tells the Client what to do.
     *
     * @param command the command
     * @return false if the client needs to be stopped
     * (due to messages not being sent in case of a closed connection),
     * true otherwise
     */
    //@ requires command != null && command != "";
    @Override
    protected boolean parseCommand(String command) {
        if (command == null) {
            return true;
        }

        String[] args = command.split(" ");

        switch (args[0].toLowerCase()) {
            // GENERAL
            case "ping":
                return protocol.sendPing();
            case "quit":
                return false;
            case "help":
                client.inform(getHelpMessage());
                return true;
            case "l":
            case "list":
                return protocol.sendList();
            case "q":
            case "queue":
                return protocol.sendQueue();
            // BONUS
            case "c":
            case "chat":
                return sendChat(command, args);
            case "w":
            case "whisper":
                return sendWhisper(command, args);
            case "rank":
                return getRanking(args);
            // BOT
            case "auto":
                autoMode(args);
                return true;
            // GAMEPLAY
            case "h":
            case "hint":
                return getHint(args);
            case "p":
                if (args.length == 1) {
                    // without args: assume it's the ping command
                    return protocol.sendPing();
                }
                // NB: fall through to 'place' if args.length > 1
            case "place":
                if (client.getCurrentGame() != null) {
                    setPosition(args);
                } else {
                    client.informError("You are not currently in a game");
                }
                return true;
            case "r":
            case "rot":
            case "rotate":
                Move move = parseMove(args, false);
                if (move != null) {
                    return sendMove(move, false);
                }
                return true;
            default:
                // try to parse it as a 'place' command without the prefix
                if (client.getCurrentGame() != null
                        && ((OnlineClient) client).hasOpponentMoved()
                        && parsePosition(args[0], true)) {
                    return true;
                }

                // try to parse it as a 'rotate' command without the prefix
                Move temp = parseMove(args, true);
                if (temp != null) {
                    return sendMove(temp, true);
                }
                // if it's null, it wasn't a move, so continue to next line

                client.informError("That's not a command");
                return true;
        }
    }

    /**
     * Check the username and try to send it to the Server to login.
     *
     * @param username the username (from input)
     * @throws IOException thrown when the Server closed the connection
     */
    protected void setUsername(String username) throws IOException {
        if (ClientProtocolHandler.isAcceptableUsername(username)) {

            if (!protocol.sendLogin(username)) {
                client.informError("Disconnected from server");
                // make sure it exits out of this buffered reader loop without
                // trying to read more input below this while block
                throw new IOException();

            } else {
                ((OnlineClient) client).setUsername(username);
                client.inform(
                        String.format("Welcome to the server, %s!", username));
            }

        } else {
            client.inform("That username is not valid, try again.");
        }
    }

    /**
     * While running, obtain user commands from System.in and process them,
     * telling the client what to do. On exit, call the associated Client's {@code close()}.
     */
    @Override
    public void run() {
        protocol.sendHello("Amazing Client");

        client.inform("Enter your name to login to the server: ");

        // Obtain user input
        while (running) {
            try {
                // ready() should make sure that if there's a line, it won't block
                while (inputReader.ready()) {
                    String input = inputReader.readLine();

                    // If we're not logged in, the first message should be the username
                    if (!((OnlineClient) client).isLoggedIn()) {
                        setUsername(input);

                        // If we are logged in, interpret input as a command
                    } else if (!input.equals("") && !parseCommand(input)) {
                        // If we close here, going back to the main menu
                        // (which has a Scanner(System.in)) will throw errors,
                        // and not closing here is actually not a problem...
//                            inputReader.close();
                        running = false;
                    }
                }
            } catch (IOException e) {
                Logger.info(this, "reader closed");
                running = false;
            }

            if (((OnlineClient) client).isLoggedIn() && autoMode) {
                determineBotAction();

                delay();
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
    @Override
    protected String getHelpMessage() {
        return "" +
                "---- ALLOWED COMMANDS --------------------------------------------------------\n" +
                " q, queue                 queue up for a game\n" +
                " l, list                  show a list of online players\n" +
                " p, ping                  measure the connection to the server\n" +
                (((OnlineClient) client).isChatEnabled()
                        ? " c, chat <msg>            send a message to the global chat\n"
                        + " w, whisper <user> <msg>  send a message to the user\n"
                        + "                          use '<user>' if username contains spaces\n"
                        : "") +
                (((OnlineClient) client).isRankEnabled()
                        ? " rank                     show the ELO leaderboard\n"
                        : "") +
                " help                     show this help menu\n" +
                " quit                     quit the application\n" +
                "---- bot ---------------------------------------------------------------------\n" +
                String.format(
                        " auto <%d-%d>               turn on auto mode, %d is lowest difficulty%n",
                        PlayerFactory.MIN_AI_DIFFICULTY, PlayerFactory.MAX_AI_DIFFICULTY,
                        PlayerFactory.MIN_AI_DIFFICULTY) +
                " auto                     turn off auto mode\n" +
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

    /**
     * Make the Thread wait a bit, so the Bot doesn't move too fast.
     */
    protected void delay() {
        try {
            Thread.sleep(Config.getResponseDelayMultiPlayer());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            // ignore
        }
    }

    /**
     * A method that handles automated game play.
     */
    protected void determineBotAction() {
        if (!((OnlineClient) client).isQueued()) {

            // -- Priority 1. Queue if we're not in a queue ----

            if (!protocol.sendQueue()) {
                running = false;
            }

        } else if (((OnlineClient) client).isInGame()) {

            // -- Priority 2. Play the game ----

            if (((OnlineClient) client).hasOpponentMoved()) {

                // The opponent has moved, send our move

                if (!protocol.sendMove(client.getMove())) {
                    running = false;
                } else {
                    opponentStartTime = System.currentTimeMillis();
                }

            } else {

                // The opponent hasn't moved yet, check the timer

                long elapsed = System.currentTimeMillis() - opponentStartTime;
                client.inform(String.format(
                        "%d ms elapsed while waiting for opponent to move", elapsed));

                // And request them to disconnect if it's taking too long

                if (elapsed > Config.getTimeUntilDisconnect()
                        && !protocol.sendQuit()) {
                    running = false;
                }
            }
        }
    }
}
