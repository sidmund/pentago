package ss.pentago.network.protocol;

import ss.pentago.file.Config;
import ss.pentago.model.exception.*;
import ss.pentago.model.player.PlayerFactory;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;
import ss.pentago.network.client.OnlineClient;
import ss.pentago.util.Logger;

import java.util.HashMap;
import java.util.Map;

/**
 * ClientProtocolHandler receives messages from the Server and parses them.
 * It tells the Client what to do.
 */
public class ClientProtocolHandler implements ProtocolHandler {

    //@ private invariant client != null;

    private static final String NOT_LOGGED_IN = "You are not logged in.";
    private static final String NOT_IN_GAME = "You are not in a game.";

    private final OnlineClient client;
    private String lastMove;

    /**
     * Records the start time when sending a ping.
     * This can then be compared against the current time when receiving pong.
     */
    private long startTimeOfPing;

    /**
     * Create a new ClientProtocolHandler for the specified Client.
     *
     * @param client the client to tell it what to do
     */
    //@ requires client != null;
    //@ ensures this.client == client;
    public ClientProtocolHandler(OnlineClient client) {
        this.client = client;
        client.resetMatch();
    }

    /**
     * Decode a protocol command received from the server, and perform a relevant reply.
     *
     * @param command the protol command
     */
    @Override
    public void receive(String command) {
        printDebugMessageReceived(command);
        String[] args = command.split(ProtocolCode.SEPARATOR);

        switch (ProtocolCode.parseString(args[0])) {
            case PING:
                sendPong();
                break;
            case PONG:
                receivePong();
                break;
            case ERROR:
                receiveError(args);
                break;
            case HELLO:
                receiveHello(args);
                break;
            case LOGIN:
                client.login();
                break;
            case ALREADYLOGGEDIN:
                client.informError("That player is already on the server.");
                break;
            case LIST:
                receiveList(args);
                break;
            case NEWGAME:
                setupNewGame(command, args);
                break;
            case MOVE:
                receiveMove(command, args);
                break;
            case GAMEOVER:
                receiveGameOver(command, args);
                break;
            case CHAT:
                receiveChat(command, args);
                break;
            case WHISPER:
                receiveWhisper(command, args);
                break;
            case CANNOTWHISPER:
                receiveCannotWhisper(command, args);
                break;
            case RANK:
                receiveRank(args);
                break;
            case QUIT:
                client.disconnect();
                break;
            case INVALID:
                // fall through
            default:
                sendError(command);
                break;
        }
    }

    /**
     * Check the received extensions and enable those in common.
     *
     * @param extensions the array of supported extensions
     */
    @Override
    public void setupExtensions(String[] extensions) {
        for (String ext : extensions) {
            switch (ProtocolCode.parseString(ext)) {
                case CRYPT:
                    client.enableCrypt();
                    break;
                case AUTH:
                    client.enableAuth();
                    break;
                case RANK:
                    client.enableRank();
                    break;
                case CHAT:
                    client.enableChat();
                    break;
                default:
                    // ignore unknown extension
                    break;
            }
        }
    }

    /**
     * Send an error message to the Logger. This is called when an invalid
     * Server command has been received.
     *
     * @param error the error description
     */
    @Override
    public void sendError(String error) {
        Logger.error(this, String.format("invalid message from server: %s", error));
    }

    /**
     * Send a ping to the server.
     *
     * @return false when the connection was closed
     */
    public boolean sendPing() {
        if (client.isLoggedIn()) {
            String ping = MessageFactory.createPingRequest();
            printDebugMessageSent(ping);
            startTimeOfPing = System.currentTimeMillis();

            return client.send(ping);
        } else {
            client.inform(NOT_LOGGED_IN);
            return true;
        }
    }

    /**
     * Send a pong upon receiving ping from the server.
     */
    private void sendPong() {
        if (client.isLoggedIn()) {
            String pong = MessageFactory.createPongReply();
            printDebugMessageSent(pong);

            if (!client.send(pong)) {
                printDebugMessageSent("writing error in sendPong");
            }
        } else {
            client.inform(NOT_LOGGED_IN);
        }
    }

    /**
     * Receive a pong from the server after we sent a ping.
     * Measure the time elapsed and inform the client about it.
     */
    private void receivePong() {
        long elapsed = System.currentTimeMillis() - startTimeOfPing;
        String latency = String.format("Latency: %d ms", elapsed);
        client.inform(latency);
    }

    /**
     * Ask the client this client is in a game with to disconnect.
     *
     * @return false if a writing error occurred, true if success
     */
    public boolean sendQuit() {
        if (client.isLoggedIn() && client.isInGame()) {
            String quit = MessageFactory.createQuitRequest();
            printDebugMessageSent(quit);
            return client.send(quit);
        } else {
            client.inform("You are not logged in or not in a game.");
            return true;
        }
    }

    /**
     * Receive an error message, which is printed to the Logger.
     *
     * @param args the arguments
     */
    private void receiveError(String[] args) {
        if (checkArgumentLengthExact(args, 2)) {
            // description is optional
            printDebugMessageReceived(String.format("error '%s'", args[1]));
        } else {
            printDebugMessageReceived("error");
        }
    }

    /**
     * Start the initialization sequence with the server.
     *
     * @param description the client description
     */
    public void sendHello(String description) {
        String hello = MessageFactory.createHelloMessage(
                description,
                Config.doesClientSupportAuth(),
                Config.doesClientSupportCrypt(),
                Config.doesClientSupportChat(),
                Config.doesClientSupportRank()
        );
        printDebugMessageSent(hello);

        if (!client.send(hello)) {
            printDebugMessageSent("writing error in sendHello");
        }
    }

    /**
     * Receive the hello message from the server.
     * Enable the extensions both sides support.
     *
     * @param args the arguments containing the server description and extensions
     */
    private void receiveHello(String[] args) {
        client.inform(String.format("Connected to server '%s'", args[1]));
        String[] extensions = new String[args.length - 2];
        System.arraycopy(args, 2, extensions, 0, args.length - 2);
        setupExtensions(extensions);
    }

    /**
     * Sends a Login request to the server.
     *
     * @param username the username
     * @return false when the connection was closed
     */
    public boolean sendLogin(String username) {
        String login = MessageFactory.createLoginMessage(username);
        printDebugMessageSent(login);

        return client.send(login);
    }

    /**
     * Sends a list request to the server.
     *
     * @return false when the connection was closed
     */
    public boolean sendList() {
        if (client.isLoggedIn()) {
            String list = MessageFactory.createListRequest();
            printDebugMessageSent(list);

            return client.send(list);
        } else {
            client.inform(NOT_LOGGED_IN);
            return true;
        }
    }

    /**
     * Receive a list of online users from the server.
     *
     * @param args the arguments containing online users
     */
    private void receiveList(String[] args) {
        String[] connectedClients = new String[args.length - 1];
        System.arraycopy(args, 1, connectedClients, 0, args.length - 1);
        client.informList(connectedClients);
    }

    /**
     * Sends a Queue request to the server.
     * This toggles whether the client is in the queue or not.
     *
     * @return false when the connection was closed
     */
    public boolean sendQueue() {
        if (client.isLoggedIn()) {
            if (client.isInGame()) {
                client.inform("You can't queue while in game...");
                return true;
            }

            String queue = MessageFactory.createQueueRequest();
            printDebugMessageSent(queue);

            client.toggleQueue();
            if (client.isQueued()) {
                client.inform("Waiting for a game to start...");
            } else {
                client.inform("Left the queue");
            }
            return client.send(queue);
        } else {
            client.inform(NOT_LOGGED_IN);
            return true;
        }
    }

    /**
     * Receive a new game command and set it up for the client.
     *
     * @param command the full command
     * @param args    the arguments containing both players
     */
    //@ requires command != null && args != null && args.length == 3;
    private void setupNewGame(String command, String[] args) {
        if (checkArgumentLengthExact(args, 3)) {
            if (client.isLoggedIn()) {
                client.startGame(
                        PlayerFactory.makeHumanPlayer(args[1]),
                        PlayerFactory.makeHumanPlayer(args[2]));
            } else {
                client.inform("Dropped new game request from server.");
            }
        } else {
            sendError(command);
        }
    }

    /**
     * Send the move to the server.
     *
     * @param move the move
     * @return false when the connection was closed
     */
    //@ requires move != null;
    public boolean sendMove(Move move) {
        if (!client.isLoggedIn()) {
            client.inform(NOT_LOGGED_IN);
            return true;
        }

        if (!client.isInGame()) {
            client.inform(NOT_IN_GAME);
            return true;
        }

        if (!client.hasOpponentMoved()) {
            if (client.showGameplay()) {
                client.inform("Still waiting for opponent move.");
            }
            return true;
        }

        if (!client.isMoveConfirmed()) {
            if (client.showGameplay()) {
                client.inform("Can't send a new move now, still awaiting confirmation.");
            }
            return true;
        }

        if (move == null) {
            printDebugMessageSent("move was null");
            return true;
        }

        try {
            int index = move.getPosition();
            int rotation = move.getRotation().getCode();

            client.setIsMoveConfirmed(false);
            lastMove = String.format("%d,%d", index, rotation);
            String moveCmd = MessageFactory.createMoveMessage(index, rotation);
            printDebugMessageSent(moveCmd);
            return client.send(moveCmd);
        } catch (RotationFormatException e) {
            // can be ignored, the move will be valid at this point
            return true;
        }
    }

    /**
     * Receive a move from the server.
     *
     * @param command the full command
     * @param args    the arguments containing the indices of the position and the rotation
     */
    //@ requires command != null && args != null && args.length == 3;
    private void receiveMove(String command, String[] args) {
        if (!checkArgumentLengthExact(args, 3)) {
            sendError(command);
            return;
        }

        if (!client.isLoggedIn() && !client.isInGame()) {
            sendError("received move without being in game");
            return;
        }

        int position;
        Rotation rot;
        try {
            position = Move.parseIndex(Integer.parseInt(args[1]));
            int rotationCode = Integer.parseInt(args[2]);
            rot = Rotation.parseRotation(rotationCode);
        } catch (NumberFormatException
                | MovePositionFormatException
                | RotationFormatException e) {
            sendError(String.format("illegal move: index=%s, rotation=%s",
                    args[1], args[2]));
            return;
        }

        Move move = new Move(position, rot);
        try {
            if (String.format("%d,%d", move.getPosition(), rot.getCode()).equals(lastMove)) {
                // this was a confirmation move
                client.setIsMoveConfirmed(true);
                client.setHasOpponentMoved(false);
                client.informMove(client.getCurrentGame().getCurrentPlayer(), move);
                client.updateGame(move);
                if (client.showGameplay()) {
                    client.inform(String.format("It's the opponent's turn: %s",
                            client.getCurrentGame().getCurrentPlayer()));
                }
            } else {
                // this was the opponent's move
                client.setHasOpponentMoved(true);
                client.informMove(client.getCurrentGame().getCurrentPlayer(), move);
                client.updateGame(move);
                if (client.showGameplay()) {
                    client.inform(String.format("It's your turn now: %s",
                            client.getCurrentGame().getCurrentPlayer()));
                }
            }
        } catch (RotationFormatException e) {
            sendError(String.format("illegal move: %s", move));
        }
    }

    /**
     * Receive a game over.
     *
     * @param command the full command
     * @param args    the arguments, containing the reason and possibly a winner
     */
    //@ requires args != null && (args.length == 2 || args.length == 3);
    private void receiveGameOver(String command, String[] args) {
        if (checkArgumentLengthExact(args, 2)) {
            endGameDraw(args[1]);
        } else if (checkArgumentLengthExact(args, 3)) {
            endGameWinner(args[1], args[2]);
        } else {
            sendError(command);
        }
    }

    /**
     * End the Client's game as a draw.
     *
     * @param reason draw
     */
    private void endGameDraw(String reason) {
        if (client.isLoggedIn() && client.isInGame()) {
            if (reason.equals(ProtocolCode.DRAW.toString())) {
                client.resetMatch();

                client.endGameDraw();
            } else {
                sendError("This reason shouldn't happen " + reason);
            }
        } else {
            sendError("We are not in game, but we got a game over?! " + reason);
        }
    }

    /**
     * End the Client's game as a disconnection victory or a real victory.
     *
     * @param reason the reason
     * @param winner the winner
     */
    private void endGameWinner(String reason, String winner) {
        if (client.isLoggedIn() && client.isInGame()) {
            if (reason.equals(ProtocolCode.VICTORY.toString())) {
                client.resetMatch();

                client.endGameVictory(winner);
            } else if (reason.equals(ProtocolCode.DISCONNECT.toString())) {
                client.resetMatch();

                client.endGameDisconnect(winner);
            } else {
                sendError("This reason shouldn't happen " + reason);
            }
        } else {
            sendError("We are not in game, but we got a game over?! " + reason);
        }
    }

    /**
     * Sends a chat to all online users on the server.
     *
     * @param message the message
     * @return false when the connection was closed
     */
    public boolean sendChat(String message) {
        if (client.isLoggedIn()) {
            String chat = MessageFactory.createChatMessage(message);
            printDebugMessageSent(chat);

            return client.send(chat);
        } else {
            client.inform(NOT_LOGGED_IN);
            return true;
        }
    }

    /**
     * Receive a chat message from a sender.
     *
     * @param command the full command
     * @param args    the arguments, containing the sender and the message
     */
    private void receiveChat(String command, String[] args) {
        if (checkArgumentLengthMin(args, 2)) {
            client.informChat(args[1], MessageFactory.decodeChatMessage(command));
        } else {
            sendError(command);
        }
    }

    /**
     * Sends a private message to the recipient.
     *
     * @param recipient the recipient
     * @param message   the message
     * @return false when the connection was closed
     */
    public boolean sendWhisper(String recipient, String message) {
        if (client.isLoggedIn()) {
            String whisper = MessageFactory.createWhisperMessageFor(recipient, message);
            printDebugMessageSent(whisper);

            return client.send(whisper);
        } else {
            client.inform(NOT_LOGGED_IN);
            return true;
        }
    }

    /**
     * Receive a private message from another Client.
     *
     * @param command the full command
     * @param args    the arguments, containing sender and message
     */
    private void receiveWhisper(String command, String[] args) {
        if (checkArgumentLengthMin(args, 2)) {
            client.informWhisper(args[1], MessageFactory.decodeWhisperMessage(command));
        } else {
            sendError(command);
        }
    }

    /**
     * Receive a message that the Client this Client wanted to whisper to,
     * is not online or does not support chat.
     *
     * @param command the full command
     * @param args    the arguments, containing the recipient
     */
    private void receiveCannotWhisper(String command, String[] args) {
        if (checkArgumentLengthExact(args, 2)) {
            client.informError(
                    String.format("'%s' is not on the server or does not support chat.",
                            args[1]));
        } else {
            sendError(command);
        }
    }

    /**
     * Request the ranking.
     *
     * @return false if a writing error occurred, true if success
     */
    public boolean sendEloRank() {
        if (client.isLoggedIn()) {
            String rank = MessageFactory.createRankRequest();
            printDebugMessageSent(rank);
            return client.send(rank);
        } else {
            client.inform(NOT_LOGGED_IN);
            return true;
        }
    }

    /**
     * Receive the rankings on the server by their ELO stat.
     *
     * @param args the arguments containing the rankings
     */
    private void receiveRank(String[] args) {
        try {
            Map<String, Integer> rankings = new HashMap<>();

            for (int i = 1; i < args.length; i += 2) {
                if (i + 1 >= args.length) {
                    throw new NumberFormatException();
                }

                rankings.put(args[i], Integer.parseInt(args[i + 1]));
            }

            client.informRankings(rankings);
        } catch (NumberFormatException e) {
            sendError("Invalid format of rank message");
        }
    }

    /**
     * Utility method to check username validity.
     *
     * @param username the username
     * @return true when valid, false otherwise
     */
    /*@
        ensures \result ==> !(username == null || username.equals("") ||
                username.contains(ProtocolCode.SEPARATOR));
    */
    //@ pure
    public static boolean isAcceptableUsername(String username) {
        return !(username == null || username.equals("") ||
                username.contains(ProtocolCode.SEPARATOR));
    }

    /**
     * @return String "ClientProtocolHandler" + client username
     */
    //@ pure
    @Override
    public String toString() {
        return "ClientProtocolHandler:" + client.getUsername();
    }
}
