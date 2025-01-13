package ss.pentago.network.protocol;

import ss.pentago.network.server.ClientHandler;
import ss.pentago.network.server.Server;
import ss.pentago.util.Logger;

/**
 * ServerProtocolHandler receives messages from the Client and parses them.
 * It tells the ClientHandler what to do.
 */
public class ServerProtocolHandler implements ProtocolHandler {

    //@ private invariant clientHandler != null;

    private final ClientHandler clientHandler;

    /**
     * Create a new ServerProtocolHandler for the specified ClientHandler.
     *
     * @param clientHandler the clientHandler to tell it what to do
     */
    //@ requires clientHandler != null;
    //@ ensures this.clientHandler == clientHandler;
    public ServerProtocolHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }

    /**
     * Decode a message received from a client, and perform a relevant reply.
     *
     * @param command the protocol command
     */
    @Override
    public void receive(String command) {
        printDebugMessageReceived(command);
        String[] args = command.split(ProtocolCode.SEPARATOR);

        switch (ProtocolCode.parseString(args[0])) {
            case PING:
                receivePing(args);
                break;
            case PONG:
                receivePong(args);
                break;
            case HELLO:
                receiveHello(args);
                break;
            case LOGIN:
                receiveLogin(args);
                break;
            case QUEUE:
                receiveQueue(args);
                break;
            case MOVE:
                receiveMove(args);
                break;
            case LIST:
                receiveList(args);
                break;
            case CHAT:
                receiveChat(command);
                break;
            case WHISPER:
                receiveWhisper(args, args[1], command);
                break;
            case RANK:
                receiveRank(args);
                break;
            case QUIT:
                if (checkArgumentLengthExact(args, 1)) {
                    clientHandler.disconnect();
                }
                break;
            default:
                // Unknown command should send error, quit then close socket
                sendError("Unknown command: " + command);
                sendQuit();
                clientHandler.closeSocket();
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
                    clientHandler.getServer().enableCrypt();
                    break;
                case AUTH:
                    clientHandler.getServer().enableAuth();
                    break;
                case RANK:
                    clientHandler.getServer().enableRank();
                    break;
                case CHAT:
                    clientHandler.getServer().enableChat();
                    break;
                default:
                    // ignore unknown extension
                    break;
            }
        }
    }

    /**
     * Send the error message to the Client and if unsuccessful then call handleFailMessage.
     *
     * @param error the error message
     */
    @Override
    public void sendError(String error) {
        String s = MessageFactory.createErrorMessage(error);
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    /**
     * This method is called when ClientHandler's send method couldn't send
     * due to a closed socket.
     *
     * @param error the error message
     */
    private void handleFailMessage(String error) {
        Logger.error(this, "fail to send: %s", error);
    }

    /**
     * Send a ping to the client.
     */
    public void sendPing() {
        if (checkLogin()) {
            String ping = MessageFactory.createPingRequest();
            printDebugMessageSent(ping);
            if (!clientHandler.send(ping)) {
                handleFailMessage(ping);
            }
        }
    }

    /**
     * Send a pong message to client in response of their ping.
     *
     * @param args the arguments
     */
    //@ requires args != null && args.length == 1;
    private void receivePing(String[] args) {
        if (checkLogin() && checkArgumentLengthExact(args, 1)) {
            String s = MessageFactory.createPongReply();
            printDebugMessageSent(s);
            if (!clientHandler.send(s)) {
                handleFailMessage(s);
            }
        }
    }

    /**
     * Receive a pong from the client, this will reset the disconnection timer,
     * making sure the client is still seen as connected.
     *
     * @param args the arguments
     */
    //@ requires args != null && args.length == 1;
    private void receivePong(String[] args) {
        if (checkLogin() && checkArgumentLengthExact(args, 1)) {
            clientHandler.getServer().resetDisconnectionTime(clientHandler);
        }
    }

    /**
     * Send hello back with description and supported extensions.
     *
     * @param args the whole received message
     */
    public void receiveHello(String[] args) {
        if (checkArgumentLengthMinMax(args, 2, 7)) {
            String[] extensions = new String[args.length - 2];
            System.arraycopy(args, 2, extensions, 0, args.length - 2);
            setupExtensions(extensions);

            String hello = MessageFactory.createHelloMessage(
                    Server.SERVER_DESCRIPTION,
                    clientHandler.getServer().isAuthSupported(),
                    clientHandler.getServer().isCryptSupported(),
                    clientHandler.getServer().isChatSupported(),
                    clientHandler.getServer().isRankSupported()
            );
            printDebugMessageSent(hello);
            if (!clientHandler.send(hello)) {
                handleFailMessage(hello);
            }
        }
    }

    /**
     * check login and deal with error if the client is not logged in.
     *
     * @return login state
     */
    //@ ensures \result == clientHandler.isLoggedIn();
    private boolean checkLogin() {
        if (!clientHandler.isLoggedIn()) {
            sendError("Requires Login");
            return false;
        }
        return true;

    }

    /**
     * Send a LOGIN to the client to indicate the client is login to the server.
     */
    public void sendLogin() {
        String s = MessageFactory.createLoginReply();
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    /**
     * Handle login.
     *
     * @param args the argument
     */
    private void receiveLogin(String[] args) {
        if (checkArgumentLengthExact(args, 2)) {
            if (clientHandler.getServer().isUsernamePresent(args[1])
                    || clientHandler.isLoggedIn()) {
                sendAlreadyLogin();
            } else {
                clientHandler.setUsername(args[1]);
                clientHandler.login();
                sendLogin();
            }
        }
    }

    /**
     * Send a ALREADYLOGGEDIN to the client to indicate the invalid username
     * or already login.
     */
    public void sendAlreadyLogin() {
        String s = MessageFactory.createAlreadyLoggedInReply();
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }


    /**
     * Send a QUIT to the client.
     */
    public void sendQuit() {
        String s = MessageFactory.createQuitRequest();
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    /**
     * Sends a LIST to the client.
     *
     * @param args the arguments
     */
    public void receiveList(String[] args) {
        if (checkLogin() && checkArgumentLengthExact(args, 1)) {
            String list = MessageFactory.createListMessage(clientHandler.getServer().getUserList());
            printDebugMessageSent(list);
            if (!clientHandler.send(list)) {
                handleFailMessage(list);
            }
        }
    }


    /**
     * Send CANNOTWHISPHER to client.
     *
     * @param recipient the recipient
     */
    public void sendCannotWhisper(String recipient) {
        String s = MessageFactory.createCannotWhisperReply(recipient);
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    /**
     * Handle queue.
     *
     * @param args the whole argument from command
     */
    private void receiveQueue(String[] args) {
        if (checkLogin() && checkArgumentLengthExact(args, 1)) {
            if (clientHandler.isInGame()) {
                sendError("You cannot queue since you already in the match!");
            } else {
                if (clientHandler.queue()) {
                    Logger.info(this, "%s enter queue", clientHandler.getUsername());
                } else {
                    Logger.info(this, "%s dequeue", clientHandler.getUsername());
                }
            }
        }
    }

    /**
     * Send a NEWGAME message to client.
     *
     * @param p1 username of Black player (Player who start first)
     * @param p2 username of White player (Player who start second)
     */
    public void sendNewGame(String p1, String p2) {
        String s = MessageFactory.createNewGameMessage(p1, p2);
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    /**
     * handle move command.
     *
     * @param args the argument
     */
    private void receiveMove(String[] args) {
        if (checkLogin() && checkArgumentLengthExact(args, 3)) {
            try {
                int position = Integer.parseInt(args[1]);
                int rotation = Integer.parseInt(args[2]);
                if (!clientHandler.getServer().getGameManager()
                        .updateMatchOf(clientHandler, position, rotation)) {
                    sendError("Unknown ERROR");
                }
            } catch (NumberFormatException e) {
                sendError("NumberFormatException");
            }
        }
    }


    /**
     * Send the move to the client.
     *
     * @param position the position
     * @param rotation the rotation
     */
    public void sendMove(int position, int rotation) {
        String s = MessageFactory.createMoveMessage(position, rotation);
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    public void sendGameOverWinner(String winner) {
        String s = MessageFactory.createGameOverVictoryMessage(winner);
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            sendError("Cant send win result");
        }
    }

    /**
     * Send GAMEOVER~DRAW to client.
     */
    public void sendGameOverDraw() {
        String s = MessageFactory.createGameOverDrawMessage();
        printDebugMessageSent(s);
        if (!clientHandler.send(s)) {
            handleFailMessage(s);
        }
    }

    /**
     * Send Game Over disconnect message to client.
     *
     * @param dcUser the disconnect player
     * @param dc whether disconnect
     */
    public void sendGameOverDisconnect(String dcUser, boolean dc) {
        String s = MessageFactory.createGameOverDisconnectMessage(dcUser);
        printDebugMessageSent(s);
        if (!clientHandler.send(s) && !dc) {
            handleFailMessage(s);
        }
    }

    /**
     * Send CHAT + message to client for all chat.
     *
     * @param message the message
     */
    private void receiveChat(String message) {
        int chatCmdLen = ProtocolCode.CHAT.toString().length();
        if (checkLogin() && message.length() >= chatCmdLen + 1
                && message.startsWith(ProtocolCode.SEPARATOR, chatCmdLen)) {

            clientHandler.getServer().sendChat(clientHandler,
                    MessageFactory.createChatMessageFor(clientHandler.getUsername(), message));
        }
    }

    /**
     * Send WHISPER + message to client for private chat.
     *
     * @param args      the receive message
     * @param message   the message
     * @param recipient the recipient
     */
    private void receiveWhisper(String[] args, String recipient, String message) {
        if (checkLogin() && args.length >= 2) {
            clientHandler.getServer().sendWhisper(clientHandler, recipient,
                    MessageFactory.createWhisperMessageFrom(clientHandler.getUsername(), message));
        }
    }

    /**
     * Send the ELO rankings.
     *
     * @param args the arguments
     */
    private void receiveRank(String[] args) {
        if (clientHandler.getServer().isRankEnabled() && checkLogin()
                && checkArgumentLengthExact(args, 1)) {
            String rank = MessageFactory.createEloRankMessageFor(
                    clientHandler.getServer().getEloRankings());
            printDebugMessageSent(rank);
            if (!clientHandler.send(rank)) {
                handleFailMessage(rank);
            }
        }
    }

    @Override
    public String toString() {
        return "ServerProtocolHandler:" + clientHandler.getUsername();
    }
}
