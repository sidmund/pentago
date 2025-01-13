package ss.pentago.network.protocol;

import ss.pentago.network.server.rank.RankedPlayer;

import java.util.List;

/**
 * MessageFactory deals only with the proper formatting of messages.
 * The ProtocolHandler classes, on the other hand, should be used for the logic
 * around sending/receiving these messages.
 */
public class MessageFactory {

    private static final String FORMAT_LENGTH_3 = "%s%s%s";
    private static final String FORMAT_LENGTH_4 = "%s%s%s%s";
    private static final String FORMAT_LENGTH_5 = "%s%s%s%s%s";

    private MessageFactory() {
    }

    // -- Initialization

    /**
     * Format a hello message.
     *
     * @param description      the description of either Server or Client
     * @param isAuthSupported  whether the auth extension is supported
     * @param isCryptSupported whether the crypt extension is supported
     * @param isChatSupported  whether the chat extension is supported
     * @param isRankSupported  whether the rank extension is supported
     * @return formatted message
     */
    public static String createHelloMessage(
            String description, boolean isAuthSupported, boolean isCryptSupported,
            boolean isChatSupported, boolean isRankSupported) {

        StringBuilder sb = new StringBuilder();
        sb.append(String.format(FORMAT_LENGTH_3,
                ProtocolCode.HELLO, ProtocolCode.SEPARATOR, description));

        if (isAuthSupported) {
            sb.append(String.format("%s%s", ProtocolCode.SEPARATOR, ProtocolCode.AUTH));
        }
        if (isCryptSupported) {
            sb.append(String.format("%s%s", ProtocolCode.SEPARATOR, ProtocolCode.CRYPT));
        }
        if (isChatSupported) {
            sb.append(String.format("%s%s", ProtocolCode.SEPARATOR, ProtocolCode.CHAT));
        }
        if (isRankSupported) {
            sb.append(String.format("%s%s", ProtocolCode.SEPARATOR, ProtocolCode.RANK));
        }

        return sb.toString();
    }

    /**
     * Format a login message.
     *
     * @param username the username of the Client
     * @return formatted message
     */
    public static String createLoginMessage(String username) {
        return String.format(FORMAT_LENGTH_3,
                ProtocolCode.LOGIN, ProtocolCode.SEPARATOR, username);
    }

    /**
     * Format a login reply.
     *
     * @return formatted message
     */
    public static String createLoginReply() {
        return ProtocolCode.LOGIN.toString();
    }

    /**
     * Format an already logged in reply.
     *
     * @return formatted message
     */
    public static String createAlreadyLoggedInReply() {
        return ProtocolCode.ALREADYLOGGEDIN.toString();
    }

    // -- General ----

    /**
     * Format a ping request.
     *
     * @return formatted message
     */
    public static String createPingRequest() {
        return ProtocolCode.PING.toString();
    }

    /**
     * Format a pong reply.
     *
     * @return formatted message
     */
    public static String createPongReply() {
        return ProtocolCode.PONG.toString();
    }

    /**
     * Format an error message.
     *
     * @param error the error description
     * @return formatted message
     */
    public static String createErrorMessage(String error) {
        return String.format(FORMAT_LENGTH_3, ProtocolCode.ERROR, ProtocolCode.SEPARATOR, error);
    }

    /**
     * Format a quit request.
     *
     * @return formatted message
     */
    public static String createQuitRequest() {
        return ProtocolCode.QUIT.toString();
    }

    /**
     * Format a list request.
     *
     * @return formatted message
     */
    public static String createListRequest() {
        return ProtocolCode.LIST.toString();
    }

    /**
     * Format a list message.
     *
     * @param users the list of online users
     * @return formatted message
     */
    public static String createListMessage(List<String> users) {
        StringBuilder sb = new StringBuilder();
        sb.append(ProtocolCode.LIST);

        for (String user : users) {
            if (user != null) {
                sb.append(ProtocolCode.SEPARATOR).append(user);
            }
        }

        return sb.toString();
    }

    // -- Gameplay ----

    /**
     * Format a queue request.
     *
     * @return formatted message
     */
    public static String createQueueRequest() {
        return ProtocolCode.QUEUE.toString();
    }

    /**
     * Format a new game message.
     *
     * @param player1 the starting player
     * @param player2 the second player
     * @return formatted message
     */
    public static String createNewGameMessage(String player1, String player2) {
        return String.format(FORMAT_LENGTH_5, ProtocolCode.NEWGAME,
                ProtocolCode.SEPARATOR, player1, ProtocolCode.SEPARATOR, player2);
    }

    /**
     * Format a move message. Validity checks of the arguments are meant to be done
     * in a ProtocolHandler.
     *
     * @param position the position index
     * @param rotation the rotation index
     * @return formatted message
     */
    public static String createMoveMessage(int position, int rotation) {
        return String.format("%s%s%d%s%d",
                ProtocolCode.MOVE, ProtocolCode.SEPARATOR, position,
                ProtocolCode.SEPARATOR, rotation);
    }

    /**
     * Format a victory game over message.
     *
     * @param winner the winner
     * @return formatted message
     */
    public static String createGameOverVictoryMessage(String winner) {
        return String.format(FORMAT_LENGTH_5,
                ProtocolCode.GAMEOVER, ProtocolCode.SEPARATOR,
                ProtocolCode.VICTORY, ProtocolCode.SEPARATOR, winner);
    }

    /**
     * Format a draw game over message.
     *
     * @return formatted message
     */
    public static String createGameOverDrawMessage() {
        return String.format(FORMAT_LENGTH_3,
                ProtocolCode.GAMEOVER, ProtocolCode.SEPARATOR, ProtocolCode.DRAW);
    }

    /**
     * Format a disconnected game over message.
     *
     * @param disconnectedUser the user that disconnected during a match
     * @return formatted message
     */
    public static String createGameOverDisconnectMessage(String disconnectedUser) {
        return String.format(FORMAT_LENGTH_5,
                ProtocolCode.GAMEOVER, ProtocolCode.SEPARATOR,
                ProtocolCode.DISCONNECT, ProtocolCode.SEPARATOR, disconnectedUser);
    }

    // -- Bonus ----

    /**
     * Format a chat message to be sent.
     *
     * @param message the message
     * @return formatted message
     */
    public static String createChatMessage(String message) {
        return String.format(FORMAT_LENGTH_3,
                ProtocolCode.CHAT, ProtocolCode.SEPARATOR, message);
    }

    /**
     * Format a chat message to be received by a recipient.
     *
     * @param recipient the recipient
     * @param message   the message
     * @return formatted message
     */
    public static String createChatMessageFor(String recipient, String message) {
        // CHAT~msg or CHAT~~~~~, needs to be cut at '|':
        // CHAT~|msg or CHAT~|~~~~
        String chat = message.substring(message.indexOf(ProtocolCode.SEPARATOR) + 1);
        return String.format(FORMAT_LENGTH_5,
                ProtocolCode.CHAT,
                ProtocolCode.SEPARATOR, recipient,
                ProtocolCode.SEPARATOR, chat);
    }

    /**
     * Extract just the message from a chat message.
     *
     * @param message the full message (including protocol code and sender)
     * @return the message alone
     */
    public static String decodeChatMessage(String message) {
        // CHAT~Bob~msg or CHAT~Bob~~~~~, needs to be cut at '|':
        // CHAT~Bob~|msg or CHAT~Bob~|~~~~
        String chat = message.substring(message.indexOf(ProtocolCode.SEPARATOR) + 1);
        chat = chat.substring(chat.indexOf(ProtocolCode.SEPARATOR) + 1);
        return chat;
    }

    /**
     * Format a whisper message to be received by a recipient.
     *
     * @param recipient the recipient
     * @param message   the message
     * @return formatted message
     */
    public static String createWhisperMessageFor(String recipient, String message) {
        return String.format(FORMAT_LENGTH_5, ProtocolCode.WHISPER,
                ProtocolCode.SEPARATOR, recipient,
                ProtocolCode.SEPARATOR, message);
    }

    /**
     * Format a whisper message to be sent by the sender.
     *
     * @param sender  the sender
     * @param message the message
     * @return formatted message
     */
    public static String createWhisperMessageFrom(String sender, String message) {
        // WHISPER~Bob~msg or WHISPER~Bob~~~~~, needs to be cut at '|':
        // WHISPER~Bob~|msg or WHISPER~Bob~|~~~~
        String whisper = message.substring(message.indexOf(ProtocolCode.SEPARATOR) + 1);
        whisper = whisper.substring(whisper.indexOf(ProtocolCode.SEPARATOR) + 1);
        return String.format(FORMAT_LENGTH_5,
                ProtocolCode.WHISPER,
                ProtocolCode.SEPARATOR, sender,
                ProtocolCode.SEPARATOR, whisper);
    }

    /**
     * Extract just the message from a whisper message.
     *
     * @param message the full message (including protocol code and sender)
     * @return the message alone
     */
    public static String decodeWhisperMessage(String message) {
        // WHISPER~Bob~msg or WHISPER~Bob~~~~~, needs to be cut at '|':
        // WHISPER~Bob~|msg or WHISPER~Bob~|~~~~
        String whisper = message.substring(message.indexOf(ProtocolCode.SEPARATOR) + 1);
        whisper = whisper.substring(whisper.indexOf(ProtocolCode.SEPARATOR) + 1);
        return whisper;
    }

    /**
     * Format a cannot whisper reply.
     *
     * @param recipient the recipient
     * @return formatted message
     */
    public static String createCannotWhisperReply(String recipient) {
        return String.format(FORMAT_LENGTH_3,
                ProtocolCode.CANNOTWHISPER, ProtocolCode.SEPARATOR, recipient);
    }

    /**
     * Format a rank request.
     *
     * @return formatted message
     */
    public static String createRankRequest() {
        return ProtocolCode.RANK.toString();
    }

    /**
     * Format a rank message for the players by their ELO stat.
     *
     * @param rankedPlayers the players on the leaderboard
     * @return formatted message
     */
    public static String createEloRankMessageFor(List<RankedPlayer> rankedPlayers) {
        StringBuilder sb = new StringBuilder();

        sb.append(ProtocolCode.RANK);

        for (RankedPlayer p : rankedPlayers) {
            sb.append(String.format(FORMAT_LENGTH_4,
                    ProtocolCode.SEPARATOR, p.getUsername(), ProtocolCode.SEPARATOR, p.getElo()));
        }

        return sb.toString();
    }
}
