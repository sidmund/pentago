package ss.pentago.network.protocol;

/**
 * An Enum to store all possible (supported) client-server protocol codes.
 * This is meant to simplify checking and to standardize communication handling.
 */
public enum ProtocolCode {

    // --------------------------
    //  INITIALIZATION
    // --------------------------

    /**
     * Defines a client connection initialization request, or a response to it.
     */
    HELLO,

    /**
     * Defines a user login request, or response.
     */
    LOGIN,

    /**
     * Defines a reply when a login failed because the username was already present on the server.
     */
    ALREADYLOGGEDIN,

    // --------------------------
    //  GENERAL
    // --------------------------

    /**
     * Defines an error message reply.
     */
    ERROR,

    /**
     * Defines a command to determine connectivity. The other party must return PONG.
     */
    PING,

    /**
     * This reply should be sent in response to PING.
     */
    PONG,

    /**
     * Defines a query to get online users, or a reply containing a list of users.
     */
    LIST,

    // --------------------------
    //  GAMEPLAY
    // --------------------------

    /**
     * Defines a command to enter or leave the queue of waiting players.
     */
    QUEUE,

    /**
     * Defines a command to start a new game.
     */
    NEWGAME,

    /**
     * Defines a command to send or confirm a move.
     */
    MOVE,

    /**
     * Defines a reply that signifies a game over event.
     */
    GAMEOVER,

    /**
     * Defines a draw as the reason for a GAMEOVER.
     */
    DRAW,

    /**
     * Defines disconnection as the reason for a GAMEOVER.
     */
    DISCONNECT,

    /**
     * Defines a victory as the reason for a GAMEOVER.
     */
    VICTORY,

    /**
     * Defines a request to disconnect.
     */
    QUIT,

    // --------------------------
    //  BONUS
    // --------------------------

    // CRYPT

    /**
     * Defines that the sender supports encryption.
     */
    CRYPT,

    /**
     * Defines a request or reply to initiate encryption.
     */
    ENCRYPT,

    // AUTH

    /**
     * Defines that the sender supports authentication.
     */
    AUTH,

    /**
     * Defines an authentication challenge.
     */
    CHALLENGE,

    /**
     * Defines a reply when client signature verification fails.
     */
    WRONGKEY,

    // RANK

    /**
     * Defines that the sender supports ranking.
     * It is also used to request the server's player rankings.
     */
    RANK,

    // CHAT

    /**
     * Defines that the sender supports chatting.
     * It is also used to send a chat message to all other connected clients,
     * or to tell a client that it has a chat message.
     */
    CHAT,

    /**
     * Defines a command to send a private chat message to another client,
     * or to tell a client that is has a whisper message.
     */
    WHISPER,

    /**
     * Defines a reply when the recipient of a whisper is unknown or does not support CHAT.
     */
    CANNOTWHISPER,

    // --------------------------
    //  INVALID
    // --------------------------

    /**
     * Defines an invalid operation.
     */
    INVALID;

    /**
     * The separator used to format protocol codes.
     */
    public static final String SEPARATOR = "~";

    /**
     * Parses a string into a ProtocolCode.
     *
     * @param s the string
     * @return the associated code
     */
    /*@
        requires s != null;
        ensures (\exists int i; i >= 0 && i < ProtocolCode.values().length;
                    ProtocolCode.values()[i] == \result);
    */
    public static ProtocolCode parseString(String s) {
        for (ProtocolCode code : ProtocolCode.values()) {
            if (code.toString().equals(s.toUpperCase())) {
                return code;
            }
        }
        return INVALID;
    }
}
