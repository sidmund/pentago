package ss.pentago.file;

import ss.pentago.tui.skin.BoardGridCharacter;
import ss.pentago.tui.skin.BoardGridStyle;
import ss.pentago.tui.skin.BoardSkin;
import ss.pentago.tui.skin.MarbleStyle;
import ss.pentago.util.LoggingLevel;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Stores some settings.
 */
public class Config {

    private Config() {
    }

    //
    // -- EXTENSIONS --
    //

    public static final boolean CLIENT_CHAT_IMPLEMENTED = true;
    public static final boolean CLIENT_RANK_IMPLEMENTED = true;
    public static final boolean CLIENT_AUTH_IMPLEMENTED = false;
    public static final boolean CLIENT_CRYPT_IMPLEMENTED = false;

    private static boolean clientSupportsChat = true;
    private static boolean clientSupportsRank = true;
    private static boolean clientSupportsAuth = false;
    private static boolean clientSupportsCrypt = false;

    /**
     * @return whether chat is supported
     */
    public static boolean doesClientSupportChat() {
        return clientSupportsChat;
    }

    /**
     * @return whether auth is supported
     */
    public static boolean doesClientSupportAuth() {
        return clientSupportsAuth;
    }

    /**
     * @return whether crypt is supported
     */
    public static boolean doesClientSupportCrypt() {
        return clientSupportsCrypt;
    }

    /**
     * @return whether rank is supported
     */
    public static boolean doesClientSupportRank() {
        return clientSupportsRank;
    }

    /**
     * Enable/disable chat support.
     *
     * @param support whether to enable chat support
     */
    public static void setClientChatSupport(boolean support) {
        clientSupportsChat = support && CLIENT_CHAT_IMPLEMENTED;
    }

    /**
     * Enable/disable rank support.
     *
     * @param support whether to enable rank support
     */
    public static void setClientRankSupport(boolean support) {
        clientSupportsRank = support && CLIENT_RANK_IMPLEMENTED;
    }

    /**
     * Enable/disable auth support.
     *
     * @param support whether to enable auth support
     */
    public static void setClientAuthSupport(boolean support) {
        clientSupportsAuth = support && CLIENT_AUTH_IMPLEMENTED;
    }

    /**
     * Enable/disable crypt support.
     *
     * @param support whether to enable crypt support
     */
    public static void setClientCryptSupport(boolean support) {
        clientSupportsCrypt = support && CLIENT_CRYPT_IMPLEMENTED;
    }

    //
    // -- SERVER --
    //

    /**
     * A sorted Map containing the server profiles, identified by their name,
     * and holding the address value as a string in the format "hostname:port".
     */
    private static final Map<String, String> SERVER_PROFILES = new TreeMap<>();

    static {
        // Default servers
        addServerProfile("Local server", "localhost:55555");
    }

    /**
     * Adds a new server profile to the server profiles map, identified by name and address.
     *
     * @param name    the server name
     * @param address the server address, as "hostname:port"
     */
    //@ requires name != null && name != "" && address != null && name != "";
    public static void addServerProfile(String name, String address) {
        SERVER_PROFILES.put(name, address);
    }

    /**
     * Return a set of server profiles.
     *
     * @return the entry set of the server profiles map
     */
    //@ pure
    public static Set<Map.Entry<String, String>> getServerProfiles() {
        return SERVER_PROFILES.entrySet();
    }

    /**
     * Controls after how long of a delay to send quit to a client.
     * Measured in milliseconds.
     */
    private static long timeUntilDisconnect = 30000;

    /**
     * Set how long to wait until telling the client to disconnect.
     *
     * @param delay the delay in ms
     */
    //@ ensures timeUntilDisconnect == delay;
    public static void setTimeUntilDisconnect(long delay) {
        timeUntilDisconnect = delay;
    }

    /**
     * Get how long to wait until telling the client to disconnect.
     * 30 seconds by default.
     *
     * @return the delay in ms
     */
    //@ pure
    public static long getTimeUntilDisconnect() {
        return timeUntilDisconnect;
    }

    /**
     * How often to send a ping to connected clients.
     * Measured in milliseconds.
     */
    private static long pingInterval = 15000;

    /**
     * Set how often to send a ping to connected clients.
     *
     * @param interval the interval in ms
     */
    //@ ensures pingInterval == interval;
    public static void setPingInterval(long interval) {
        pingInterval = interval;
    }

    /**
     * Get how often to send a ping to connected clients.
     * 5 seconds by default.
     *
     * @return the interval in ms
     */
    //@ pure
    public static long getPingInterval() {
        return pingInterval;
    }

    /**
     * How often the GameManager updates.
     * Measured in milliseconds.
     */
    private static long gameManagerTickRate = 1;

    /**
     * Set how often the GameManager updates.
     *
     * @param rate the interval in ms
     */
    //@ ensures gameManagerTickRate == rate;
    public static void setGameManagerTickRate(long rate) {
        gameManagerTickRate = rate;
    }

    /**
     * Get how often the GameManager updates.
     * 1 ms by default.
     *
     * @return the interval in ms
     */
    //@ pure
    public static long getGameManagerTickRate() {
        return gameManagerTickRate;
    }

    //
    // -- BOARD SKIN --
    //

    /**
     * The BoardSkin is used by the {@code TextDisplay} to render the {@code Board}.
     */
    public static final BoardSkin BOARD_SKIN = new BoardSkin(
            BoardGridStyle.QUADRANT,
            BoardGridCharacter.DOT, BoardGridCharacter.COMMA,
            MarbleStyle.LETTERS, false);

    //
    // -- AI --
    //

    /**
     * Controls how much to delay the AI's moves in single player.
     * Measured in milliseconds.
     */
    private static long responseDelaySinglePlayer = 1000;

    /**
     * Set how much to delay the AI's moves in single player.
     *
     * @param delay the delay in ms
     */
    //@ ensures responseDelaySinglePlayer == delay;
    public static void setResponseDelaySinglePlayer(long delay) {
        responseDelaySinglePlayer = delay;
    }

    /**
     * Get how much to delay the AI's moves in single player.
     *
     * @return the delay in ms
     */
    //@ pure
    public static long getResponseDelaySinglePlayer() {
        return responseDelaySinglePlayer;
    }

    /**
     * Controls how much to delay the AI's commands/moves in multiplayer.
     * Measured in milliseconds.
     */
    private static long responseDelayMultiPlayer = 1000;

    /**
     * Set how much to delay the AI's commands/moves in multiplayer.
     *
     * @param delay the delay in ms
     */
    //@ ensures responseDelayMultiPlayer == delay;
    public static void setResponseDelayMultiPlayer(long delay) {
        responseDelayMultiPlayer = delay;
    }

    /**
     * Get how much to delay the AI's commands/moves in multiplayer.
     *
     * @return the delay in ms
     */
    //@ pure
    public static long getResponseDelayMultiPlayer() {
        return responseDelayMultiPlayer;
    }

    //
    // -- LOGGER --
    //

    private static LoggingLevel loggingLevel = LoggingLevel.IGNORE;

    /**
     * Set the logging level of the Logger.
     *
     * @param level the logging level
     */
    //@ ensures loggingLevel == level;
    public static void setLoggingLevel(LoggingLevel level) {
        loggingLevel = level;
    }

    /**
     * Get the logging level of the Logger.
     *
     * @return the logging level
     */
    //@ pure
    public static LoggingLevel getLoggingLevel() {
        return loggingLevel;
    }

}
