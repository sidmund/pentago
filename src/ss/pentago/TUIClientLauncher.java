package ss.pentago;

import ss.pentago.file.FileHandler;
import ss.pentago.model.player.Player;
import ss.pentago.network.NetworkFactory;
import ss.pentago.network.client.OnlineClient;
import ss.pentago.tui.menu.TUIMenus;

import java.net.InetAddress;
import java.net.UnknownHostException;

/**
 * TUIClientLauncher acts as the entry point of the client application.
 * It handles setting up the server connection (or starts an offline session),
 * and launching the actual client which handles user input and server communication.
 */
public class TUIClientLauncher {

    /**
     * Configures the Client to run offline.
     *
     * @param player1 the first player
     * @param player2 the second player
     * @param shuffle whether to shuffle the players at the start of the game
     */
    //@ requires player1 != null && player2 != null;
    public static void playOffline(Player player1, Player player2, boolean shuffle) {
        NetworkFactory.makeOfflineClientWithTUI(player1, player2, shuffle).start();
    }

    /**
     * Configures the Client to run online.
     *
     * @param player   the player
     * @param hostname the server address
     * @param port     the port number, between 0 and 65535 (inclusive)
     * @return {@code false} when connected was made (games played, etc)
     * and the client successfully returned from the server and should go back to the main menu<br>
     * {@code true} when the client couldn't connect and should go back to the server menu
     */
    //@ requires player != null && hostname != null && port >= 0 && port < 65536;
    public static boolean playOnline(Player player, String hostname, int port) {
        OnlineClient client = NetworkFactory.makeOnlineClientWithTUI(player);

        // Establish connection
        boolean connected = false;
        while (!connected) {
            try {
                if (client.connect(InetAddress.getByName(hostname), port)) {
                    connected = true;
                } else {
                    client.inform("Server seems to be down.");
                    // we don't want to be stuck in an 'infinite' loop,
                    // just waiting for a connection, so go back to server menu
                    // to select a different profile
                    return true;
                }
            } catch (UnknownHostException e) {
                client.inform("Unknown host. Try again.");
            }
        }

        client.start();

        return false;
    }

    public static void main(String[] args) {
        FileHandler.loadConfig();
        TUIMenus.showMainMenu();
    }
}
