package ss.pentago.network;

import ss.pentago.model.player.HumanPlayer;
import ss.pentago.model.player.Player;
import ss.pentago.network.client.ClientListener;
import ss.pentago.network.client.OfflineClient;
import ss.pentago.network.client.OnlineClient;
import ss.pentago.network.protocol.ClientProtocolHandler;
import ss.pentago.network.server.Server;
import ss.pentago.network.server.ServerInputHandler;
import ss.pentago.tui.BotInputHandler;
import ss.pentago.tui.OfflineTextInputHandler;
import ss.pentago.tui.OnlineTextInputHandler;
import ss.pentago.tui.TextDisplay;

/**
 * Factory class to generate all Client/Server related objects.
 */
public class NetworkFactory {

    private NetworkFactory() {
    }

    // -- Client Listeners ----

    /**
     * Create a new {@code TextDisplay}, a TUI-based ClientListener
     * which displays text to System.out.
     *
     * @return a new TextDisplay
     */
    private static ClientListener makeTextDisplay() {
        return new TextDisplay();
    }

    // -- Clients ----

    /**
     * Create a new {@code OnlineClient} with specified {@code Player}.
     * The OnlineClient allows connecting to a Server to play games against
     * other OnlineClients.
     *
     * @param player the player to use for setting the username and to call its hint AI
     * @return a new TUI-integrated OnlineClient
     */
    //@ requires player != null;
    public static OnlineClient makeOnlineClientWithTUI(Player player) {

        // create the client, which will use the player to set the username
        OnlineClient client = new OnlineClient(player);

        // setup client listeners and handlers
        client.setProtocolHandler(new ClientProtocolHandler(client));
        client.addListener(makeTextDisplay());
        if (player instanceof HumanPlayer) {
            // Human input
            client.setInputHandler(new OnlineTextInputHandler(client));
        } else {
            // Automated (AI) input
            client.setInputHandler(new BotInputHandler(client));
        }

        return client;
    }

    /**
     * Create a new {@code OfflineClient} with specified {@code Player} objects.
     * The OfflineClient runs a local game between two human or AI players.
     *
     * @param player1 the first player
     * @param player2 the second player
     * @param shuffle whether to use a random starting order
     * @return a new TUI-integrated OfflineClient
     */
    //@ requires player1 != null && player2 != null;
    public static OfflineClient makeOfflineClientWithTUI(
            Player player1, Player player2, boolean shuffle) {

        OfflineClient client = new OfflineClient(player1, player2, shuffle);

        // setup client listeners and handlers
        client.addListener(makeTextDisplay());
        client.setInputHandler(new OfflineTextInputHandler(client));

        return client;
    }

    // -- Servers ----

    /**
     * Create a new {@code Server}.
     *
     * @return a new TUI-integrated Server
     */
    public static Server makeServerWithTUI() {
        Server server = new Server();

        // Create the TUI input handler to handle user input and run the server
        server.setInputHandler(new ServerInputHandler(server));

        return server;
    }
}