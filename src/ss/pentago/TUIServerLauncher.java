package ss.pentago;

import ss.pentago.file.FileHandler;
import ss.pentago.network.NetworkFactory;
import ss.pentago.network.server.Server;
import ss.pentago.tui.menu.TUIMenus;

import java.util.Scanner;

/**
 * Runs a TUI server application.
 */
public class TUIServerLauncher {

    /**
     * Setup and run a server at a port.
     */
    private static void runServer() {
        Server server = NetworkFactory.makeServerWithTUI();

        Scanner scanner = new Scanner(System.in);

        int port;
        do {
            port = TUIMenus.showServerPortMenu(scanner);

            if (port == -1) {
                return;
            }
        }
        while (!server.createSocketAt(port));

        server.start();
    }

    public static void main(String[] args) {
        FileHandler.loadConfig();
        runServer();
    }
}
