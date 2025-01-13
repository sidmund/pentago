package ss.pentago.network.server;

import ss.pentago.network.server.rank.RankedPlayer;
import ss.pentago.tui.Colors;
import ss.pentago.util.Logger;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;

/**
 * Just runs in a thread to listen to commands from System.in
 * and do something to the Server based on it, while the Server
 * itself only listens to new connections from Clients.
 */
public class ServerInputHandler implements Runnable {

    //@ private invariant server != null && inputReader != null;

    private final BufferedReader inputReader;

    private final Server server;

    private Thread thread;
    private boolean running;

    /**
     * Create a new ServerInputHandler that listens to input from System.in,
     * and tells the Server what to do with it.
     * @param server the server
     */
    //@ requires server != null;
    //@ ensures this.server == server && inputReader != null;
    public ServerInputHandler(Server server) {
        this.server = server;

        inputReader = new BufferedReader(new InputStreamReader(System.in));
    }

    /**
     * Start running this ServerInputHandler.
     */
    public void start() {
        Logger.info(this, "starting thread...");
        running = true;
        thread = new Thread(this, "ServerInputHandler");
        thread.start();
    }

    /**
     * Stop this ServerInputHandler.
     */
    public void stop() {
        running = false;
        Logger.info(this, "trying to stop...");

        // wait for thread to stop
        try {
            thread.join();
            Logger.info(this, "thread is joined: " + !thread.isAlive());
        } catch (InterruptedException e) {
            // restore interrupted status
            thread.interrupt();
            Logger.info(this, "thread interrupted");
        }
    }

    /**
     * This is the what is continually running in the TUI.
     */
    @Override
    public void run() {
        // Continually obtain user input
        while (running) {
            try {
                while (inputReader.ready()) {
                    String input = inputReader.readLine();

                    if (!input.isBlank()) {
                        switch (input.toLowerCase()) {
                            case "list":
                                System.out.println(getList());
                                break;
                            case "quit":
                                running = false;
                                break;
                            case "help":
                                System.out.println(getHelpMessage());
                                break;
                            case "rank":
                                showRank();
                                break;
                            case "status":
                                System.out.println(getStatus());
                                break;
                            default:
                                System.out.printf("Unknown command: %s%n", input);
                                break;
                        }
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        server.stop();
    }

    /**
     * @return list of all online users as a String
     */
    private String getList() {
        StringBuilder sb = new StringBuilder();

        sb.append(String.format("%s %s %s%n", "-".repeat(4), "List", "-".repeat(68)));
        for (String user : server.getUserList()) {
            sb.append(String.format(" %-76s%n", user));
        }
        sb.append("-".repeat(78));

        return sb.toString();
    }

    /**
     * Show how many players are online, and how many matches have been played.
     *
     * @return server status as String
     */
    private String getStatus() {
        return "" +
                "---- STATUS-------------------------------------------------------------------\n" +
                String.format("    %d players online%n",
                        server.getClientHandlers().size()) +
                String.format("    %d matches played%n",
                        server.getGameManager().getNrMatchesPlayed()) +
                "------------------------------------------------------------------------------";
    }

    /**
     * @return the help message
     */
    private String getHelpMessage() {
        return "" +
                "---- ALLOWED COMMANDS --------------------------------------------------------\n" +
                " status                   show current statistics\n" +
                " list                     show all online users\n" +
                " rank                     show the full leaderboard\n" +
                " help                     show this help menu\n" +
                " quit                     quit the application\n" +
                "------------------------------------------------------------------------------";
    }

    /**
     * Show full leaderboard with all player stats.
     */
    private void showRank() {
        if (!server.isRankEnabled()) {
            System.out.println("Rank is not enabled");
            return;
        }

        List<RankedPlayer> rankings = server.getEloRankings();

        StringBuilder sb = new StringBuilder();

        sb.append(String.format("%n| %-30s | %-12s | %-8s | %-10s | %-13s |%n",
                "username", "ELO rating", "win rate", "#games won", "#games played"));
        sb.append(String.format("| %s | %s | %s | %s | %s |%n",
                "-".repeat(30), "-".repeat(12), "-".repeat(8), "-".repeat(10), "-".repeat(13)));

        int max = 20;
        for (RankedPlayer player : rankings) {
            sb.append(String.format("| %s%-30s%s | %s%-12d%s | %-8d | %-10d | %-13d |%n",
                    Colors.YELLOW, player.getUsername(), Colors.RESET,
                    Colors.YELLOW, player.getElo(), Colors.RESET,
                    player.getWinRate(), player.getTotalGamesWon(), player.getTotalGamesPlayed()));

            max--;
            if (max <= 0) {
                break;
            }
        }

        System.out.println(sb);
    }

    @Override
    public String toString() {
        return "ServerInputHandler";
    }
}
