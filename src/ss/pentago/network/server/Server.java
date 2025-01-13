package ss.pentago.network.server;

import ss.pentago.file.Config;
import ss.pentago.network.protocol.ServerProtocolHandler;
import ss.pentago.network.server.rank.Leaderboard;
import ss.pentago.network.server.rank.RankedPlayer;
import ss.pentago.util.Logger;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

/**
 * Server provides a platform for Clients to connect to and play games together.
 * This class manages the connections with Clients through ClientHandlers,
 * manages their games through the GameManager,
 * and the connectivity through PingPong.
 */
public class Server implements Runnable {

    public static final String SERVER_DESCRIPTION = "Custom Server";

    protected ServerSocket ss;
    protected ServerInputHandler inputHandler;

    protected final Map<ClientHandler, Long> clientHandlers;
    protected GameManager gameManager;
    protected final Leaderboard leaderboard;
    protected PingPong pinger;

    private boolean isChatEnabled = false;
    private boolean isRankEnabled = false;

    /**
     * Create a new Server. This initializes the GameManager and Leaderboard.
     */
    /*@
        ensures clientHandlers != null && clientHandlers.isEmpty();
        ensures gameManager != null && leaderboard != null;
    */
    public Server() {
        this.clientHandlers = new HashMap<>();
        this.gameManager = new GameManager(this);
        leaderboard = new Leaderboard();
    }

    /**
     * Tries to create a server socket bound to the specified port.
     * The intended use is to call {@link #start()} after this function has returned true.
     * This will then run this server in a thread.
     *
     * @param port the port to make the Server listen to
     * @return whether server could be started at port (the socket has been created)
     */
    //@ requires port >= 0 && port < 65536;
    public boolean createSocketAt(int port) {
        try {
            ss = new ServerSocket(port);
            System.out.println("Server started at port " + getPort());
            return true;
        } catch (IOException e) {
            Logger.error(Server.class.getSimpleName(), "could not start at port " + port);
            return false;
        }
    }

    /**
     * Starts this Server in a new thread, and start the GameManager in a new thread.
     */
    public void start() {
        Logger.info(this, "starting thread...");
        Thread thread = new Thread(this, "Server");
        thread.start();

        gameManager = new GameManager(this);
        Thread gmThread = new Thread(gameManager);

        pinger = new PingPong(this);
        Thread ping = new Thread(pinger, "PingPong");

        gmThread.start();
        ping.start();

        // wait for it to stop
        try {
            if (thread.isAlive()) {
                thread.join();
            }
            if (gmThread.isAlive()) {
                gmThread.join();
            }
            if (ping.isAlive()) {
                ping.join();
            }
            Logger.info(this, "thread is joined: " + !thread.isAlive());
            Logger.info(this, "GameManager thread is joined: " + !gmThread.isAlive());
            Logger.info(this, "PingPong thread is joined: " + !ping.isAlive());
        } catch (InterruptedException e) {
            // restore interrupted status
            thread.interrupt();
            gmThread.interrupt();
            ping.interrupt();
            Logger.info(this, "thread interrupted");
            Logger.info(this, "GameManager thread interrupted");
            Logger.info(this, "PingPong thread interrupted");
        }
    }

    /**
     * While running, just wait for client to connect, and spawn a ClientHandler for them.
     */
    @Override
    public void run() {
        boolean running = true;

        if (inputHandler != null) {
            inputHandler.start();
        }

        while (running) {
            try {
                Logger.info(this, "waiting for connections...");
                Socket socket = ss.accept();
                Logger.info(this, "client accepted");

                ClientHandler ch = new ClientHandler(socket, this);
                ch.setProtocolHandler(new ServerProtocolHandler(ch));
                addClientHandler(ch);
                ch.start();
            } catch (IOException e) {
                Logger.info(this, "server socket closed");
                running = false;
            }
        }

        if (inputHandler != null) {
            inputHandler.stop();
        }

        stop();
    }

    /**
     * Returns the port of the server.
     *
     * @return port
     */
    public int getPort() {
        return ss.getLocalPort();
    }

    /**
     * Sends a disconnections request to all ClientHandlers and
     * stops the server by closing the ServerSocket.
     */
    public void stop() {
        if (gameManager != null) {
            gameManager.stop();
        }
        if (pinger != null) {
            pinger.stop();
        }

        for (ClientHandler ch : clientHandlers.keySet()) {
            ch.getProtocolHandler().sendQuit();
            ch.closeSocket();
        }

        try {
            if (!ss.isClosed()) {
                ss.close();
            }
        } catch (IOException e) {
            Logger.info(this, "I/O error while closing socket");
        }

        clientHandlers.clear();
    }

    /**
     * Sends out a ping to all logged in Clients.
     *
     * @return false when the server socket is closed to signal that PingPong should stop,
     * true otherwise
     */
    public synchronized boolean pingHandlers() {
        if (ss.isClosed()) {
            return false;
        }

        for (ClientHandler ch : clientHandlers.keySet()) {
            if (ch.isLoggedIn()) {
                ch.getProtocolHandler().sendPing();
            }
        }

        return true;
    }

    /**
     * Reset the disconnection timer for the specified ClientHandler.
     * This method should be invoked when a ClientHandler receives a pong from the Client.
     * If the time elapsed since the disconnection timer got set is bigger than
     * the disconnection timeout, the ClientHandler will close the socket,
     * effectively kicking the Client.
     * If the time elapsed is less than the timeout, the timer is reset.
     *
     * @param ch the client handler
     */
    public synchronized void resetDisconnectionTime(ClientHandler ch) {
        for (Map.Entry<ClientHandler, Long> entry : clientHandlers.entrySet()) {
            if (entry.getKey() == ch && ch.isLoggedIn()) {

                long elapsed = System.currentTimeMillis() - entry.getValue();
                if (elapsed > Config.getTimeUntilDisconnect()) {
                    ch.closeSocket();

                } else {
                    entry.setValue(System.currentTimeMillis());
                }

                break;
            }
        }
    }

    /**
     * For each connected ClientHandler check how much time has elapsed since it's timer was set.
     * If this is less than the disconnection timeout, the ClientHandler in fact received
     * a pong from its Client, and the connection is still up.
     * However, if the time is more than the disconnection timeout, the associated ClientHandler
     * closes the socket and consequently the Client gets kicked from the server.
     *
     * @return false when the server socket is closed to signal that PingPong should stop,
     * true otherwise
     */
    public synchronized boolean checkConnections() {
        if (ss.isClosed()) {
            return false;
        }

        long now = System.currentTimeMillis();

        for (Map.Entry<ClientHandler, Long> entry : clientHandlers.entrySet()) {

            long elapsed = now - entry.getValue();
            if (entry.getKey().isLoggedIn()
                    && elapsed > Config.getTimeUntilDisconnect()) {
                entry.getKey().closeSocket();
            }
        }

        return true;
    }

    /**
     * Send a message from the server to all clients except the sender.
     *
     * @param sender  the ClientHandler who sent the message
     * @param message the protocol encoded message
     */
    public synchronized void sendChat(ClientHandler sender, String message) {
        if (isChatEnabled) {
            for (ClientHandler clientHandler : clientHandlers.keySet()) {
                if (clientHandler != sender) {
                    clientHandler.send(message);
                }
            }
        }
    }

    /**
     * Send a private message to the Client with the specified name.
     *
     * @param sender    the sender
     * @param recipient the user to sent the private message to
     * @param message   the protocol encoded message
     */
    public synchronized void sendWhisper(ClientHandler sender, String recipient, String message) {
        if (isChatEnabled) {
            boolean whisperSent = false;
            for (ClientHandler clientHandler : clientHandlers.keySet()) {
                if (clientHandler.getUsername().equals(recipient)) {
                    clientHandler.send(message);
                    whisperSent = true;
                    break;
                }
            }

            if (!whisperSent) {
                sender.getProtocolHandler().sendCannotWhisper(recipient);
            }
        }
    }

    /**
     * Checks if any of the currently connected clients has the specified username.
     *
     * @param username check username
     * @return false when username is available, true if not
     */
    /*@ requires username != null;
     @ ensures \result && getUserList().contains(username) ||
               !\result && !getUserList().contains(username);
    */
    public synchronized boolean isUsernamePresent(String username) {
        for (ClientHandler ch : clientHandlers.keySet()) {
            String user = ch.getUsername();
            if (user == null) {
                continue;
            }
            if (user.equals(username)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Make request to game manager to add client into queue for matchmaking.
     *
     * @param clientHandler the client
     * @return queue or dequeue
     */
    public synchronized boolean queuePlayer(ClientHandler clientHandler) {
        return gameManager.queue(clientHandler);
    }

    /**
     * Get list of user connected to server.
     *
     * @return list of username
     */
    /*@
        ensures (\forall ClientHandler ch; clientHandlers.containsKey(ch);
                                      \result.contains(ch.getUsername()));
    */
    //@ pure
    public synchronized List<String> getUserList() {
        List<String> users = new ArrayList<>();
        for (ClientHandler ch : clientHandlers.keySet()) {
            users.add(ch.getUsername());
        }
        return users;
    }

    /**
     * @return the leaderboard's ELO rankings
     */
    public List<RankedPlayer> getEloRankings() {
        return leaderboard.getRankingSortedByElo();
    }

    /**
     * Tell the leaderboard to update the rankings.
     *
     * @param winner the winner
     * @param loser  the loser
     * @param isDraw whether it was a draw
     */
    public void updateMatch(String winner, String loser, boolean isDraw) {
        leaderboard.updateRankings(winner, loser, isDraw);
    }

    /**
     * @param clientHandler the client to add
     */
    public synchronized void addClientHandler(ClientHandler clientHandler) {
        clientHandlers.put(clientHandler, System.currentTimeMillis());
        System.out.printf("Server connections active: %d%n", clientHandlers.size());
    }

    /**
     * @param clientHandler the client to remove
     */
    public synchronized void removeClientHandler(ClientHandler clientHandler) {
        clientHandlers.remove(clientHandler);
        System.out.printf("Server connections active: %d%n", clientHandlers.size());
    }

    /**
     * Sets the ServerInputHandler associated with this Server.
     * The ServerInputHandler forwards user input to this Server.
     *
     * @param inputHandler the inputhandler
     */
    public void setInputHandler(ServerInputHandler inputHandler) {
        this.inputHandler = inputHandler;
    }

    /**
     * @return game manager
     */
    public GameManager getGameManager() {
        return gameManager;
    }

    public synchronized Map<ClientHandler, Long> getClientHandlers() {
        return clientHandlers;
    }

    public void enableChat() {
        isChatEnabled = isChatSupported();
    }

    public void enableRank() {
        isRankEnabled = isRankSupported();
    }

    /**
     * Crypt cannot be enabled, because it is not supported.
     */
    public void enableCrypt() {
//        isCryptEnabled = isCryptSupported();
    }

    /**
     * Auth cannot be enabled, because it is not supported.
     */
    public void enableAuth() {
//        isAuthEnabled = isAuthSupported();
    }

    /**
     * @return whether this server supports rank
     */
    public boolean isRankSupported() {
        return true;
    }

    /**
     * @return whether this server supports crypt
     */
    public boolean isCryptSupported() {
        return false;
    }

    /**
     * @return whether this server supports chat
     */
    public boolean isChatSupported() {
        return true;
    }

    /**
     * @return whether this server supports auth
     */
    public boolean isAuthSupported() {
        return false;
    }

    /**
     * @return isRankEnabled
     */
    public boolean isRankEnabled() {
        return isRankEnabled;
    }

    @Override
    public String toString() {
        return "Server:" + getPort();
    }
}
