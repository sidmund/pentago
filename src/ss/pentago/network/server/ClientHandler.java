package ss.pentago.network.server;

import ss.pentago.network.protocol.ProtocolHandler;
import ss.pentago.network.protocol.ServerProtocolHandler;
import ss.pentago.util.Logger;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

/**
 * ClientHandler acts as the Server's representative in dealing with a connected Client.
 * It receives messages from the Client and can send messages to the Client,
 * for this purpose it tracks some gameplay variables.
 * The interpretation of these messages however, is largely handled by the ServerProtocolHandler.
 */
public class ClientHandler implements Runnable {

    private final Socket socket;
    private final PrintWriter socketOut;
    private final BufferedReader socketIn;

    private final Server server;
    private ServerProtocolHandler protocol;

    // Track game play status
    private boolean isLoggedIn;
    private boolean isInGame;
    private boolean canMove;

    private Thread thread;
    private boolean running;

    /**
     * The username of the Client, if null, the client has not logged in yet.
     */
    private String username;

    /**
     * Create a new ClientHandler. This manages a connection with a Client.
     *
     * @param socket the socket
     * @param server the server
     * @throws IOException when the socket closed
     */
    public ClientHandler(Socket socket, Server server) throws IOException {
        this.socket = socket;
        this.server = server;
        this.socketOut = new PrintWriter(socket.getOutputStream(), true);
        this.socketIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));

        isLoggedIn = false;
        isInGame = false;
    }

    /**
     * Continually receive client messages.
     */
    @Override
    public void run() {
        reset();

        running = true;

        while (running) {
            try {
                String msg = socketIn.readLine();

                if (msg == null) {
                    running = false;
                } else {
                    protocol.receive(msg);
                }
            } catch (IOException e) {
                // connection closed
                running = false;
            }
        }

        protocol.sendQuit();

        stop();
    }

    /**
     * Sends specified message to the socket output stream.
     * This method should be called by a ServerProtocolHandler
     * after formatting the message accordingly.
     * When a writing error occurs, the socket is closed.
     *
     * @param message the message
     * @return false when a writing error occurred, true otherwise
     */
    public boolean send(String message) {
        if (!socket.isClosed()) {
            if (message == null) {
                return false;
            }

            socketOut.println(message);

            if (socketOut.checkError()) {
                closeSocket();
                return false;
            } else {
                return true;
            }
        } else {
            Logger.info(this, "socket closed, can't send message");
            running = false;
            stop();
            return false;
        }
    }

    /**
     * Runs this ClientHandler in a thread.
     */
    public void start() {
        Logger.info(this, "starting %s thread for...", getUsername());

        thread = new Thread(this);
        thread.start();

        new ConnectionTimer(this).start();
    }

    /**
     * End the match being played if present, remove this ClientHandler from the
     * server, close the socket, and wait for the thread to end.
     */
    private void stop() {
        try {
            if (isInGame) {
                server.getGameManager().endMatchIfPresent(this);
            }
            server.removeClientHandler(this);
            closeSocket();

            if (thread.isAlive()) {
                thread.interrupt();
                thread.join();
            }
            Logger.info(this, "%s thread is joined: %s",
                    getUsername(), !thread.isAlive());
        } catch (InterruptedException e) {
            thread.interrupt();
            Logger.info(this, "%s thread is joined: %s",
                    getUsername(), !thread.isAlive());
        }
    }

    /**
     * Close the socket, thereby disconnecting the Client.
     */
    public void closeSocket() {
        try {
            if (!socket.isClosed()) {
                socket.close();
            }
        } catch (IOException e) {
            Logger.info(this,
                    "trying to close socket, this %s thread was blocked in I/O", getUsername());
        }
    }

    /**
     * Disconnect the Client by:
     * (a) clearing their associated matches,
     * (b) sending a quit message through the ProtocolHandler, and
     * (c) closing the socket.
     */
    public void disconnect() {
        if (isInGame) {
            server.getGameManager().endMatchIfPresent(this);
        }
        protocol.sendQuit();
        closeSocket();
        stop();
    }

    public void setProtocolHandler(ProtocolHandler ph) {
        this.protocol = (ServerProtocolHandler) ph;
    }

    //@ pure
    public ServerProtocolHandler getProtocolHandler() {
        return protocol;
    }

    /**
     * Set username to the client handler.
     *
     * @param username the user name
     */
    //@ ensures this.username == username;
    public void setUsername(String username) {
        this.username = username;
    }

    //@ pure
    public String getUsername() {
        return username;
    }

    /**
     * Queue/dequeue player into the matchMaking system.
     *
     * @return true for enter queue false for dequeue
     */
    public boolean queue() {
        return server.queuePlayer(this);
    }

    public void reset() {
        isInGame = false;
        canMove = false;
    }

    //@ pure
    public boolean isInGame() {
        return isInGame;
    }

    //@ pure
    public boolean canMove() {
        return canMove;
    }

    //@ pure
    public Server getServer() {
        return server;
    }

    public void setInGame(boolean inGame) {
        this.isInGame = inGame;
    }

    public void setCanMove(boolean canMove) {
        this.canMove = canMove;
    }

    //@ ensures isLoggedIn();
    public synchronized void login() {
        isLoggedIn = true;
    }

    /**
     * @return isLoggedIn
     */
    //@ pure
    public synchronized boolean isLoggedIn() {
        return isLoggedIn;
    }

    @Override
    public String toString() {
        return "ClientHandler:" + getUsername();
    }
}
