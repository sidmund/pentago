package ss.pentago.network.server;

import ss.pentago.file.Config;
import ss.pentago.util.Logger;

/**
 * ConnectionTimer needs to determine how long it takes for a user to be logged in,
 * because if a user stays idle, valuable server resources are still taken up.
 * In such a case this Timer makes sure that the user is kicked.
 */
public class ConnectionTimer implements Runnable {

    //@ private invariant ch != null;

    private final ClientHandler ch;

    /**
     * Create a new ConnectionTimer, which kicks the user when the time it takes
     * them to enter their login information exceeds to possible amount.
     * If the user does login before that, this timer automatically stops.
     *
     * @param ch the client handler, to tell it to close the connection
     */
    //@ ensures this.ch == ch;
    public ConnectionTimer(ClientHandler ch) {
        this.ch = ch;
    }

    /**
     * Start this Timer in a new thread.
     */
    public void start() {
        Logger.info(this, "starting thread...");

        Thread thread = new Thread(this, "Connection Timer");
        thread.start();

        // wait for it to stop (when client logs in or when ch is destroyed)
        try {
            if (thread.isAlive()) {
                thread.join();
            }
            Logger.info(this, "thread is joined: %s", !thread.isAlive());
        } catch (InterruptedException e) {
            thread.interrupt();
            Logger.info(this, "thread is joined: %s", !thread.isAlive());
        }
    }

    /**
     * While running, compute the elapsed time since this timer was created.
     * If this exceeds the configured disconnection timeout, tell the ClientHandler
     * to end the connection.
     * If the user logs in before timer expiry, this timer will automatically end.
     */
    @Override
    public void run() {
        long startTime = System.currentTimeMillis();

        while (!ch.isLoggedIn()) {
            long elapsed = System.currentTimeMillis() - startTime;
            if (elapsed > Config.getTimeUntilDisconnect()) {
                Logger.info(this, "kicking client due to inactivity");
                ch.closeSocket();
                break;
            }
        }
    }

    @Override
    public String toString() {
        return "ConnectionTimer:" + ch.getUsername();
    }
}
