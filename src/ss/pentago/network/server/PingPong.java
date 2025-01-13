package ss.pentago.network.server;

import ss.pentago.file.Config;
import ss.pentago.util.Logger;

/**
 * PingPong periodically pings all connected clients, and requests the Server
 * to check how many ClientHandler objects are still active.
 */
public class PingPong implements Runnable {

    //@ private invariant server != null;

    private final Server server;

    private boolean running;

    /**
     * Creates a new Ping, which periodically sends ping messages to the Client.
     * Additionally it sends a request everytime the disconnection timer times out
     * to the server to check the connectivity of all ClientHandler objects.
     *
     * @param server the server
     */
    //@ ensures this.server == server;
    public PingPong(Server server) {
        this.server = server;
    }

    /**
     * While running, ping all ClientHandlers at a specified interval.
     * Periodically tell the Server to check how many ClientHandlers didn't receive
     * a pong, which disconnects their Clients.
     */
    @Override
    public void run() {
        Logger.info(this, "starting...");

        running = true;

        long startPingTime = System.currentTimeMillis();
        long startDisconnectTime = System.currentTimeMillis();

        while (running) {

            // PING CYCLE
            // measure elapsed ping time
            long elapsedPing = System.currentTimeMillis() - startPingTime;
            if (elapsedPing > Config.getPingInterval()) {

                startPingTime = System.currentTimeMillis();
                if (!server.pingHandlers()) {
                    running = false;
                }
            }

            // DISCONNECTION TIMEOUT CYCLE
            long elapsedDisconnection = System.currentTimeMillis() - startDisconnectTime;
            if (elapsedDisconnection > Config.getTimeUntilDisconnect()) {

                startDisconnectTime = System.currentTimeMillis();
                if (!server.checkConnections()) {
                    running = false;
                }
            }
        }

        Logger.info(this, "stopping...");
    }

    /**
     * Stop the thread/runnable.
     */
    public void stop() {
        running = false;
    }

    @Override
    public String toString() {
        return "PingPong";
    }
}
