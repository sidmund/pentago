package ss.pentago.test.network;

import ss.pentago.network.protocol.ServerProtocolHandler;
import ss.pentago.network.server.*;
import ss.pentago.util.Logger;

import java.io.IOException;
import java.net.Socket;

public class AutomatedServer extends Server {

    private Thread serverThread;
    private Thread gmThread;
    private Thread pingThread;

    public AutomatedServer() {
        super();

        createSocketAt(55555);
//        setInputHandler(new ServerInputHandler(this));
    }

    /**
     * Need to override because the start and stop need to be separated,
     * otherwise in super.start() it would get stuck,
     * waiting for the threads to close.
     */
    @Override
    public void start() {
        Logger.info(this, "starting thread...");
        serverThread = new Thread(this, "Server");
        serverThread.start();

        gameManager = new GameManager(this);
        gmThread = new Thread(gameManager);

        pinger = new PingPong(this);
        pingThread = new Thread(pinger, "PingPong");

        gmThread.start();
        pingThread.start();
    }

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

    @Override
    public void stop() {
        super.stop();

        // wait for it to stop
        try {
            if (pingThread.isAlive()) {
                pingThread.join();
            }
            Logger.info(this, "PingPong thread is joined: " + !pingThread.isAlive());

            if (gmThread.isAlive()) {
                gmThread.join();
            }
            Logger.info(this, "GameManager thread is joined: " + !gmThread.isAlive());

            if (serverThread.isAlive()) {
                serverThread.interrupt();
                serverThread.join();
            }
            Logger.info(this, "thread is joined: " + !serverThread.isAlive());
        } catch (InterruptedException e) {
            // restore interrupted status
            serverThread.interrupt();
            gmThread.interrupt();
            pingThread.interrupt();
            Logger.info(this, "thread interrupted");
            Logger.info(this, "GameManager thread interrupted");
            Logger.info(this, "PingPong thread interrupted");
        }
    }
}
