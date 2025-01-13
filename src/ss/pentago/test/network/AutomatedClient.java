package ss.pentago.test.network;

import ss.pentago.model.player.PlayerFactory;
import ss.pentago.network.client.OnlineClient;
import ss.pentago.network.protocol.ClientProtocolHandler;
import ss.pentago.tui.BotInputHandler;
import ss.pentago.util.Logger;

import java.io.IOException;
import java.net.InetAddress;
import java.net.UnknownHostException;

public class AutomatedClient extends OnlineClient {

    private Thread clientThread;

    public AutomatedClient() {
        super(PlayerFactory.makeEasyAI());

        setProtocolHandler(new ClientProtocolHandler(this));
//        addListener(makeTextDisplay());
        setInputHandler(new BotInputHandler(this));

        while (true) {
            try {
                if (connect(InetAddress.getByName("localhost"), 55555)) {
                    break;
                }
            } catch (UnknownHostException e) {
                // ignore
            }
        }
    }

    /**
     * Need to override to separate the starting and stopping,
     * so we can start other threads in between.
     */
    @Override
    public void start() {
        Logger.info(this, "starting thread...");
        clientThread = new Thread(this, "Client");
        clientThread.start();
    }

    @Override
    public void run() {
        boolean run = true;

        if (inputHandler != null) {
            inputHandler.start();
        }

        while (run) {
            try {
                String msg = socketIn.readLine();

                if (msg == null) {
                    run = false;
                } else {
                    protocol.receive(msg);
                }
            } catch (IOException e) {
                // connection closed
                run = false;
            }
        }

        disconnect();
    }

    @Override
    public void stop() {
        super.stop();

        // wait for it to stop
        try {
            clientThread.join();
            Logger.info(this, "thread is joined: " + !clientThread.isAlive());
        } catch (InterruptedException e) {
            // restore interrupted status
            clientThread.interrupt();
            Logger.info(this, "thread interrupted");
        }
    }
}
