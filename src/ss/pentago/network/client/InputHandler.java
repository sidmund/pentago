package ss.pentago.network.client;

import ss.pentago.util.Logger;

/**
 * The {@code InputHandler} processes user input and
 * tells the {@code Client} what to do with it.
 */
public abstract class InputHandler implements Runnable {

    /*@
        protected invariant client != null;
    */

    /**
     * The associated Client to control.
     */
    protected final Client client;

    private Thread thread;
    protected boolean running;

    /**
     * Creates a new {@code InputHandler} object.
     *
     * @param client the client to send input to
     */
    /*@
        requires client != null;
        ensures this.client == client;
    */
    protected InputHandler(Client client) {
        this.client = client;
    }

    /**
     * Start running this {@code InputHandler}.
     */
    //@ ensures thread != null && thread.isAlive() && running == true;
    public void start() {
        Logger.info(this, "starting thread...");
        running = true;
        thread = new Thread(this, "InputHandler");
        thread.start();
    }

    /**
     * Stop this {@code InputHandler}.
     */
    //@ ensures running == false && !thread.isAlive();
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
}
