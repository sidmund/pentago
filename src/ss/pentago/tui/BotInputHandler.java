package ss.pentago.tui;

import ss.pentago.network.client.OnlineClient;
import ss.pentago.util.Logger;
import ss.pentago.util.NameGenerator;

import java.io.IOException;

/**
 * BotInputHandler extends OnlineTextInputHandler by automatically sending
 * commands to the server, while still providing some basic user options
 * through a text-based interface to control the Bot. <br>
 * The BotInputHandler tries to queue for games and play them automatically
 * by calling the associated Client's player (AIPlayer) to generate a move.
 */
public class BotInputHandler extends OnlineTextInputHandler {

    /**
     * Creates a new {@code BotInputHandler} object,
     * which sends automated requests and AI-generated moves to a server.
     * This type of InputHandler only supports some basic commands for the operating user,
     * as all gameplay related commands are handled automatically.
     *
     * @param client the client to send input to
     */
    /*@
        requires client != null;
        ensures this.client == client;
    */
    public BotInputHandler(OnlineClient client) {
        super(client);
    }

    /**
     * Parses the supplied command, and tells the Client what to do.
     *
     * @param command the command
     * @return false if the client needs to be stopped
     * (due to messages not being sent in case of a closed connection),
     * true otherwise
     */
    //@ requires command != null && command != "";
    @Override
    protected boolean parseCommand(String command) {
        if (command == null) {
            return true;
        }

        String[] args = command.split(" ");

        switch (args[0].toLowerCase()) {
            case "p":
            case "ping":
                return protocol.sendPing();
            case "quit":
                return false;
            case "help":
                client.inform(getHelpMessage());
                return true;
            case "show":
                ((OnlineClient) client).setShowGameplay(true);
                client.inform("Now showing the gameplay");
                return true;
            case "hide":
                ((OnlineClient) client).setShowGameplay(false);
                client.inform("Now hiding the gameplay from view");
                return true;
            case "l":
            case "list":
                return protocol.sendList();
            default:
                client.informError("That's not a command");
                return true;
        }
    }

    /**
     * Generate a random username for this bot.
     *
     * @param username the username (ignored)
     * @throws IOException thrown when the Server closed the connection
     */
    @Override
    protected void setUsername(String username) throws IOException {
        super.setUsername(NameGenerator.randomName());
    }

    /**
     * While running, generate AI moves/commands, and read from System.in to
     * listen for bot control commands. Parse the input and tell the Client what to do.
     * On exit, call the associated Client's {@code close()}.
     */
    @Override
    public void run() {
        protocol.sendHello("Amazing Bot Client");

        // As long as we're not logged in, send a random username
        while (!((OnlineClient) client).isLoggedIn()) {
            try {
                setUsername(null);
                delay();
            } catch (IOException e) {
                Logger.info(this, "reader closed");
                running = false;
            }
        }

        opponentStartTime = System.currentTimeMillis();

        // Obtain user input
        while (running) {
            try {
                while (inputReader.ready()) {
                    String userInput = inputReader.readLine();

                    if (!userInput.equals("") && !parseCommand(userInput)) {
                        running = false;
                    }
                }
            } catch (IOException e) {
                Logger.info(this, "reader closed");
                running = false;
            }

            if (((OnlineClient) client).isLoggedIn()) {
                determineBotAction();
                delay();
            }
        }

        client.close();

        Logger.info(this, "no longer running");
    }

    /**
     * Get the full help message of allowed commands for this input handler.
     *
     * @return the help message
     */
    //@ pure
    @Override
    protected String getHelpMessage() {
        return "\n" +
                "---- ALLOWED COMMANDS (BOT CONTROL) ------------------------------------------\n" +
                " l, list                        show a list of online players\n" +
                " p, ping                        measure the connection to the server\n" +
                " show                           show the game play of this bot\n" +
                " hide                           hide the game play of this bot\n" +
                " help                           show this help menu\n" +
                " quit                           stop the bot and quit the application\n" +
                "------------------------------------------------------------------------------\n" +
                "\n";
    }
}
