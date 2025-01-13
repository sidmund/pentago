package ss.pentago.test.network;

import org.junit.jupiter.api.*;
import ss.pentago.file.Config;
import ss.pentago.network.server.GameManager;
import ss.pentago.network.server.PingPong;
import ss.pentago.network.server.Server;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Test for validating message content when sending to and receiving from the Server.
 */
public class ServerTest {

    private Server server;
    private GameManager gameManager;
    private PingPong pinger;

    private Thread serverThread;
    private Thread gmThread;
    private Thread pingThread;

    /**
     * Create new server and start it.
     */
    @BeforeEach
    public void setUp() {
        server = new Server();
        gameManager = new GameManager(server);
        pinger = new PingPong(server);
        Config.setPingInterval(50000);

        // Start server receiving connections
        server.createSocketAt(0);
        serverThread = new Thread(server);
        gmThread = new Thread(gameManager);
        pingThread = new Thread(pinger, "PingPong");

        serverThread.start();
        gmThread.start();
        pingThread.start();
    }

    /**
     * Test whether server responds to invalid and valid commands.
     * @throws IOException when the socket was closed
     */
    @Test
    public void invalidCommandTest() throws IOException {
        // try-with-resources to ensure closing of resources afterwards
        // connect to server
        try (Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer = new BufferedReader(
                     new InputStreamReader(socket.getInputStream()));
             PrintWriter writeToServer = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()), true)) {
            // Init sequence to get into the server
            writeToServer.println("HELLO~test client");
            assertEquals("HELLO", getMessage(readFromServer).split("~")[0]);
            writeToServer.println("LOGIN~test user");
            assertEquals("LOGIN", getMessage(readFromServer));

            // Incorrect messages that should be ignored, the server should not crash
            // or maybe it actually tells the client to disconnect
            writeToServer.println("hhgshskdg");
            assertError(readFromServer);
            assertEquals("QUIT", getMessage(readFromServer));
        }
    }

    /**
     * Check if server kick player after client not responding.
     * (Not the actual user but the user client).
     * @throws IOException exception
     */
    @Test
    public void kickPlayerTest() throws IOException {
        try (Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer = new BufferedReader(
                     new InputStreamReader(socket.getInputStream()));
             PrintWriter writeToServer = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()), true)) {

            Config.setTimeUntilDisconnect(5000);

            writeToServer.println("HELLO~Client1");
            Assertions.assertEquals("HELLO", getMessage(readFromServer).split("~")[0]);

            writeToServer.println("LOGIN~1");
            Assertions.assertEquals("LOGIN", getMessage(readFromServer));

            writeToServer.println("LOGIN~TINTIN");
            Assertions.assertEquals("ALREADYLOGGEDIN", getMessage(readFromServer));

            try {
                Thread.sleep(Config.getTimeUntilDisconnect() + 1000);
            } catch (InterruptedException e) {
                //Do nothing
            }

            // The Server shouldn't send any messages anymore
            // (due to the way our ping is implemented),
            // since there are no clients to ping or sent other messages to
            Assertions.assertNull(getMessage(readFromServer));
        }
    }

    /**
     * Test when client disconnect that the client handler is stop/remove from the server.
     * @throws IOException exception
     */
    @Test
    public void disconnectTest() throws IOException {
        try (Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer = new BufferedReader(
                     new InputStreamReader(socket.getInputStream()));
             PrintWriter writeToServer = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()), true)) {

            establish(readFromServer, writeToServer);
            login(readFromServer, writeToServer);
            Assertions.assertEquals(1, server.getUserList().size());
            Assertions.assertEquals("ALICE", server.getUserList().get(0));
        }

        // give time for server to respond
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            // ignore
        }

        Assertions.assertEquals(0, server.getUserList().size());
    }


    /**
     * Check the command list.
     * @throws IOException exception
     */
    @Test
    public void listTest() throws IOException {
        try (Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer1 = new BufferedReader(
                     new InputStreamReader(socket1.getInputStream()));
             PrintWriter writeToServer1 = new PrintWriter(
                     new OutputStreamWriter(socket1.getOutputStream()), true);
             Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer2 = new BufferedReader(
                     new InputStreamReader(socket2.getInputStream()));
             PrintWriter writeToServer2 = new PrintWriter(
                     new OutputStreamWriter(socket2.getOutputStream()), true)) {

            establish(readFromServer1, writeToServer1);
            writeToServer1.println("LOGIN~ALICE");
            getMessage(readFromServer1);
            writeToServer2.println("HELLO~CLIENT BOB");
            getMessage(readFromServer2);
            // Test error when they request LIST when they not login
            writeToServer2.println("LIST");
            assertError(readFromServer2);
            // Test error when they request LIST with wrong format
            writeToServer1.println("LIST~fdjfe");
            assertError(readFromServer1);
            // Test if the LIST only show log in user
            writeToServer1.println("LIST");
            Assertions.assertEquals("LIST~ALICE", getMessage(readFromServer1));

            writeToServer2.println("LOGIN~BOB");
            getMessage(readFromServer2);
            writeToServer2.println("LIST");
            Assertions.assertEquals(3, getMessage(readFromServer2).split("~").length);
            writeToServer1.println("QUIT");
            socket1.close();
            // wait so the server remove the socket1 and it clientHandler
            try {
                Thread.sleep(100);
            } catch (InterruptedException e) {
                // ignore
            }
            writeToServer2.println("LIST");
            Assertions.assertEquals("LIST~BOB", getMessage(readFromServer2));
        }
    }

    /**
     * Test the ping and pong system.
     * @throws IOException exception
     */
    @Test
    public void pingTest() throws IOException {
        try (Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer = new BufferedReader(
                     new InputStreamReader(socket.getInputStream()));
             PrintWriter writeToServer = new PrintWriter(
                     new OutputStreamWriter(socket.getOutputStream()), true)) {

            // Test ping before establish connection should fail
            writeToServer.println("PING");
            assertError(readFromServer);

            // establish connection
            establish(readFromServer, writeToServer);

            // Test Ping before login
            writeToServer.println("PING");
            assertError(readFromServer);

            // Test Ping after login
            login(readFromServer, writeToServer);
            writeToServer.println("PING");
            Assertions.assertEquals("PONG", getMessage(readFromServer));
        }
    }

    private void assertError(BufferedReader readFromServer) {
        Assertions.assertEquals("ERROR", getMessage(readFromServer).split("~")[0]);
    }

    /**
     * Test login command.
     * @throws IOException exception
     */
    @Test
    public void loginTest() throws IOException {
        try (Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer1 = new BufferedReader(
                     new InputStreamReader(socket1.getInputStream()));
             PrintWriter writeToServer1 = new PrintWriter(
                     new OutputStreamWriter(socket1.getOutputStream()), true);
             Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer2 = new BufferedReader(
                     new InputStreamReader(socket2.getInputStream()));
             PrintWriter writeToServer2 = new PrintWriter(
                     new OutputStreamWriter(socket2.getOutputStream()), true)) {

            establish(readFromServer1, writeToServer1, readFromServer2, writeToServer2);
        }
    }

    private void login(BufferedReader readFromServer, PrintWriter writeToServer) {
        writeToServer.println("LOGIN~ALICE");
        Assertions.assertEquals("LOGIN", getMessage(readFromServer));
    }


    // Establish user "ALICE"
    private void establish(BufferedReader readFromServer, PrintWriter writeToServer) {
        writeToServer.println("HELLO~Client Alice");
        Assertions.assertEquals("HELLO", getMessage(readFromServer).split("~")[0]);
    }


    private void establish(BufferedReader readFromServer1, PrintWriter writeToServer1,
                           BufferedReader readFromServer2, PrintWriter writeToServer2) {
        writeToServer1.println("HELLO~Client Alice");
        Assertions.assertEquals("HELLO", getMessage(readFromServer1).split("~")[0]);
        writeToServer1.println("LOGIN~ALICE");
        Assertions.assertEquals("LOGIN", getMessage(readFromServer1));

        writeToServer2.println("HELLO~Client BOB");
        Assertions.assertEquals("HELLO", getMessage(readFromServer2).split("~")[0]);
        writeToServer2.println("LOGIN~BOB");
        Assertions.assertEquals("LOGIN", getMessage(readFromServer2));
    }

    private String getMessage(BufferedReader reader) {
        String s = null;
        try {
            s = reader.readLine();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return s;
    }

    /**
     * Stop the server and clean up the thread.
     */
    @AfterEach
    public void tearDown() {
        System.out.println("[ServerTest] cleaning up tests...");
        gameManager.stop();
        pinger.stop();
        server.stop();
        try {
            pingThread.join();
            gmThread.join();
            serverThread.join();
        } catch (InterruptedException e) {
            // ignore
        }
    }
}
