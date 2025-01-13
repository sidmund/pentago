package ss.pentago.test.network;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.pentago.network.server.GameManager;
import ss.pentago.network.server.Server;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

public class ServerFullGameTest {

    private Server server;
    private GameManager gameManager;
//    private PingPong pinger;

    private Thread serverThread;
    private Thread gmThread;
//    private Thread pingThread;

    /**
     * Create new server and start it.
     */
    @BeforeEach
    public void setUp() {
        server = new Server();
        gameManager = new GameManager(server);
//        pinger = new PingPong(server);
//        Config.setPingInterval(50000);

        // Start server receiving connections
        server.createSocketAt(0);
        serverThread = new Thread(server);
        gmThread = new Thread(gameManager);
//        pingThread = new Thread(pinger, "PingPong");

        serverThread.start();
        gmThread.start();
//        pingThread.start();
    }

    @Test
    // Player 1 is Alice, Player 2 is BOB and Alice suppose to win
    public void fullGameTest() throws IOException {
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

            writeToServer1.println("QUEUE");
            writeToServer2.println("QUEUE");

            Assertions.assertEquals("NEWGAME~ALICE~BOB", getMessage(readFromServer1));
            Assertions.assertEquals("NEWGAME~ALICE~BOB", getMessage(readFromServer2));

            assertMove(readFromServer1, readFromServer2, "MOVE~0~4", writeToServer1);
            assertMove(readFromServer1, readFromServer2, "MOVE~5~4", writeToServer2);
            assertMove(readFromServer1, readFromServer2, "MOVE~1~4", writeToServer1);
            assertMove(readFromServer1, readFromServer2, "MOVE~9~4", writeToServer2);
            assertMove(readFromServer1, readFromServer2, "MOVE~2~4", writeToServer1);
            assertMove(readFromServer1, readFromServer2, "MOVE~10~4", writeToServer2);
            assertMove(readFromServer1, readFromServer2, "MOVE~3~4", writeToServer1);
            assertMove(readFromServer1, readFromServer2, "MOVE~11~4", writeToServer2);
            assertMove(readFromServer1, readFromServer2, "MOVE~4~4", writeToServer1);

            Assertions.assertEquals("GAMEOVER~VICTORY~ALICE", getMessage(readFromServer1));
            Assertions.assertEquals("GAMEOVER~VICTORY~ALICE", getMessage(readFromServer2));
        }
    }

    @Test
    public void rankTest() throws IOException {
        // Run two game where user ALICE win 2 time so expected elo is 420;
        fullGameTest();
        fullGameTest();
        try (Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
             BufferedReader readFromServer1 = new BufferedReader(
                     new InputStreamReader(socket1.getInputStream()));
             PrintWriter writeToServer1 = new PrintWriter(
                     new OutputStreamWriter(socket1.getOutputStream()), true)) {

            establish(readFromServer1, writeToServer1);
            login(readFromServer1, writeToServer1);
            writeToServer1.println("RANK");
            Assertions.assertEquals("RANK~ALICE~420", getMessage(readFromServer1));
        }
    }

    private void assertMove(BufferedReader server1, BufferedReader server2,
                            String expected, PrintWriter write) {
        write.println(expected);
        Assertions.assertEquals(expected, getMessage(server1));
        Assertions.assertEquals(expected, getMessage(server2));
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
//        pinger.stop();
        server.stop();
        try {
//            pingThread.join();
            gmThread.join();
            serverThread.join();
        } catch (InterruptedException e) {
            // ignore
        }
    }
}
