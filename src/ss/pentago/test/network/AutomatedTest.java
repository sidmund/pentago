package ss.pentago.test.network;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.pentago.file.Config;

public class AutomatedTest {

    private AutomatedServer server;
    private AutomatedClient[] clients;
    private static final int SIZE = 10;

    @BeforeEach
    public void setup() throws InterruptedException {
        Config.setResponseDelayMultiPlayer(2000);

        server = new AutomatedServer();
        server.start();

        clients = new AutomatedClient[SIZE];

        for (int i = 0; i < SIZE; i++) {
            clients[i] = new AutomatedClient();
            clients[i].start();
        }

        // Let client finish some game
        Thread.sleep(100000);
    }

    @Test
    public void fullTest() {
        Assertions.assertEquals(10, server.getUserList().size());
        Assertions.assertTrue(server.getGameManager().getNrMatchesPlayed() > 0);
        Assertions.assertTrue(server.getGameManager().getCurrentMatches().size() > 0);
        Assertions.assertEquals(SIZE, server.getGameManager().getCurrentMatches().size() * 2 +
                server.getGameManager().getQueue().size());
        // Check if all the username is in user list.
        for (AutomatedClient ac : clients) {
            Assertions.assertTrue(server.getUserList().contains(ac.getUsername()));
        }
    }

    @AfterEach
    public void tearDownClient() {
        for (int i = 0; i < SIZE; i++) {
            clients[i].stop();
        }

        server.stop();
    }
}
