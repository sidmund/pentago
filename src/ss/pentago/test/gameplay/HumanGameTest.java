package ss.pentago.test.gameplay;

import ss.pentago.model.player.PlayerFactory;
import ss.pentago.network.client.OfflineClient;
import ss.pentago.tui.OfflineTextInputHandler;
import ss.pentago.tui.TextDisplay;

/**
 * Showcase gameplay between two dummy human players.
 * Tests the interaction with the command line and playability.
 */
public class HumanGameTest {

    public static void main(String[] args) {
        System.out.println("Pentago - Human vs AI");
        OfflineClient client = new OfflineClient(
                PlayerFactory.makeHumanPlayer("Alice"),
                PlayerFactory.makeHumanPlayer("Bob"),
                true);
        client.addListener(new TextDisplay());
        client.setInputHandler(new OfflineTextInputHandler(client));
        client.start();
    }

}
