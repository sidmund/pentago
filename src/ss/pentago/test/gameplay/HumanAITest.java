package ss.pentago.test.gameplay;

import ss.pentago.model.player.Player;
import ss.pentago.model.player.PlayerFactory;
import ss.pentago.network.client.OfflineClient;
import ss.pentago.tui.OfflineTextInputHandler;
import ss.pentago.tui.TextDisplay;

import java.util.Scanner;

/**
 * Showcase gameplay between a human player and an AI.
 * Tests the interaction with the command line and playability.
 */
public class HumanAITest {

    public static void main(String[] args) {
        System.out.println("Pentago - Human vs AI");
        Player p1 = PlayerFactory.selectAIFromDifficultyMenu(
                "AI difficulty", new Scanner(System.in));
        Player p2 = PlayerFactory.makeHumanPlayer("Alice");

        OfflineClient client = new OfflineClient(p1, p2, true);
        client.addListener(new TextDisplay());
        client.setInputHandler(new OfflineTextInputHandler(client));
        client.start();
    }
}
