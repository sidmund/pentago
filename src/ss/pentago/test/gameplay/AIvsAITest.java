package ss.pentago.test.gameplay;

import ss.pentago.model.board.Board;
import ss.pentago.model.player.Player;
import ss.pentago.model.player.PlayerFactory;
import ss.pentago.tui.menu.TUIInputField;

import java.util.Scanner;

/**
 * Showcase gameplay between an AI and an AI.
 * Shows what kind of game overs happened for a number of matches.
 */
public class AIvsAITest {

    public static void main(String[] args) {
        System.out.println("Pentago - Human vs AI");
        Scanner scanner = new Scanner(System.in);
        Player p1 = PlayerFactory.selectAIFromDifficultyMenu("SELECT FIRST AI", scanner);
        Player p2 = PlayerFactory.selectAIFromDifficultyMenu("SELECT SECOND AI", scanner);
        int nrGames = TUIInputField.askForNumber("Number of games to play?",
                1, 1000001, 10, scanner);

        long start = System.nanoTime();
        int p1wins = 0;
        int draw = 0;
        int p2wins = 0;
        int totalMove = 0;
        for (int i = 1; i <= nrGames; i++) {
            AutomatedGame game = new AutomatedGame(p1, p2);
            game.play();
            Board last = game.getBoard();
            totalMove += 36 - last.getNumberOfEmptySpots();
            if (game.isDraw()) {
                draw++;
            } else if (game.getWinningPlayer() == p1) {
                p1wins++;
            } else if (game.getWinningPlayer() == p2) {
                p2wins++;
            }
            System.out.printf("Match %d ended%n", i);
        }

        System.out.printf("Player %s win: %d%n", p1.getName(), p1wins);
        System.out.printf("Draw: %d%n", draw);
        System.out.printf("Player %s win: %d%n", p2.getName(), p2wins);
        System.out.println("Average game length in ns: "
                + ((System.nanoTime() - start) / nrGames));
        System.out.println("Total time in ms: "
                + ((System.nanoTime() - start) / 1000000L));
        System.out.printf("Number of move: %d%n", totalMove / nrGames);
    }
}
