package ss.pentago.test.gameplay;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;
import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.player.*;
import ss.pentago.model.player.ai.AIPlayer;
import ss.pentago.model.player.ai.EasyAI;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test AI related attributes and gameplay, i.e. two instances of {@code AIPlayer}
 * interacting with a {@code Board}.
 */
public class AITest {

    /**
     * Test whether the Naive AI generated valid random values for its move.
     */
    @RepeatedTest(100)
    public void testNaiveAIMove() {
        Board board = new Board();
        AIPlayer naive = PlayerFactory.makeNaiveAI();
        naive.setMarble(Marble.BLACK);

        Move move = naive.determineMove(board);
        assertTrue(board.isEmptyField(move.getPosition()));
        Rotation rot = move.getRotation();
        assertNotNull(rot.getQuadrant());
    }

    /**
     * Tests that a game between two Naive AIs can be started
     * and that there is eventually a game over (a full random game).
     */
    @RepeatedTest(100)
    public void testRandomPlay() {
        AIPlayer p1 = PlayerFactory.makeNaiveAI();
        AIPlayer p2 = PlayerFactory.makeNaiveAI();

        AutomatedGame game = new AutomatedGame(p1, p2);
        game.shuffle();
        game.play();

        assertTrue(game.isGameOver());
    }

    /**
     * Tests that a game between any two AIs can be started
     * and that there is eventually a game over.
     */
    @Test
    public void testAIvsAI() {
        for (int p1 = 0; p1 < 3; p1++) {
            for (int p2 = 0; p2 < 3; p2++) {
                Player one = PlayerFactory.makeAI(p1);
                Player two = PlayerFactory.makeAI(p2);

                AutomatedGame game = new AutomatedGame(one, two);
                game.shuffle();
                game.play();

                assertTrue(game.isGameOver());
            }
        }
    }

    /**
     * Test direct wins and blocks.
     */
    @Nested
    class EasyAITest {

        private Board board;
        private EasyAI black;
        private EasyAI white;

        /**
         * Set up board and two EasyAIs.
         */
        @BeforeEach
        public void setUp() {
            board = new Board();

            black = PlayerFactory.makeEasyAI();
            black.setMarble(Marble.BLACK);

            white = PlayerFactory.makeEasyAI();
            white.setMarble(Marble.WHITE);
        }

        /**
         * Test whether EasyAI is smart enough to detect a win in a row
         * after a certain placement and rotation.
         */
        @Test
        public void testEasyAIFind5ConnectedRow() {
            board.setField(0, 0, Marble.BLACK);
            board.setField(0, 1, Marble.BLACK);
            board.setField(0, 2, Marble.BLACK);
            board.setField(0, 5, Marble.BLACK);
            System.out.println(board);

            Move blackMove = black.determineMove(board);
            assertNotNull(blackMove);

            assertEquals(Quadrant.TOP_RIGHT, blackMove.getRotation().getQuadrant());
            assertFalse(blackMove.getRotation().getClockwise());

            board.setField(blackMove.getPosition(), Marble.BLACK);
            board.rotate(blackMove.getRotation());

            assertEquals(Marble.BLACK, board.hasWinner());
            System.out.println(board);
        }

        /**
         * Test whether EasyAI is smart enough to detect a win in a column
         * after a certain placement and rotation.
         */
        @Test
        public void testEasyAIFind5ConnectedColumn() {
            board.setField(1, 2, Marble.BLACK);
            board.setField(3, 1, Marble.BLACK);
            board.setField(4, 1, Marble.BLACK);
            board.setField(5, 1, Marble.BLACK);
            System.out.println(board);

            Move blackMove = black.determineMove(board);
            assertNotNull(blackMove);

            assertEquals(Quadrant.TOP_LEFT, blackMove.getRotation().getQuadrant());
            assertTrue(blackMove.getRotation().getClockwise());

            board.setField(blackMove.getPosition(), Marble.BLACK);
            board.rotate(blackMove.getRotation());

            assertEquals(Marble.BLACK, board.hasWinner());
            System.out.println(board);
        }

        /**
         * Test whether EasyAI is smart enough to detect a win in a diagonal
         * after a certain placement and rotation.
         */
        @Test
        public void testEasyAIFind5ConnectedDiagonal() {
            board.setField(5, 5, Marble.BLACK);
            board.setField(4, 4, Marble.BLACK);
            board.setField(3, 3, Marble.BLACK);
            board.setField(2, 0, Marble.BLACK);
            System.out.println(board);

            Move blackMove = black.determineMove(board);
            assertNotNull(blackMove);

            assertEquals(Quadrant.TOP_LEFT, blackMove.getRotation().getQuadrant());
            assertFalse(blackMove.getRotation().getClockwise());

            board.setField(blackMove.getPosition(), Marble.BLACK);
            board.rotate(blackMove.getRotation());

            assertEquals(Marble.BLACK, board.hasWinner());
            System.out.println(board);
        }

        /**
         * Test whether EasyAI is smart enough to block an opponent from winning.
         */
        @Test
        public void testEasyAIBlockOpponent() {
            board.setField(0, 0, Marble.WHITE);
            board.setField(0, 1, Marble.WHITE);
            board.setField(0, 2, Marble.WHITE);
            board.setField(0, 4, Marble.WHITE);
            System.out.println(board);

            // assert that white can win

            Move whiteWin = white.determineMove(board);
            assertNotNull(whiteWin);
            board.setField(whiteWin.getPosition(), Marble.WHITE);
            board.rotate(whiteWin.getRotation());

            assertEquals(Marble.WHITE, board.hasWinner());
            System.out.println(board);

            // now remove its winning marble and assert the black blocks
            board.setField(0, 3, Marble.EMPTY);

            Move blackMove = black.determineMove(board);
            assertNotNull(blackMove);
            board.setField(blackMove.getPosition(), Marble.BLACK);
            board.rotate(blackMove.getRotation());

            System.out.println(board);

            // assert that white can't win

            Move whiteMove = white.determineMove(board);
            assertNotNull(whiteMove);
            board.setField(whiteMove.getPosition(), Marble.WHITE);
            board.rotate(whiteMove.getRotation());

            assertFalse(board.hasWinning5(Marble.WHITE));
            System.out.println(board);
        }
    }
}
