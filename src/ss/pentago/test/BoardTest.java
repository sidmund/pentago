package ss.pentago.test;

import org.junit.jupiter.api.*;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.board.Quadrant;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Testing class to validate all relevant properties of the {@code Board}.
 */
public class BoardTest {

    private Board board;

    /**
     * Create a new instance of a {@code Board}.
     */
    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Test whether the board contains only {@code Marble.EMPTY} after creating a new instance.
     */
    @Test
    public void testInitialization() {
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            assertTrue(board.isEmptyField(i));
        }
    }

    /**
     * Tests whether we can create a new instance of {@code Board},
     * with the exact same {@code Marble} placement.
     */
    @Test
    public void testDeepCopy() {
        // Place some Marbles
        board.setField(0, 0, Marble.BLACK);
        assertEquals(Marble.BLACK, board.getField(0, 0));
        board.setField(3, 5, Marble.WHITE);
        assertEquals(Marble.WHITE, board.getField(3, 5));

        Board copy = board.deepCopy();
        assertNotSame(copy, board);
        assertEquals(Marble.BLACK, copy.getField(0, 0));
        assertEquals(Marble.WHITE, copy.getField(3, 5));
    }

    /**
     * Test whether a {@code Marble} of any color can be placed and recalled.
     * Also test that trying to set a field to an invalid Marble is impossible,
     * and that {@code Marble.EMPTY} or {@code null}
     * cannot be used to check win conditions.
     */
    @Test
    public void testMarblePlacement() {
        // Valid marbles
        board.setField(0, 0, Marble.BLACK);
        assertEquals(Marble.BLACK, board.getField(0, 0));
        board.setField(3, 5, Marble.WHITE);
        assertEquals(Marble.WHITE, board.getField(3, 5));

        // Try to set an invalid marble, getting this field should still return Marble.EMPTY
        board.setField(1, 0, null);
        assertEquals(Marble.EMPTY, board.getField(1, 0));

        // Make BLACK win
        for (int col = 0; col <= 4; col++) {
            board.setField(4, col, Marble.BLACK);
        }
        assertTrue(board.has5Row(Marble.BLACK));
        // Now check that the winning condition fails with an invalid mark
        assertFalse(board.has5Row(null));
        assertFalse(board.has5Row(Marble.EMPTY));
    }

    /**
     * Test that out of bounds indices result in null and don't crash.
     */
    @Test
    public void testWrongIndices() {
        assertNull(board.getField(-1));
        assertNull(board.getField(Board.DIM * Board.DIM));
        assertNull(board.getField(-1, 0));
        assertNull(board.getField(Board.DIM, 0));
        assertNull(board.getField(0, -1));
        assertNull(board.getField(0, Board.DIM));
    }

    /**
     * Nested test class to group together tests pertaining to win conditions.
     */
    @Nested
    @DisplayName("Test win conditions")
    class BoardWinConditionsTest {

        /**
         * Test whether 5 in a row is detected for both colors of {@code Marble}.
         * It should be able to verify that both situations below are seen as 5 in a row.
         * <pre>
         *     .XXXXX
         *
         *     XXXXX.
         * </pre>
         */
        @ParameterizedTest
        @EnumSource(value = Marble.class, names = {"BLACK", "WHITE"})
        public void has5RowTest(Marble marble) {
            for (int col = 0; col <= 4; col++) {
                board.setField(3, col, marble);
            }
            assertTrue(board.has5Row(marble));

            for (int col = 1; col < Board.DIM; col++) {
                board.setField(2, col, marble);
            }
            assertTrue(board.has5Row(marble));

            // Test that there are no longer 5 in a row
            board.setField(3, 3, Marble.EMPTY);
            board.setField(2, 3, Marble.EMPTY);
            assertFalse(board.has5Row(marble));
        }

        /**
         * Test whether 5 in a column is detected for both colors of {@code Marble}.
         * It should be able to verify that both situations below are seen as 5 in a column.
         * <pre>
         *     .   X
         *     X   X
         *     X   X
         *     X   X
         *     X   X
         *     X   .
         * </pre>
         */
        @ParameterizedTest
        @EnumSource(value = Marble.class, names = {"BLACK", "WHITE"})
        public void testHas5Column(Marble marble) {
            for (int row = 0; row <= 4; row++) {
                board.setField(row, 0, marble);
            }
            assertTrue(board.has5Column(marble));

            for (int row = 1; row < Board.DIM; row++) {
                board.setField(row, 2, marble);
            }
            assertTrue(board.has5Column(marble));

            // Test that there are no longer 5 in a column
            board.setField(3, 0, Marble.EMPTY);
            board.setField(3, 2, Marble.EMPTY);
            assertFalse(board.has5Row(marble));
        }

        /**
         * Test whether 5 in a down diagonal is detected for a {@code Marble}.
         * It should be able to verify that the each of the 4 possible situations below
         * are seen as 5 in a down diagonal.
         * <pre>
         *     X..... .X.... ...... ......
         *     .X.... ..X... X..... .X....
         *     ..X... ...X.. .X.... ..X...
         *     ...X.. ....X. ..X... ...X..
         *     ....X. .....X ...X.. ....X.
         *     ...... ...... ....X. .....X
         * </pre>
         */
        @ParameterizedTest
        @EnumSource(value = Marble.class, names = {"BLACK", "WHITE"})
        public void testAllDownDiagonals(Marble marble) {
            for (int xo = 0; xo < 2; xo++) {
                for (int yo = 0; yo < 2; yo++) {
                    // offsets: (0,0), (0,1), (1,0), (1,1)
                    for (int i = 0; i < 5; i++) {
                        board.setField(yo + i, xo + i, marble);
                    }
                    assertTrue(board.has5Diagonal(marble));
                    board.reset();
                }
            }
        }

        /**
         * Test whether 5 in a down diagonal is detected for a {@code Marble}.
         * It should be able to verify that the each of the 4 possible situations below
         * are seen as 5 in an up diagonal.
         * <pre>
         *     ...... ...... ....X. .....X
         *     ....X. .....X ...X.. ....X.
         *     ...X.. ....X. ..X... ...X..
         *     ..X... ...X.. .X.... ..X...
         *     .X.... ..X... X..... .X....
         *     X..... .X.... ...... ......
         * </pre>
         */
        @ParameterizedTest
        @EnumSource(value = Marble.class, names = {"BLACK", "WHITE"})
        public void testAllUpDiagonals(Marble marble) {
            for (int xo = 0; xo < 2; xo++) {
                for (int yo = 0; yo > -2; yo--) {
                    // offsets: (0,0), (1,0), (0,-1), (1,-1)
                    for (int i = 5; i > 0; i--) {
                        board.setField(yo + i, xo + Math.abs(i - 5), marble);
                    }
                    assertTrue(board.has5Diagonal(marble));
                    board.reset();
                }
            }
        }

        /**
         * Completely fill the board in such a way that no 5 in a row exists,
         * so there is no winning player, and it will result in a draw.
         */
        @Test
        public void testBoardFullNoWinner() {
            fillBoardNoWinner(board);

            assertTrue(board.isFull());
            assertTrue(board.isDraw());
            assertNull(board.hasWinner());
            assertFalse(board.hasWinning5(Marble.BLACK));
            assertFalse(board.hasWinning5(Marble.WHITE));
            assertTrue(board.isGameOver());
        }

        /**
         * Completely fill the board and let both players win.
         * Test whether this is properly detected as a draw.
         */
        @Test
        public void testBoardFullBothWin() {
            fillBoardNoWinner(board);

            // Make BLACK win
            for (int col = 0; col < 5; col++) {
                board.setField(0, col, Marble.BLACK);
            }

            // Make WHITE win
            for (int col = 0; col < 5; col++) {
                board.setField(2, col, Marble.WHITE);
            }

            assertTrue(board.isFull());
            assertTrue(board.isDraw());
            assertNull(board.hasWinner());
            assertTrue(board.hasWinning5(Marble.BLACK));
            assertTrue(board.hasWinning5(Marble.WHITE));
            assertTrue(board.isGameOver());
        }

        /**
         * Completely fill the board, and make one player win.
         * Test that this does not result in a draw, but a win for that player.
         */
        @Test
        public void testBoardFullOneWinner() {
            fillBoardNoWinner(board);

            // Make BLACK win
            for (int col = 0; col < 5; col++) {
                board.setField(0, col, Marble.BLACK);
            }

            assertTrue(board.isFull());
            assertFalse(board.isDraw());
            assertEquals(Marble.BLACK, board.hasWinner());
            assertFalse(board.hasWinning5(Marble.WHITE));
            assertTrue(board.hasWinning5(Marble.BLACK));
            assertTrue(board.isGameOver());
        }

        /**
         * Make one player win, without a completely full board,
         * and test whether this win is detected and the game is over.
         */
        @Test
        public void testBoardNotFullWinner() {
            for (int i = 0; i < 5; i++) {
                board.setField(0, i, Marble.WHITE);
            }

            assertFalse(board.isDraw());
            assertEquals(Marble.WHITE, board.hasWinner());
            assertFalse(board.hasWinning5(Marble.BLACK));
            assertTrue(board.hasWinning5(Marble.WHITE));
            assertTrue(board.isGameOver());

            board.setField(0, Marble.EMPTY);
            assertNull(board.hasWinner());
            assertFalse(board.isGameOver());
        }

        /**
         * Make both players win, without a completely full board,
         * and test whether this is detected as a draw and the game is over.
         */
        @Test
        public void testBoardNotFullBothWin() {
            for (int i = 0; i < 5; i++) {
                board.setField(0, i, Marble.WHITE);
            }
            for (int i = 0; i < 5; i++) {
                board.setField(3, i, Marble.BLACK);
            }

            assertNull(board.hasWinner());
            assertTrue(board.hasWinning5(Marble.BLACK));
            assertTrue(board.hasWinning5(Marble.WHITE));
            assertTrue(board.isDraw());
            assertTrue(board.isGameOver());

            board.setField(0, Marble.EMPTY);
            assertEquals(Marble.BLACK, board.hasWinner());
            assertTrue(board.isGameOver());
        }
    }

    /**
     * Nested class for rotation tests,
     * as they share a setup method that the other test methods don't need.
     */
    @Nested
    @DisplayName("Test rotations")
    class BoardRotationTest {

        /**
         * Initialize the board to a specific configuration for rotating testing (adapted from
         * <a href="https://www.ultraboardgames.com/pentago/gfx/game5.jpg">ultraboardgames.com</a>).
         *
         * <pre>
         * .O.  .X.
         * .O.  XOX
         * .O.  ...
         *
         * ...  X..
         * .O.  ...
         * ...  ...
         * </pre>
         */
        @BeforeEach
        public void setUpBoardForRotation() {
            board.setField(0, 1, Marble.WHITE);
            board.setField(1, 1, Marble.WHITE);
            board.setField(2, 1, Marble.WHITE);
            board.setField(4, 1, Marble.WHITE);
            board.setField(1, 4, Marble.WHITE);
            board.setField(0, 4, Marble.BLACK);
            board.setField(1, 3, Marble.BLACK);
            board.setField(1, 5, Marble.BLACK);
            board.setField(3, 3, Marble.BLACK);
        }

        /**
         * Test whether top left clockwise rotation works.
         */
        @Test
        public void testRotateTopLeftClockwise() {
            board.rotate(Quadrant.TOP_LEFT, true);

            assertEquals(Marble.WHITE, board.getField(1, 0));
            assertEquals(Marble.WHITE, board.getField(1, 1));
            assertEquals(Marble.WHITE, board.getField(1, 2));
            assertTrue(board.isEmptyField(0, 0));
            assertTrue(board.isEmptyField(0, 1));
            assertTrue(board.isEmptyField(0, 2));
            assertTrue(board.isEmptyField(2, 0));
            assertTrue(board.isEmptyField(2, 1));
            assertTrue(board.isEmptyField(2, 2));
        }

        /**
         * Test whether top left counter clockwise rotation works.
         */
        @Test
        public void testRotateTopLeftCounterClockwise() {
            board.rotate(Quadrant.TOP_LEFT, false);

            assertEquals(Marble.WHITE, board.getField(1, 0));
            assertEquals(Marble.WHITE, board.getField(1, 1));
            assertEquals(Marble.WHITE, board.getField(1, 2));
            assertTrue(board.isEmptyField(0, 0));
            assertTrue(board.isEmptyField(0, 1));
            assertTrue(board.isEmptyField(0, 2));
            assertTrue(board.isEmptyField(2, 0));
            assertTrue(board.isEmptyField(2, 1));
            assertTrue(board.isEmptyField(2, 2));
        }

        /**
         * Test whether top right clockwise rotation works.
         */
        @Test
        public void testRotateTopRightClockwise() {
            board.rotate(Quadrant.TOP_RIGHT, true);

            assertTrue(board.isEmptyField(0, 3));
            assertEquals(Marble.BLACK, board.getField(0, 4));
            assertTrue(board.isEmptyField(0, 5));
            assertTrue(board.isEmptyField(1, 3));
            assertEquals(Marble.WHITE, board.getField(1, 4));
            assertEquals(Marble.BLACK, board.getField(1, 5));
            assertTrue(board.isEmptyField(2, 3));
            assertEquals(Marble.BLACK, board.getField(2, 4));
            assertTrue(board.isEmptyField(2, 5));
        }

        /**
         * Test whether top right counter clockwise rotation works.
         */
        @Test
        public void testRotateTopRightCounterClockwise() {
            board.rotate(Quadrant.TOP_RIGHT, false);

            assertTrue(board.isEmptyField(0, 3));
            assertEquals(Marble.BLACK, board.getField(0, 4));
            assertTrue(board.isEmptyField(0, 5));
            assertEquals(Marble.BLACK, board.getField(1, 3));
            assertEquals(Marble.WHITE, board.getField(1, 4));
            assertTrue(board.isEmptyField(1, 5));
            assertTrue(board.isEmptyField(2, 3));
            assertEquals(Marble.BLACK, board.getField(2, 4));
            assertTrue(board.isEmptyField(2, 5));
        }

        /**
         * Test whether bottom left clockwise rotation works.
         */
        @Test
        public void testRotateBottomLeftClockwise() {
            board.rotate(Quadrant.BOTTOM_LEFT, true);

            assertEquals(Marble.WHITE, board.getField(4, 1));
            assertTrue(board.isEmptyField(3, 0));
            assertTrue(board.isEmptyField(3, 1));
            assertTrue(board.isEmptyField(3, 2));
            assertTrue(board.isEmptyField(4, 0));
            assertTrue(board.isEmptyField(4, 2));
            assertTrue(board.isEmptyField(5, 0));
            assertTrue(board.isEmptyField(5, 1));
            assertTrue(board.isEmptyField(5, 2));
        }

        /**
         * Test whether bottom left counter clockwise rotation works.
         */
        @Test
        public void testRotateBottomLeftCounterClockwise() {
            board.rotate(Quadrant.BOTTOM_LEFT, false);

            assertEquals(Marble.WHITE, board.getField(4, 1));
            assertTrue(board.isEmptyField(3, 0));
            assertTrue(board.isEmptyField(3, 1));
            assertTrue(board.isEmptyField(3, 2));
            assertTrue(board.isEmptyField(4, 0));
            assertTrue(board.isEmptyField(4, 2));
            assertTrue(board.isEmptyField(5, 0));
            assertTrue(board.isEmptyField(5, 1));
            assertTrue(board.isEmptyField(5, 2));
        }

        /**
         * Test whether bottom right clockwise rotation works.
         */
        @Test
        public void testRotateBottomRightClockwise() {
            board.rotate(Quadrant.BOTTOM_RIGHT, true);

            assertEquals(Marble.BLACK, board.getField(3, 5));
            assertTrue(board.isEmptyField(3, 3));
            assertTrue(board.isEmptyField(3, 4));
            assertTrue(board.isEmptyField(4, 3));
            assertTrue(board.isEmptyField(4, 4));
            assertTrue(board.isEmptyField(4, 5));
            assertTrue(board.isEmptyField(5, 3));
            assertTrue(board.isEmptyField(5, 4));
            assertTrue(board.isEmptyField(5, 5));
        }

        /**
         * Test whether bottom right counter clockwise rotation works.
         */
        @Test
        public void testRotateBottomRightCounterClockwise() {
            board.rotate(Quadrant.BOTTOM_RIGHT, false);

            assertEquals(Marble.BLACK, board.getField(5, 3));
            assertTrue(board.isEmptyField(3, 3));
            assertTrue(board.isEmptyField(3, 4));
            assertTrue(board.isEmptyField(3, 5));
            assertTrue(board.isEmptyField(4, 3));
            assertTrue(board.isEmptyField(4, 4));
            assertTrue(board.isEmptyField(4, 5));
            assertTrue(board.isEmptyField(5, 4));
            assertTrue(board.isEmptyField(5, 5));
        }
    }

    /**
     * Helper function to fill the board such that no player has 5 in a row (see below).
     * <pre>
     *     XXOOXX
     *     OOXXOO
     *     XXOOXX
     *     OOXXOO
     *     XXOOXX
     *     OOXXOO
     * </pre>
     *
     * @param b the board
     */
    public static void fillBoardNoWinner(Board b) {
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            Marble[] marbles = {Marble.BLACK, Marble.BLACK, Marble.WHITE, Marble.WHITE};
            b.setField(i, marbles[i % 4]);
        }
    }
}
