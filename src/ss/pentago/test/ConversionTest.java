package ss.pentago.test;

import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.exception.ChessNotationFormatException;
import ss.pentago.model.exception.RotationFormatException;
import ss.pentago.model.move.Rotation;
import ss.pentago.util.ChessNotation;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for index conversion, "chess" notation, rotation conversion.
 */
public class ConversionTest {

    /**
     * Test whether chess notation strings properly convert to board indices.
     */
    @Test
    public void testStringToIndexConversion() {
        String[] notated = {"a1", "a7", "z4", "g9", "f6", "c4", "aa", "a43", ":)", "a6", "f1"};
        int[] indices = {30, -1, -1, -1, 5, 14, -1, -1, -1, 0, 35};
        boolean[] passes = {true, false, false, false, true, true, false, false, false, true, true};
        for (int i = 0; i < notated.length; i++) {
            try {
                int ind = ChessNotation.parseString(notated[i]);
                assertTrue(passes[i]);
                assertEquals(indices[i], ind);
            } catch (ChessNotationFormatException e) {
                assertFalse(passes[i]);
            }
        }
    }

    /**
     * Test whether board indices properly convert to chess notation strings.
     */
    @Test
    public void testIndexToStringConversion() {
        int[] indices = {-1, 0, 30, 15, 34, 35, 36, 100, 5};
        String[] notated = {"", "a6", "a1", "d4", "e1", "f1", "", "", "f6"};
        boolean[] passes = {false, true, true, true, true, true, false, false, true};
        for (int i = 0; i < indices.length; i++) {
            try {
                String nota = ChessNotation.parseIndex(indices[i]);
                assertTrue(passes[i]);
                assertEquals(notated[i], nota);
            } catch (ChessNotationFormatException e) {
                assertFalse(passes[i]);
            }
        }
    }

    /**
     * Nested tests for rotation conversion.
     */
    @Nested
    class RotationConversionTest {
        // All possible rotations
        private final Rotation tl = new Rotation(Quadrant.TOP_LEFT, true);
        private final Rotation tlc = new Rotation(Quadrant.TOP_LEFT, false);
        private final Rotation tr = new Rotation(Quadrant.TOP_RIGHT, true);
        private final Rotation trc = new Rotation(Quadrant.TOP_RIGHT, false);
        private final Rotation bl = new Rotation(Quadrant.BOTTOM_LEFT, true);
        private final Rotation blc = new Rotation(Quadrant.BOTTOM_LEFT, false);
        private final Rotation br = new Rotation(Quadrant.BOTTOM_RIGHT, true);
        private final Rotation brc = new Rotation(Quadrant.BOTTOM_RIGHT, false);

        /**
         * Test that {@code Rotation} gets converted properly.
         */
        @Test
        public void testIndexToRotationConversion() {
            try {
                assertEquals(tlc.getCode(), 0);
                assertEquals(tl.getCode(), 1);
                assertEquals(trc.getCode(), 2);
                assertEquals(tr.getCode(), 3);
                assertEquals(blc.getCode(), 4);
                assertEquals(bl.getCode(), 5);
                assertEquals(brc.getCode(), 6);
                assertEquals(br.getCode(), 7);
            } catch (RotationFormatException e) {
                fail();
            }

            Rotation bogus = new Rotation(null, true);
            try {
                bogus.getCode();
            } catch (RotationFormatException e) {
                assertTrue(true);
            }
        }

        /**
         * Test that a int gets parsed into a {@code Rotation} properly.
         */
        @Test
        public void testRotationToIndexConversion() {
            try {
                assertEquals(tlc.getQuadrant(), Rotation.parseRotation(0).getQuadrant());
                assertEquals(tlc.getClockwise(), Rotation.parseRotation(0).getClockwise());
                assertEquals(tl.getQuadrant(), Rotation.parseRotation(1).getQuadrant());
                assertEquals(tl.getClockwise(), Rotation.parseRotation(1).getClockwise());
                assertEquals(trc.getQuadrant(), Rotation.parseRotation(2).getQuadrant());
                assertEquals(trc.getClockwise(), Rotation.parseRotation(2).getClockwise());
                assertEquals(tr.getQuadrant(), Rotation.parseRotation(3).getQuadrant());
                assertEquals(tr.getClockwise(), Rotation.parseRotation(3).getClockwise());
                assertEquals(blc.getQuadrant(), Rotation.parseRotation(4).getQuadrant());
                assertEquals(blc.getClockwise(), Rotation.parseRotation(4).getClockwise());
                assertEquals(bl.getQuadrant(), Rotation.parseRotation(5).getQuadrant());
                assertEquals(bl.getClockwise(), Rotation.parseRotation(5).getClockwise());
                assertEquals(brc.getQuadrant(), Rotation.parseRotation(6).getQuadrant());
                assertEquals(brc.getClockwise(), Rotation.parseRotation(6).getClockwise());
                assertEquals(br.getQuadrant(), Rotation.parseRotation(7).getQuadrant());
                assertEquals(br.getClockwise(), Rotation.parseRotation(7).getClockwise());
            } catch (RotationFormatException e) {
                fail();
            }

            try {
                Rotation.parseRotation(-1);
            } catch (RotationFormatException e) {
                assertTrue(true);
            }

            try {
                Rotation.parseRotation(8);
            } catch (RotationFormatException e) {
                assertTrue(true);
            }
        }
    }
}
