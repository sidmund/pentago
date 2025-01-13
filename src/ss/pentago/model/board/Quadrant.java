package ss.pentago.model.board;

import ss.pentago.model.exception.QuadrantFormatException;

/**
 * Quadrant represents one of four sub boards of {@code Board}.
 * Each Quadrant has an appropriate offset,
 * which can be used to deal with the fields in that sub board.
 */
public enum Quadrant {
    TOP_LEFT(0, 0),
    TOP_RIGHT(0, Board.DIM / 2),
    BOTTOM_LEFT(Board.DIM / 2, 0),
    BOTTOM_RIGHT(Board.DIM / 2, Board.DIM / 2);

    private final int rowOffset;
    private final int colOffset;

    /**
     * Creates a Quadrant with specified offsets.
     *
     * @param rowOffset the y offset
     * @param colOffset the x offset
     */
    /*@ ensures this.rowOffset == rowOffset
        && this.colOffset == colOffset;
    */
    Quadrant(int rowOffset, int colOffset) {
        this.rowOffset = rowOffset;
        this.colOffset = colOffset;
    }

    /**
     * @return the row, or y, offset
     */
    //@ ensures \result == rowOffset;
    //@ pure
    public int getRowOffset() {
        return rowOffset;
    }

    /**
     * @return the column, or x, offset
     */
    //@ ensures \result == colOffset;
    //@ pure
    public int getColOffset() {
        return colOffset;
    }

    /**
     * Parses the string argument as a {@code Quadrant}.
     * The string must conform exactly to either the full name of a {@code Quadrant},
     * or its abbreviation. E.g. "tl" or "topleft" or "top left" for {@code Quadrant.TOP_LEFT}.
     * Uppercase or lowercase does not matter.
     *
     * @param s the {@code String} containing
     *          the {@code Quadrant} representation to be parsed
     * @return the {@code Quadrant} represented by the string argument
     * @throws QuadrantFormatException if the {@code String}
     *                                 does not contain a parsable {@code Quadrant}
     */
    /*@
    ensures \result == TOP_LEFT && (s == "tl" || s == "topleft")
         || \result == TOP_RIGHT && (s == "tr" || s == "topright")
         || \result == BOTTOM_LEFT && (s == "bl" || s == "bottomleft")
         || \result == TOP_RIGHT && (s == "bl" || s == "bottomright");
    */
    public static Quadrant parseQuadrant(String s) throws QuadrantFormatException {
        switch (s.toLowerCase()) {
            case "tl":
            case "topleft":
            case "top left":
                return TOP_LEFT;
            case "tr":
            case "topright":
            case "top right":
                return TOP_RIGHT;
            case "br":
            case "bottomright":
            case "bottom right":
                return BOTTOM_RIGHT;
            case "bl":
            case "bottomleft":
            case "bottom left":
                return BOTTOM_LEFT;
            default:
                throw QuadrantFormatException.forInputString(s);
        }
    }

    /**
     * Returns a string representation of this {@code Quadrant}.
     *
     * @return the name of this {@code Quadrant}
     */
    @Override
    public String toString() {
        switch (this) {
            case TOP_LEFT:
                return "top left";
            case TOP_RIGHT:
                return "top right";
            case BOTTOM_LEFT:
                return "bottom left";
            default:
                return "bottom right";
        }
    }
}
