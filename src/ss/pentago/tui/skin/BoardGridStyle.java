package ss.pentago.tui.skin;

import ss.pentago.model.board.Board;

/**
 * BoardGridStyle specifies a way in which the Board grid is drawn.
 */
public enum BoardGridStyle {
    /**
     * <pre>
     *     . . . . . .
     *     . . . . . .
     *     . . . . . .
     *     . . . . . .
     *     . . . . . .
     *     . . . . . .
     * </pre>
     */
    UNIFORM("Uniform") {
        @Override
        boolean isPositionForFirstCharacter(int x, int y) {
            return true;
        }
    },
    /**
     * <pre>
     *     . . . , , ,
     *     . . . , , ,
     *     . . . , , ,
     *     , , , . . .
     *     , , , . . .
     *     , , , . . .
     * </pre>
     */
    QUADRANT("Quadrant") {
        @Override
        boolean isPositionForFirstCharacter(int x, int y) {
            return y < Board.DIM / 2 && x < Board.DIM / 2
                    || y >= Board.DIM / 2 && x >= Board.DIM / 2;
        }
    },
    /**
     * <pre>
     *     . , . , . ,
     *     , . , . , .
     *     . , . , . ,
     *     , . , . , .
     *     . , . , . ,
     *     , . , . , .
     * </pre>
     */
    ALTERNATING("Alternating") {
        @Override
        boolean isPositionForFirstCharacter(int x, int y) {
            return (y * Board.DIM + x) % 2 == y % 2;
        }
    },
    /**
     * <pre>
     *     . . . . . .
     *     , , , , , ,
     *     . . . . . .
     *     , , , , , ,
     *     . . . . . .
     *     , , , , , ,
     * </pre>
     */
    HORIZONTAL_LINES("Horizontal Lines") {
        @Override
        boolean isPositionForFirstCharacter(int x, int y) {
            return y % 2 == 0;
        }
    },
    /**
     * <pre>
     *     . , . , . ,
     *     . , . , . ,
     *     . , . , . ,
     *     . , . , . ,
     *     . , . , . ,
     *     . , . , . ,
     * </pre>
     */
    VERTICAL_LINES("Vertical Lines") {
        @Override
        boolean isPositionForFirstCharacter(int x, int y) {
            return (y * Board.DIM + x) % 2 == 0;
        }
    },
    /**
     * <pre>
     *     , , , , , ,
     *     , . . . . ,
     *     , . , , . ,
     *     , . , , . ,
     *     , . . . . ,
     *     , , , , , ,
     * </pre>
     */
    CIRCULAR("Circular") {
        @Override
        boolean isPositionForFirstCharacter(int x, int y) {
            return y > 0 && y < Board.DIM - 1 && (x == 0 || x == Board.DIM - 1)
                    || y == 0 || y == Board.DIM - 1 ||
                    (y == Board.DIM / 2 - 1 || y == Board.DIM / 2)
                            && (x == Board.DIM / 2 - 1 || x == Board.DIM / 2);
        }
    };

    private final String name;

    //@ requires name != null;
    //@ ensures this.name == name;
    BoardGridStyle(String name) {
        this.name = name;
    }

    /**
     * Calculates whether the specified position should be the first character
     * or the second (alt) character.
     * Package-private because only BoardSkin really needs to access it.
     *
     * @param x the column
     * @param y the row
     * @return true if the first character should be placed,
     * false if the second (alt) should be placed
     */
    abstract boolean isPositionForFirstCharacter(int x, int y);

    /**
     * @return the name of this BoardGridStyle
     */
    //@ pure
    @Override
    public String toString() {
        return name;
    }
}
