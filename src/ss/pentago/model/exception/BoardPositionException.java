package ss.pentago.model.exception;

/**
 * Thrown to indicate that the application has attempted to place a {@code Marble}
 * at a certain position on a {@code Board}, while that position was either
 * out of bounds or already occupied by another non-empty {@code Marble}.
 */
public class BoardPositionException extends Exception {

    /**
     * Construct a {@code BoardPositionException} with the specified detail message.
     *
     * @param s the detail message
     */
    public BoardPositionException(String s) {
        super(s);
    }

    /**
     * Factory method for making a {@code BoardPositionException}
     * given the specified input which caused the error.
     * Either the indices are out of bounds, or the position on the board is already occupied.
     *
     * @param index the index causing the error
     * @return a new {@code BoardPositionException} with error message
     */
    public static BoardPositionException forPosition(int index) {
        return new BoardPositionException(
                String.format("For position: %d", index));
    }
}
