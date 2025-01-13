package ss.pentago.model.exception;

/**
 * Thrown to indicate that the application has attempted to convert an int
 * to a {@code Move} position value,
 * but that the int does not have the appropriate range.
 */
public class MovePositionFormatException extends Exception {

    /**
     * Construct a {@code MovePositionFormatException} with the specified detail message.
     *
     * @param s the detail message
     */
    public MovePositionFormatException(String s) {
        super(s);
    }

    /**
     * Factory method for making a {@code MovePositionFormatException}
     * given the specified input which caused the error.
     *
     * @param i the input causing the error
     * @return a new {@code MovePositionFormatException} with the error message
     */
    public static MovePositionFormatException forInputInt(int i) {
        return new MovePositionFormatException("For input int: \"" + i + "\"");
    }
}
