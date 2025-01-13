package ss.pentago.model.exception;

/**
 * Thrown to indicate that the application has attempted to convert
 * a chess notation string to an int index value or vice versa,
 * but that the string or int does not have the appropriate format.
 */
public class ChessNotationFormatException extends Exception {

    /**
     * Construct a {@code ChessNotationFormatException} with the specified detail message.
     *
     * @param s the detail message
     */
    public ChessNotationFormatException(String s) {
        super(s);
    }

    /**
     * Factory method for making a {@code ChessNotationFormatException}
     * given the specified input which caused the error.
     *
     * @param s the input causing the error
     * @return a new {@code ChessNotationFormatException} with the error message
     */
    public static ChessNotationFormatException forInputString(String s) {
        return new ChessNotationFormatException("For input string: \"" + s + "\"");
    }

    /**
     * Factory method for making a {@code ChessNotationFormatException}
     * given the specified input which caused the error.
     *
     * @param i the input causing the error
     * @return a new {@code ChessNotationFormatException} with the error message
     */
    public static ChessNotationFormatException forInputIndex(int i) {
        return new ChessNotationFormatException("For input index: \"" + i + "\"");
    }
}
