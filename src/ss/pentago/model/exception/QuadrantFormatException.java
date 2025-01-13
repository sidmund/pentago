package ss.pentago.model.exception;

/**
 * Thrown to indicate that the application has attempted to convert a string to a Quadrant value,
 * but that the string does not have the appropriate format.
 */
public class QuadrantFormatException extends Exception {

    /**
     * Construct a {@code QuadrantFormatException} with the specified detail message.
     *
     * @param s the detail message
     */
    public QuadrantFormatException(String s) {
        super(s);
    }

    /**
     * Factory method for making a {@code QuadrantFormatException}
     * given the specified input which caused the error.
     *
     * @param s the input causing the error
     * @return a new {@code QuadrantFormatException} with the error message
     */
    public static QuadrantFormatException forInputString(String s) {
        return new QuadrantFormatException("For input string: \"" + s + "\"");
    }
}
