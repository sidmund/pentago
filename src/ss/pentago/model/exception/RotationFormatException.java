package ss.pentago.model.exception;

import ss.pentago.model.move.Rotation;

/**
 * Thrown to indicate that the application has attempted to convert an int to a Rotation value,
 * but that the int does not have the appropriate range. It can also be thrown to indicate that
 * a Rotation cannot be converted to an int.
 */
public class RotationFormatException extends Exception {

    /**
     * Construct a {@code RotationFormatException} with the specified detail message.
     *
     * @param s the detail message
     */
    public RotationFormatException(String s) {
        super(s);
    }

    /**
     * Factory method for making a {@code RotationFormatException}
     * given the specified input which caused the error.
     *
     * @param i the input causing the error
     * @return a new {@code RotationFormatException} with the error message
     */
    public static RotationFormatException forInputInt(int i) {
        return new RotationFormatException("For input int: \"" + i + "\"");
    }

    /**
     * Factory method for making a {@code RotationFormatException}
     * given the specified input which caused the error.
     * This will happen when the Rotation's Quadrant is null;
     *
     * @param i the input causing the error
     * @return a new {@code RotationFormatException} with the error message
     */
    public static RotationFormatException forInputRotation(Rotation i) {
        return new RotationFormatException("For input int: \"" + i.toString() + "\"");
    }
}
