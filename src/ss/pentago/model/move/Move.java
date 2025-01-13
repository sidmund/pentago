package ss.pentago.model.move;

import ss.pentago.model.exception.MovePositionFormatException;

/**
 * Encodes a Move of a Player, including the index to place a Marble at,
 * the quadrant to rotate, and the direction of rotation.
 */
public class Move {

    //@ private invariant position > 0 && position <= 35;
    //@ private invariant rotation != null;

    private final int position;
    private final Rotation rotation;

    /**
     * Creates a new Move.
     *
     * @param position the index to place a Marble at
     * @param rotation the rotation of the quadrant
     */
    /*@
        requires position > 0 && position <= 35;
        ensures this.position == position && this.rotation == rotation;
    */
    public Move(int position, Rotation rotation) {
        this.position = position;
        this.rotation = rotation;
    }

    /**
     * Gets the associated position to place a Marble at.
     *
     * @return the position as an index
     */
    //@ ensures \result == position;
    //@ pure
    public int getPosition() {
        return position;
    }

    /**
     * Gets the associated Rotation.
     *
     * @return the rotation of the quadrant
     */
    //@ ensures \result == rotation;
    //@ pure
    public Rotation getRotation() {
        return rotation;
    }

    /**
     * Parses the int argument as a {@code Rotation}.
     * The int must be between 0 and 35 (inclusive), which covers all possible board positions.
     *
     * @param i the index position
     * @return the same i if it's within range, otherwise throw the exception
     * @throws MovePositionFormatException when i is out of bounds
     */
    //@ requires i >= 0 && i < 36;
    //@ ensures \result == i ==> i >= 0 && i < 36;
    public static int parseIndex(int i) throws MovePositionFormatException {
        if (i < 0 || i > 35) {
            throw MovePositionFormatException.forInputInt(i);
        } else {
            return i;
        }
    }

    /**
     * Returns a string representation of this {@code Move}.
     *
     * @return string representation
     */
    //@ pure
    @Override
    public String toString() {
        return String.format("Move (position=%d, %s)", getPosition(), getRotation());
    }
}
