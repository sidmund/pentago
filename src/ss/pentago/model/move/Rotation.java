package ss.pentago.model.move;

import ss.pentago.model.board.Quadrant;
import ss.pentago.model.exception.RotationFormatException;

/**
 * Encodes a Rotation of a Quadrant, either clockwise or counterclockwise.
 */
public class Rotation {

    //@ private invariant quadrant != null;

    private final Quadrant quadrant;
    private final boolean clockwise;

    /**
     * Create a new Rotation.
     *
     * @param quadrant  quadrant to rotate
     * @param clockwise rotation direction, true for clockwise, false for counterclockwise
     */
    /*@
        requires clockwise == true || clockwise == false;
        ensures this.clockwise == clockwise && this.quadrant == quadrant;
    */
    public Rotation(Quadrant quadrant, boolean clockwise) {
        this.quadrant = quadrant;
        this.clockwise = clockwise;
    }

    /**
     * Get the associated Quadrant.
     *
     * @return the quadrant to rotate
     */
    //@ ensures \result == quadrant;
    //@ pure
    public Quadrant getQuadrant() {
        return quadrant;
    }

    /**
     * Get the associated direction.
     *
     * @return true for clockwise rotation, false for counterclockwise
     */
    //@ ensures \result == clockwise;
    //@ pure
    public boolean getClockwise() {
        return clockwise;
    }

    /**
     * Compute the code of a Rotation, as determined by quadrant and rotation direction.
     * <pre>
     * 0  top left counter-clockwise<br>
     * 1  top left clockwise<br>
     * 2  top right counter-clockwise<br>
     * 3  top right clockwise<br>
     * 4  bottom left counter-clockwise<br>
     * 5  bottom left clockwise<br>
     * 6  bottom right counter-clockwise<br>
     * 7  bottom right clockwise<br>
     * </pre>
     *
     * @return -1 if quadrant is invalid (i.e. null), else the code as listed above
     * @throws RotationFormatException when the Quadrant is null or undefined
     */
    /*@
        requires getQuadrant() != null;
        ensures \result >= 0 && \result < 8;
        ensures \result % 2 == 1 && getClockwise() &&
                \result % 2 == 0 && !getClockwise() &&
                (\forall int i; 0 <= i && i < Quadrant.values().length;
                    Quadrant.values()[i] == getQuadrant() && \result / 2 == i);
    */
    //@ pure
    public int getCode() throws RotationFormatException {
        if (getQuadrant() == null) {
            throw RotationFormatException.forInputRotation(this);
        }

        switch (getQuadrant()) {
            case TOP_LEFT:
                return getClockwise() ? 1 : 0;
            case TOP_RIGHT:
                return getClockwise() ? 3 : 2;
            case BOTTOM_LEFT:
                return getClockwise() ? 5 : 4;
            case BOTTOM_RIGHT:
                return getClockwise() ? 7 : 6;
            default:
                throw RotationFormatException.forInputRotation(this);
        }
    }

    /**
     * Parses the int argument as a {@code Rotation}.
     * The int must be between 0 and 7 (inclusive), which covers all possible 4 quadrant
     * along with all possible 2 rotation directions (clockwise and counterclockwise).
     *
     * @param rot the rotation code
     * @return a corresponding {@code Rotation}
     * @throws RotationFormatException when rot is out of bounds
     */
    //@ requires rot >= 0 && rot < 8;
    public static Rotation parseRotation(int rot) throws RotationFormatException {
        switch (rot) {
            case 0:
            case 1:
                return new Rotation(Quadrant.TOP_LEFT, rot % 2 == 1);
            case 2:
            case 3:
                return new Rotation(Quadrant.TOP_RIGHT, rot % 2 == 1);
            case 4:
            case 5:
                return new Rotation(Quadrant.BOTTOM_LEFT, rot % 2 == 1);
            case 6:
            case 7:
                return new Rotation(Quadrant.BOTTOM_RIGHT, rot % 2 == 1);
            default:
                throw RotationFormatException.forInputInt(rot);
        }
    }

    /**
     * Returns a string representation of this {@code Rotation}.
     *
     * @return string representation
     */
    //@ pure
    @Override
    public String toString() {
        return String.format("Rotation (quadrant=%s, clockwise=%s)", getQuadrant(), getClockwise());
    }
}
