package ss.pentago.util;

import java.util.Random;

/**
 * Saved and reused Random object for efficiency.
 */
public class Randomizer {

    //@ private invariant RNG != null;

    private static final Random RNG = new Random();

    private Randomizer() {
    }

    /**
     * Returns a random integer between 0 and max (exclusive).
     *
     * @param max maximum amount (exclusive)
     * @return random int between 0 and max (exclusive)
     */
    //@ requires max > 0;
    //@ ensures \result >= 0 && \result < max;
    public static int randomInt(int max) {
        return RNG.nextInt(max);
    }

    /**
     * Returns a random boolean.
     *
     * @return a random boolean
     */
    //@ ensures \result || !\result;
    public static boolean randomBoolean() {
        return RNG.nextBoolean();
    }
}
