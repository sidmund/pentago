package ss.pentago.model.board;

/**
 * Marble represents the state a field on the {@code Board} can be in,
 * which is either empty, or held by either of two players, identified by black and white.
 */
public enum Marble {
    /**
     * Represents an empty spot on the board.
     */
    EMPTY('.'),
    /**
     * Represents the player who moves first.
     */
    BLACK('B'),
    /**
     * Represents the player who moves second.
     */
    WHITE('W');

    private final char character;

    /**
     * Creates a Marble with specified character representation.
     *
     * @param character the String representation
     */
    //@ ensures this.character == character;
    Marble(char character) {
        this.character = character;
    }

    /**
     * Gets the opposite {@code Marble} of the one supplied.
     * I.e. {@code Marble.BLACK} when supplied with {@code Marble.WHITE},
     * and {@code Marble.WHITE} when supplied with {@code Marble.BLACK}.
     *
     * @param marble the marble
     * @return the opposite marble
     */
    /*@
        requires marble != null;
        ensures \result == BLACK ==> marble == WHITE;
        ensures \result == WHITE ==> marble == BLACK;
    */
    public static Marble getOppositeOf(Marble marble) {
        return WHITE == marble ? BLACK : WHITE;
    }

    /**
     * @return String representation of this Marble
     */
    //@ pure
    @Override
    public String toString() {
        return String.valueOf(character);
    }
}
