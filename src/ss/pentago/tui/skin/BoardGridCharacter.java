package ss.pentago.tui.skin;

/**
 * BoardGridCharacter holds the allowed characters for drawing the Board grid.
 */
public enum BoardGridCharacter {
    CLEAR("Clear", ' '),
    LINE("Line", '-'),
    WATER("Water", '~'),
    DOT("Dot", '.'),
    COMMA("Comma", ','),
    COLON("Colon", ':');

    private final String name;
    private final char character;

    //@ requires name != null;
    //@ ensures this.name == name && this.character == character;
    BoardGridCharacter(String name, char character) {
        this.name = name;
        this.character = character;
    }

    //@ pure
    public char getCharacter() {
        return character;
    }

    //@ pure
    @Override
    public String toString() {
        return String.format("%s (%s)", name, character);
    }
}
