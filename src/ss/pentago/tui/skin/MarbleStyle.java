package ss.pentago.tui.skin;

import ss.pentago.model.board.Marble;

/**
 * MarbleStyle specifies in what way the player Marbles are drawn.
 */
public enum MarbleStyle {
    /**
     * Marble.BLACK: ◼, Marble.WHITE: ◻.
     */
    SQUARES("Squares", '◼', '◻'),
    /**
     * Marble.BLACK: B, Marble.WHITE: W.
     */
    LETTERS("Letters", 'B', 'W'),
    /**
     * Marble.BLACK: X, Marble.WHITE: O.
     */
    TIC_TAC_TOE("Tic Tac Toe", 'X', 'O');

    private final String name;
    private final char black;
    private final char white;

    //@ requires name != null;
    //@ ensures this.name == name && this.black == black && this.white == white;
    MarbleStyle(String name, char black, char white) {
        this.name = name;
        this.black = black;
        this.white = white;
    }

    //@ pure
    public char getBlack() {
        return black;
    }

    //@ pure
    public char getWhite() {
        return white;
    }

    //@ requires marble != Marble.EMPTY;
    //@ pure
    public char getCharacterFor(Marble marble) {
        switch (marble) {
            case BLACK:
                return black;
            case WHITE:
                return white;
            default:
                return ' ';
        }
    }

    /**
     * @return string representation of the MarbleStyle with the name
     * and how the player Marbles are represented.
     */
    //@ pure
    @Override
    public String toString() {
        return String.format("%s (%s, %s)", name, black, white);
    }
}
