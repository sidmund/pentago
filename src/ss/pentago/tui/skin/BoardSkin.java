package ss.pentago.tui.skin;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;

/**
 * {@code BoardSkin} controls how the {@code Board} will look.
 * This class is only used by TUI related classes, and by the FileHandler and Config classes.
 */
public class BoardSkin {

    /**
     * The way the grid is drawn.
     */
    private BoardGridStyle boardGridStyle;
    /**
     * The main character.
     */
    private BoardGridCharacter gridCharacter;
    /**
     * A second character for certain board styles.
     */
    private BoardGridCharacter altGridCharacter;
    /**
     * The way the marbles are drawn.
     */
    private MarbleStyle marbleStyle;
    /**
     * Whether to display the notation along the sides.
     */
    private boolean hideNotation;

    /**
     * Create a new BoardSkin with specified attributes.
     * The BoardSkin represents how the Board will be drawn:
     * in what style and with what characters.
     *
     * @param boardGridStyle   the board grid style
     * @param gridCharacter    the main character
     * @param altGridCharacter the alternative character
     *                         (used for board styles that require two characters)
     * @param marbleStyle      the marble style
     * @param hideNotation     whether to display the notation along the sides.
     */
    public BoardSkin(BoardGridStyle boardGridStyle,
                     BoardGridCharacter gridCharacter, BoardGridCharacter altGridCharacter,
                     MarbleStyle marbleStyle, boolean hideNotation) {
        this.boardGridStyle = boardGridStyle;
        this.gridCharacter = gridCharacter;
        this.altGridCharacter = altGridCharacter;
        this.marbleStyle = marbleStyle;
        this.hideNotation = hideNotation;
    }

    /**
     * Returns a String representation of the supplied board, annotated with "chess" notation
     * if so desired. The board is drawn according to the {@code BoardSkin}.
     * For example:
     *
     * <pre>
     *     a b c d e f
     *   6 . , . , . , 6
     *   5 , . , ⬜ , . 5
     *   4 . , ⬜ , . , 4
     *   3 , . , ⬛ , . 3
     *   2 . ⬜ ⬜ , ⬛ , 2
     *   1 ⬛ . , . , . 1
     *     a b c d e f
     * </pre>
     *
     * @param board  the board to render
     * @param indent how many spaces to indent, if smaller than 0, this method will default to 0
     * @return the skinned board as a string
     */
    //@ requires indent >= 0;
    //@ pure
    public String render(Board board, int indent) {
        String indentation = " ".repeat(Math.max(0, indent));
        String columnAnnotation = hideNotation ? "  ———————————  " : "  a b c d e f  ";
        String rowAnnotation = hideNotation ? "||||||" : "654321";

        char firstChar = gridCharacter.getCharacter();
        char secondChar = altGridCharacter.getCharacter();

        StringBuilder sb = new StringBuilder();

        sb.append(indentation).append(columnAnnotation).append("\n");
        for (int y = 0; y < Board.DIM; y++) {
            sb.append(indentation).append(rowAnnotation.charAt(y));

            for (int x = 0; x < Board.DIM; x++) {
                Marble m = board.getField(y, x);
                if (m == Marble.EMPTY) {
                    sb.append(" ").append(boardGridStyle.isPositionForFirstCharacter(x, y)
                            ? firstChar : secondChar);
                } else {
                    sb.append(" ").append(marbleStyle.getCharacterFor(m));
                }
            }

            sb.append(" ").append(rowAnnotation.charAt(y)).append("\n");
        }
        sb.append(indentation).append(columnAnnotation);

        return sb.toString();
    }

    /**
     * Generates a preview of this BoardSkin.
     *
     * @param indent how much indentation on the left side for displaying in the terminal
     * @return a preview board as a string rendered in this BoardSkin
     */
    //@ pure
    public String getPreview(int indent) {
        Board preview = new Board();
        preview.setField(1, 1, Marble.BLACK);
        preview.setField(3, 2, Marble.BLACK);
        preview.setField(3, 4, Marble.WHITE);
        preview.setField(4, 0, Marble.WHITE);
        return render(preview, indent);
    }

    /**
     * Returns a string representation of this skin, along with rendering details.
     *
     * @return the string representation of this board skin
     */
    //@ pure
    @Override
    public String toString() {
        return String.format("BoardSkin: %s ('%s' '%s'), marbles ('%s' '%s'), %s",
                boardGridStyle,
                gridCharacter.getCharacter(), altGridCharacter.getCharacter(),
                marbleStyle.getBlack(), marbleStyle.getWhite(),
                hideNotation ? "hide notation" : "show notation");
    }

    //@ pure
    public BoardGridStyle getBoardGridStyle() {
        return boardGridStyle;
    }

    //@ pure
    public BoardGridCharacter getGridCharacter() {
        return gridCharacter;
    }

    //@ pure
    public BoardGridCharacter getAltGridCharacter() {
        return altGridCharacter;
    }

    //@ pure
    public MarbleStyle getMarbleStyle() {
        return marbleStyle;
    }

    //@ pure
    public boolean hideNotation() {
        return hideNotation;
    }

    //@ requires boardGridStyle != null;
    //@ ensures this.boardGridStyle == boardGridStyle;
    public void setBoardGridStyle(BoardGridStyle boardGridStyle) {
        this.boardGridStyle = boardGridStyle;
    }

    //@ requires gridCharacter != null;
    //@ ensures this.gridCharacter == gridCharacter;
    public void setGridCharacter(BoardGridCharacter gridCharacter) {
        this.gridCharacter = gridCharacter;
    }

    //@ requires altGridCharacter != null;
    //@ ensures this.altGridCharacter == altGridCharacter;
    public void setAltGridCharacter(BoardGridCharacter altGridCharacter) {
        this.altGridCharacter = altGridCharacter;
    }

    //@ requires marbleStyle != null;
    //@ ensures this.marbleStyle == marbleStyle;
    public void setMarbleStyle(MarbleStyle marbleStyle) {
        this.marbleStyle = marbleStyle;
    }

    //@ ensures this.hideNotation == hideNotation;
    public void setHideNotation(boolean hideNotation) {
        this.hideNotation = hideNotation;
    }
}
