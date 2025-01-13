package ss.pentago.util;

import ss.pentago.model.exception.ChessNotationFormatException;

/**
 * Helper class to convert String containing chess notation to {@code Board} indices
 * and vice versa.
 * <br><br>
 * The indices on the board are numbered as follows:
 *
 * <pre>
 *      0  1  2  3  4  5
 *      6  7  8  9 10 11
 *     12 13 14 15 16 17
 *     18 19 20 21 22 23
 *     24 25 26 27 28 29
 *     30 31 32 33 34 35
 * </pre>
 * <p>
 * While the chess notation looks like this:
 *
 * <pre>
 *     6 . . . . . .
 *     5 . . . . . .
 *     4 . . . . . .
 *     3 . . . . . .
 *     2 . . . . . .
 *     1 . . . . . .
 *       a b c d e f
 * </pre>
 */
public class ChessNotation {

    private ChessNotation() {
    }

    /**
     * Convert a {@code Board} index to chess notation as a String.
     *
     * @param index the board index, between 0 and 36 (exclusive)
     * @return a String containing the chess notation
     * @throws ChessNotationFormatException when the index is out of range
     */
    /*@
        requires index >= 0 && index < 36;
        ensures \result.length() == 2
            && "abcdef".contains(String.valueOf(\result.charAt(0)))
            && "123456".contains(String.valueOf(\result.charAt(1)));
    */
    public static String parseIndex(int index) throws ChessNotationFormatException {
        if (index < 0 || index > 35) {
            throw ChessNotationFormatException.forInputIndex(index);
        }

        char col = "abcdef".charAt(index % 6);
        int row = 6 - index / 6;
        return String.format("%s%d", col, row);
    }

    /**
     * Convert a chess notation String to a {@code Board} index.
     *
     * @param s the string
     * @return an index between 0 and 36 (exclusive)
     * @throws ChessNotationFormatException when the string is not valid chess notation
     */
    /*@
        requires s != null && s.length() == 2
            && "abcdef".contains(s.substring(0, 1))
            && "123456".contains(s.substring(1));
        ensures \result >= 0 && \result < 36;
    */
    public static int parseString(String s) throws ChessNotationFormatException {
        if (s == null || s.length() != 2
                || !"abcdef".contains(s.toLowerCase().substring(0, 1))
                || !"123456".contains(s.toLowerCase().substring(1))) {
            throw ChessNotationFormatException.forInputString(s);
        }

        int col = s.toLowerCase().charAt(0) - 'a';
        int row = '6' - s.toLowerCase().charAt(1);
        return row * 6 + col;
    }
}
