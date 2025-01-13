package ss.pentago.model.board;

import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;

import java.util.Arrays;

/**
 * Board represents the full {@code DIM * DIM} Pentago board.
 * A Board can be queried for information about fields and win conditions,
 * and its fields can be updated.
 */
public class Board {

    /*@ public invariant fields.length == DIM && fields[0].length == DIM;
        public invariant
            (\forall int r; r >= 0 && r < DIM;
                (\forall int c; c >= 0 && c < DIM;
                           fields[r][c] == Marble.EMPTY
                        || fields[r][c] == Marble.BLACK
                        || fields[r][c] == Marble.WHITE
            ));
    @*/
    /**
     * The dimension of the Pentago board.
     */
    public static final int DIM = 6;

    /**
     * The fields of the Pentago board as an array of {@code Marble},
     * measuring {@code DIM * DIM}.
     */
    //@ spec_public
    private final Marble[][] fields;

    /**
     * Creates a new Board filled with {@code Marble.EMPTY}.
     */
    //@ ensures fields != null;
    public Board() {
        fields = new Marble[DIM][DIM];
        reset();
    }

    /**
     * Returns a deep copy of this Board.
     *
     * @return a deep copy of this board
     */
    /*@ ensures \result != this;
        ensures (\forall int r; r >= 0 && r < DIM; (\forall int c; c >= 0 && c < DIM;
            \result.fields[r][c] == fields[r][c]));
     @*/
    public Board deepCopy() {
        Board boardCopy = new Board();
        for (int r = 0; r < DIM; r++) {
            for (int c = 0; c < DIM; c++) {
                boardCopy.setField(r, c, fields[r][c]);
            }
        }
        return boardCopy;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     *
     * @param index the index in the field
     * @return true if index is a valid index
     */
    //@ ensures \result ==> index >= 0 && index < DIM * DIM;
    //@ pure
    public boolean isField(int index) {
        return isField(index / DIM, index % DIM);
    }

    /**
     * Returns true if the specified position refers to
     * a valid field on the board.
     *
     * @param row the row
     * @param col the column
     * @return true if the position is valid
     */
    //@ ensures \result ==> row >= 0 && row < DIM && col >= 0 && col < DIM;
    //@ pure
    public boolean isField(int row, int col) {
        return row >= 0 && row < DIM && col >= 0 && col < DIM;
    }

    /**
     * Returns the Marble at {@code index}.
     *
     * @param index the number of the field
     * @return the mark on the field, or null if the index was not valid
     */
    /*@ requires isField(index);
      ensures !isField(index) ==> \result == null;
      ensures isField(index) ==> \result == Marble.EMPTY
                                || \result == Marble.BLACK
                                || \result == Marble.WHITE;
     @*/
    //@ pure
    public Marble getField(int index) {
        return getField(index / DIM, index % DIM);
    }

    /**
     * Returns the {@code Marble} at the specified position.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field, or null if the position was not valid
     */
    /*@ requires isField(row, col);
        ensures !isField(row, col) ==> \result == null;
        ensures isField(row, col) ==> \result == Marble.EMPTY
                                || \result == Marble.BLACK
                                || \result == Marble.WHITE;
     @*/
    //@ pure
    public Marble getField(int row, int col) {
        return isField(row, col) ? fields[row][col] : null;
    }

    /**
     * Returns true if the board contains {@code Marble.EMPTY} at the specified index.
     *
     * @param index the index of the field
     * @return true if the field is empty
     */
    /*@ requires isField(index);
        ensures \result ==> getField(index) == Marble.EMPTY;
     @*/
    //@ pure
    public boolean isEmptyField(int index) {
        return isEmptyField(index / DIM, index % DIM);
    }

    /**
     * Returns true if the board contains {@code Marble.EMPTY} at the specified position.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return true if the field is empty
     */
    /*@ requires isField(row, col);
        ensures \result ==> getField(row, col) == Marble.EMPTY;
     @*/
    public boolean isEmptyField(int row, int col) {
        return getField(row, col) == Marble.EMPTY;
    }

    /**
     * Sets the content of the field at specified position to {@code marble}.
     *
     * @param row    the field row
     * @param col    the field column
     * @param marble the marble to be placed
     */
    /*@ requires marble != null && isField(row, col);
        ensures getField(row, col) == marble;
        ensures \old(getNumberOfEmptySpots()) - 1 == getNumberOfEmptySpots();
     @*/
    public void setField(int row, int col, Marble marble) {
        if (marble != null && isField(row, col)) {
            fields[row][col] = marble;
        }
    }

    /**
     * Sets the content of the field at {@code index} to {@code marble}.
     *
     * @param index  the index
     * @param marble the marble to be placed
     */
    /*@ requires marble != null && isField(index);
        ensures getField(index) == marble;
        ensures \old(getNumberOfEmptySpots()) - 1 == getNumberOfEmptySpots();
     @*/
    public void setField(int index, Marble marble) {
        setField(index / DIM, index % DIM, marble);
    }

    /**
     * Checks whether there is a row which contains 5
     * of the specified {@code Marble}.
     *
     * @param marble the {@code Marble} of interest
     * @return true if that {@code Marble} has a row of 5
     */
    //@ requires marble != null && marble != Marble.EMPTY;
    //@ pure
    public boolean has5Row(Marble marble) {
        if (marble == null || marble == Marble.EMPTY) {
            return false;
        }

        for (int row = 0; row < DIM; row++) {
            int connect = 0;

            for (int col = 0; col < DIM; col++) {
                if (getField(row, col) == marble) {
                    connect++;
                } else if (col >= 1) {
                    break;
                }
            }

            if (connect >= 5) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether there is a column which contains 5
     * of the specified {@code Marble}.
     *
     * @param marble the {@code Marble} of interest
     * @return true if that {@code Marble} has a column of 5
     */
    //@ requires marble != null && marble != Marble.EMPTY;
    //@ pure
    public boolean has5Column(Marble marble) {
        if (marble == null || marble == Marble.EMPTY) {
            return false;
        }

        for (int col = 0; col < DIM; col++) {
            int connect = 0;

            for (int row = 0; row < DIM; row++) {
                if (getField(row, col) == marble) {
                    connect++;
                } else if (row >= 1) {
                    break;
                }
            }

            if (connect >= 5) {
                return true;
            }
        }
        return false;
    }

    /**
     * Helper method to check whether there is a downward sloping diagonal which contains 5
     * of the specified {@code Marble}.
     *
     * @param marble the {@code Marble} of interest
     * @return true if that {@code Marble} has a down diagonal of 5
     */
    //@ requires marble != null && marble != Marble.EMPTY;
    //@ pure
    private boolean has5InDownDiagonal(Marble marble) {
        if (marble == null || marble == Marble.EMPTY) {
            return false;
        }

        // The 4 possible down diagonals can start in either of the following positions (#):
        /*
            ##....
            ##o...
            .ooo..
            ..ooo.
            ...ooo
            ....oo
         */
        for (int xo = 0; xo < 2; xo++) {
            for (int yo = 0; yo < 2; yo++) {
                // offsets: (0,0), (0,1), (1,0), (1,1)
                boolean hasDiagonal = true;
                for (int i = 0; i < 5; i++) {
                    if (getField(yo + i, xo + i) != marble) {
                        hasDiagonal = false;
                        break;
                    }
                }
                if (hasDiagonal) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Helper method to check whether there is a upward sloping diagonal which contains 5
     * of the specified {@code Marble}.
     *
     * @param marble the {@code Marble} of interest
     * @return true if that {@code Marble} has an up diagonal of 5
     */
    //@ requires marble != null && marble != Marble.EMPTY;
    //@ pure
    private boolean has5InUpDiagonal(Marble marble) {
        if (marble == null || marble == Marble.EMPTY) {
            return false;
        }

        // The 4 possible up diagonal can start in either of the following positions (#):
        /*
            ....oo
            ...ooo
            ..ooo.
            .ooo..
            ##o...
            ##....
         */
        for (int xo = 0; xo < 2; xo++) {
            for (int yo = 0; yo > -2; yo--) {
                // offsets: (0,0), (1,0), (0,-1), (1,-1)
                boolean hasDiagonal = true;
                for (int i = 5; i > 0; i--) {
                    if (getField(yo + i, xo + Math.abs(i - 5)) != marble) {
                        hasDiagonal = false;
                        break;
                    }
                }
                if (hasDiagonal) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Checks whether there is a diagonal which contains 5
     * of the specified {@code Marble}.
     *
     * @param marble the {@code Marble} of interest
     * @return true if that {@code Marble} has a diagonal of 5
     */
    //@ requires marble != null && marble != Marble.EMPTY;
    //@ pure
    public boolean has5Diagonal(Marble marble) {
        return has5InDownDiagonal(marble) || has5InUpDiagonal(marble);
    }

    /**
     * Rotates a sub board.
     *
     * @param rotation the quadrant and direction
     */
    /*@
        requires rotation != null;
        ensures \old(getNumberOfEmptySpots()) == getNumberOfEmptySpots();
    */
    public void rotate(Rotation rotation) {
        if (rotation == null) {
            return;
        }

        rotate(rotation.getQuadrant(), rotation.getClockwise());
    }

    /**
     * Rotates a sub board.
     *
     * @param quadrant  the sub board to rotate
     * @param clockwise true for clockwise, false for counterclockwise
     */
    /*@
        requires quadrant != null;
        ensures \old(getNumberOfEmptySpots()) == getNumberOfEmptySpots();
    */
    public void rotate(Quadrant quadrant, boolean clockwise) {
        if (quadrant == null) {
            return;
        }

        int yo = quadrant.getRowOffset();
        int xo = quadrant.getColOffset();

        // flip quadrant by line x = y
        for (int i = 0; i < DIM / 2; i++) {
            for (int j = i; j < DIM / 2; j++) {
                Marble temp = getField(i + yo, j + xo);
                setField(i + yo, j + xo, getField(j + yo, i + xo));
                setField(j + yo, i + xo, temp);
            }
        }

        if (clockwise) {
            // flip quadrant by line x = 0 when center of quadrant is (0,0)
            for (int i = 0; i < DIM / 2; i++) {
                Marble temp = getField(i + yo, xo);
                setField(i + yo, xo, getField(i + yo, xo + 2));
                setField(i + yo, xo + 2, temp);
            }

        } else {
            // flip quadrant by line y = 0 when center of quadrant is (0,0)
            for (int i = 0; i < DIM / 2; i++) {
                Marble temp = getField(yo, xo + i);
                setField(yo, xo + i, getField(yo + 2, xo + i));
                setField(yo + 2, xo + i, temp);
            }
        }
    }

    /**
     * Performs a full move: first places the marble, then rotates a sub board.
     *
     * @param move   the move
     * @param marble the marble
     */
    /*@
        requires move != null && marble != null;
        ensures \old(getNumberOfEmptySpots()) - 1 == getNumberOfEmptySpots();
    */
    public void perform(Move move, Marble marble) {
        if (move != null) {
            setField(move.getPosition(), marble);
            rotate(move.getRotation());
        }
    }

    /**
     * Computes number of empty spots left on the board.
     *
     * @return number of empty spots
     */
    //@ pure
    public int getNumberOfEmptySpots() {
        int count = 0;
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (getField(row, col) == Marble.EMPTY) {
                    count++;
                }
            }
        }
        return count;
    }

    /**
     * Checks if the whole board is full, without checking if there is a winner.
     *
     * @return true if the whole board is full
     */
    /*@
         ensures \result ==> (\forall int r; r >= 0 && r < DIM; (\forall int c; c >= 0 && c < DIM;
            fields[r][c] != Marble.EMPTY));
    */
    //@ pure
    public boolean isFull() {
        return getNumberOfEmptySpots() == 0;
    }

    /**
     * Checks whether the board is full without having a winner.
     *
     * @return true if the board is full without a winner
     */
    /*@
        ensures \result ==> isFull() && !(
            hasWinning5(Marble.BLACK) && !hasWinning5(Marble.WHITE)
         || hasWinning5(Marble.WHITE) && !hasWinning5(Marble.BLACK)
        );
    */
    //@ pure
    public boolean isDraw() {
        boolean blackWins = hasWinning5(Marble.BLACK);
        boolean whiteWins = hasWinning5(Marble.WHITE);

        if (isFull()) {
            // Check whether there is only 1 winner, in this case there is no draw
            // Otherwise (both win or none), it is a draw
            return !(blackWins && !whiteWins || whiteWins && !blackWins);
        } else {
            // Board is not full, so not a draw unless they both won
            return blackWins && whiteWins;
        }
    }

    /**
     * Checks if specified {@code Marble} has any winning row. It wins if it has at
     * least one row, column or diagonal of 5 of its pieces.
     * This method does not guarantee that that Marble actually wins, since
     * the other Marble might have a winning 5 too.
     *
     * @param marble the marble of interest
     * @return true if the mark has won exclusively,
     * false if it's a draw or the game is undecided
     */
    /*@
        requires marble == Marble.BLACK || marble == Marble.WHITE;
        ensures \result ==> has5Row(marble) || has5Column(marble) || has5Diagonal(marble);
    */
    //@ pure
    public boolean hasWinning5(Marble marble) {
        return has5Row(marble) || has5Column(marble) || has5Diagonal(marble);
    }

    /**
     * Returns true if the board has exactly one winner. This is the case when one of the
     * either {@code Marble.BLACK} or {@code Marble.WHITE}
     * has at least one row, column or diagonal of 5 of their pieces,
     * so not both can have a win.
     *
     * @return the Marble of the winner, null if no winner (or it was a draw)
     */
    /*@
        ensures \result == Marble.BLACK ==> hasWinning5(Marble.BLACK) && !hasWinning5(Marble.WHITE);
        ensures \result == Marble.WHITE ==> !hasWinning5(Marble.BLACK) && hasWinning5(Marble.WHITE);
        ensures \result == null ==> hasWinning5(Marble.BLACK) && hasWinning5(Marble.WHITE)
                                    || !hasWinning5(Marble.BLACK) && !hasWinning5(Marble.WHITE);
    */
    //@ pure
    public Marble hasWinner() {
        boolean blackWins = hasWinning5(Marble.BLACK);
        boolean whiteWins = hasWinning5(Marble.WHITE);

        if (blackWins && !whiteWins) {
            return Marble.BLACK;
        } else if (!blackWins && whiteWins) {
            return Marble.WHITE;
        } else {
            return null;
        }
    }

    /**
     * Returns true if the game is over. The game is over when there is exactly one winner
     * or the whole board is full (draw) or both win (draw).
     *
     * @return true if the game is over
     */
    //@ ensures \result ==> isDraw() || hasWinner() != null;
    //@ pure
    public boolean isGameOver() {
        return isDraw() || hasWinner() != null;
    }

    /**
     * Empties the board by setting all fields to {@code Marble.EMPTY}.
     */
    /*@ ensures (\forall int r; r >= 0 && r < DIM; (\forall int c; c >= 0 && c < DIM;
        fields[r][c] == Marble.EMPTY));
    */
    public void reset() {
        for (int row = 0; row < DIM; row++) {
            Arrays.fill(fields[row], Marble.EMPTY);
        }
    }

    /**
     * Returns a basic String representation of this board, showing just the field with marbles.
     *
     * @return the board representation
     */
    //@ pure
    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();

        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                s.append(getField(row, col));
            }
            s.append("\n");
        }

        return s.toString();
    }
}
