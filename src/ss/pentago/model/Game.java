package ss.pentago.model;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.exception.BoardPositionException;
import ss.pentago.model.player.Player;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;

/**
 * Game holds the two {@code Player} objects and the {@code Board}.
 * It provides methods for updating and querying the game board, and querying the players.
 */
public class Game {

    /*@
        protected invariant board != null;
        protected invariant current == 0 || current == 1;
        protected invariant players.length == 2;
        protected invariant players[0] != null && players[0].getMarble() == Marble.BLACK;
        protected invariant players[1] != null && players[1].getMarble() == Marble.WHITE;
    */

    protected final Board board;

    /**
     * The 2 players of the game.
     */
    protected final Player[] players;

    /**
     * Index of the current player.
     */
    protected int current;

    /**
     * Creates a new Game object, and sets the players marbles.
     * By default, the first player supplied is the starting player.
     * Call shuffle() to randomize the starting player.
     *
     * @param s0 the first player
     * @param s1 the second player
     */
    /*@
        requires s0 != null && s1 != null;
        ensures getFirstPlayer().getMarble() == Marble.BLACK;
        ensures getSecondPlayer().getMarble() == Marble.WHITE;
    */
    public Game(Player s0, Player s1) {
        board = new Board();
        players = new Player[2];

        players[0] = s0;
        players[0].setMarble(Marble.BLACK);
        players[1] = s1;
        players[1].setMarble(Marble.WHITE);

        current = 0;
    }

    /**
     * Meant to be used after calling the constructor,
     * to shuffle the players.
     */
    /*@
        ensures getFirstPlayer().getMarble() == Marble.BLACK;
        ensures getSecondPlayer().getMarble() == Marble.WHITE;
    */
    public void shuffle() {
        if (Math.random() < 0.5) {
            Player temp = players[0];
            players[0] = players[1];
            players[1] = temp;
            players[0].setMarble(Marble.BLACK);
            players[1].setMarble(Marble.WHITE);
        } else {
            Player temp = players[1];
            players[1] = players[0];
            players[0] = temp;
            players[0].setMarble(Marble.BLACK);
            players[1].setMarble(Marble.WHITE);
        }
    }

    /**
     * Updates the board by placing the current player's marble.
     *
     * @param position the position index
     * @throws BoardPositionException when the position is out of range or already occupied
     */
    //@ requires position >= 0 && position < Board.DIM * Board.DIM;
    //@ ensures board.getField(position) == getCurrentPlayer().getMarble();
    public void update(int position) throws BoardPositionException {
        if (!board.isEmptyField(position)) {
            throw BoardPositionException.forPosition(position);
        }

        board.setField(position, getCurrentPlayer().getMarble());
    }

    /**
     * Updates the board by rotating a sub board,
     * and switches to the next player.
     *
     * @param rotation the rotation
     * @return true if board so far resulted in a game over, false otherwise
     */
    //@ requires rotation != null;
    public boolean update(Rotation rotation) {
        board.rotate(rotation);

        // Alternate players
        current = (current + 1) % 2;

        return board.isGameOver();
    }

    /**
     * Updates the board by placing the current player's marble and rotating a sub board,
     * and switches to the next player. This is a convenience method that combines
     * updating the board with the position and with the rotation.
     *
     * @param move the move
     * @return true if move resulted in a game over, false otherwise
     * @throws BoardPositionException when the position is out of range or already occupied
     */
    //@ requires move != null;
    public boolean update(Move move) throws BoardPositionException {
        update(move.getPosition());
        return update(move.getRotation());
    }

    /**
     * Check whether the game is over.
     *
     * @return true if game over, false otherwise
     */
    //@ pure
    public boolean isGameOver() {
        return getBoard().isGameOver();
    }

    /**
     * Check whether the game ended in a draw.
     *
     * @return true if a draw, false otherwise
     */
    //@ pure
    public boolean isDraw() {
        return getBoard().isDraw();
    }

    /**
     * Get the winning player.
     *
     * @return null if no player won due to a draw or because the game is not over yet,
     * the first player, respectively, the second player, if they alone won
     */
    //@ pure
    public Player getWinningPlayer() {
        Marble win = getBoard().hasWinner();
        if (win == getFirstPlayer().getMarble()) {
            return getFirstPlayer();
        } else if (win == getSecondPlayer().getMarble()) {
            return getSecondPlayer();
        }
        return null;
    }

    /**
     * Get the Board associated with this game.
     *
     * @return the board
     */
    //@ pure
    public Board getBoard() {
        return board;
    }

    /**
     * Get the player who's turn it currently is.
     *
     * @return the current player
     */
    //@ pure
    public Player getCurrentPlayer() {
        return players[current];
    }

    /**
     * Get the first player.
     *
     * @return the first player
     */
    //@ pure
    public Player getFirstPlayer() {
        return players[0];
    }

    /**
     * Get the second player.
     *
     * @return the second player
     */
    //@ pure
    public Player getSecondPlayer() {
        return players[1];
    }
}
