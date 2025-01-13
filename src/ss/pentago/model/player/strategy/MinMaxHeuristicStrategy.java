package ss.pentago.model.player.strategy;

import ss.pentago.model.board.Board;
import ss.pentago.model.board.Marble;
import ss.pentago.model.board.Quadrant;
import ss.pentago.model.move.Move;
import ss.pentago.model.move.Rotation;

import java.util.ArrayList;
import java.util.List;

/**
 * {@code MinMaxHeuristicStrategy} is a type of {@code Strategy} that determines its moves
 * using a min-max algorithm and some smart heuristics. By default it looks 3 moves ahead.
 */
public class MinMaxHeuristicStrategy implements Strategy {

    private static final int DEPTH = 3;
    private final Boolean[] bools = {true, false};
    private int myPlayer;
    private int oppoPlayer;

    /**
     * @return the name of the strategy
     */
    //@ pure
    @Override
    public String getName() {
        return "Min Max Heuristics";
    }

    /**
     * Determines a move according to the min max strategy with smarter heuristics.
     *
     * @param board  the current game board
     * @param marble the player's marble
     * @return a strategical move
     */
    /*@
        requires board != null && marble != Marble.EMPTY;
        ensures board.isEmptyField(\result.getPosition());
    */
    //@ pure
    @Override
    public Move determineMove(Board board, Marble marble) {
        myPlayer = marble == Marble.BLACK ? 0 : 1;
        oppoPlayer = myPlayer == 0 ? 1 : 0;

        Move miniMax = firstBranch(board, marble);
        if (miniMax == null) {
            return randomMove(board);
        }
        return miniMax;
    }

    private int centerMarble(int[] board) {
        int score = 0;
        // Look middle coordinate (1,1), (4,4), (1,4), (4,1)
        if (board[7] == myPlayer) {
            score += 5;
        }
        if (board[10] == myPlayer) {
            score += 5;
        }
        if (board[25] == myPlayer) {
            score += 5;
        }
        if (board[28] == myPlayer) {
            score += 5;
        }
        if (board[7] == oppoPlayer) {
            score -= 5;
        }
        if (board[10] == oppoPlayer) {
            score -= 5;
        }
        if (board[25] == oppoPlayer) {
            score -= 5;
        }
        if (board[28] == oppoPlayer) {
            score -= 5;
        }
        return score;
    }

    private int calConnected(int connected, int look) {
        int score = 0;
        if (look != 2 && connected >= 3) {
            if (connected == 3) {
                score += look == myPlayer ? 100 : -100;
            } else if (connected == 4) {
                score += look == myPlayer ? 1200 : -1200;
            }
            return score;
        }
        return score;
    }

    private int connectedX(int[] board) {
        int score = 0;
        for (int row = 0; row < 6; row++) {
            int connected = 1;
            int look = board[row * 6];
            for (int col = 1; col < 6; col++) {
                int m = board[(row * 6) + col];
                if (m == look) {
                    connected++;
                } else {
                    if (connected >= 3) {
                        if (connected == 3) {
                            score += calConnected(connected, look);
                        } else {
                            break;
                        }
                    }
                    look = m;
                    connected = 1;
                }
            }
            score += calConnected(connected, look);
        }
        return score;
    }

    private int connectedY(int[] board) {
        int score = 0;
        for (int col = 0; col < Board.DIM; col++) {
            int connected = 1;
            int look;
            look = board[col];
            for (int row = 1; row < Board.DIM; row++) {
                int m = board[row * 6 + col];
                if (m == look) {
                    connected++;
                } else {
                    if (connected >= 3) {
                        if (connected == 3) {
                            score += calConnected(connected, look);
                        } else {
                            break;
                        }
                    }
                    look = m;
                    connected = 1;
                }
            }
            score += calConnected(connected, look);
        }
        return score;
    }

    private int longDownXY(int[] board) {
        int score = 0;
        // Offset (0,0) (0,1) (1,0) (1,1)
        // for (0,0)
        int connected = 1;
        int look = board[0];
        for (int i = 1; i < 36; i += 7) {
            int m = board[i];
            if (m == look) {
                connected++;
            } else {
                if (connected >= 3) {
                    if (connected == 3) {
                        score += calConnected(connected, look);
                    } else {
                        break;
                    }
                }
                look = m;
                connected = 1;
            }
        }
        score += calConnected(connected, look);
        return score;
    }

    private int shortDownXY(int[] board) {
        int score = 0;
        // for (1,0)
        int connected = 1;
        int look = board[6];
        for (int i = 1; i < 5; i++) {
            int m = board[((i + 1) * 6) + i];
            if (m == look) {
                connected++;
            } else {
                if (connected >= 3) {
                    score += calConnected(connected, look);
                    connected = 0;
                    break;
                }
                look = m;
                connected = 1;
            }
        }
        score += calConnected(connected, look);
        // for (0,1)
        connected = 1;
        look = board[1];
        for (int i = 1; i < 5; i++) {
            int m = board[i * 6 + i + 1];
            if (m == look) {
                connected++;
            } else {
                if (connected >= 3) {
                    score += calConnected(connected, look);
                    connected = 0;
                    break;
                }
                look = m;
                connected = 1;
            }
        }
        score += calConnected(connected, look);
        return score;
    }

    private int longUpXY(int[] board) {
        int score = 0;
        int connected = 1;
        // offset (5,0)
        int look = board[30];
        for (int i = 4; i >= 0; i--) {
            int m = board[i * 6 + Math.abs(i - 5)];
            if (m == look) {
                connected++;
            } else {
                if (connected >= 3) {
                    if (connected == 3) {
                        score += calConnected(connected, look);
                    } else {
                        break;
                    }
                }
                look = m;
                connected = 1;
            }
        }
        score += calConnected(connected, look);
        return score;
    }

    private int shortUpXY(int[] board) {
        int score = 0;
        // for (5,1)
        int connected = 1;
        int look = board[31];
        for (int i = 4; i >= 1; i--) {
            int m = board[i * 6 + Math.abs(6 - i)];
            if (m == look) {
                connected++;
            } else {
                if (connected >= 3) {
                    score += calConnected(connected, look);
                    connected = 1;
                    break;
                }
                look = m;
                connected = 1;
            }
        }
        score += calConnected(connected, look);
        // for (4,0)
        connected = 1;
        look = board[24];
        for (int i = 4; i >= 1; i--) {
            int m = board[((i - 1) * 6) + Math.abs(5 - i)];
            if (m == look) {
                connected++;
            } else {
                if (connected >= 3) {
                    score += calConnected(connected, look);
                    connected = 1;
                    break;
                }
                look = m;
                connected = 1;
            }
        }
        score += calConnected(connected, look);
        return score;
    }

    private int connectedXY(int[] board) {
        int score = 0;
        score += longUpXY(board);
        score += shortUpXY(board);
        score += longDownXY(board);
        score += shortDownXY(board);
        return score;
    }

    private int evaluation(int[] board) {
        boolean myWin = isWinner(board, myPlayer);
        boolean oppoWin = isWinner(board, oppoPlayer);
        if (myWin && oppoWin || isFull(board)) {
            return 0;
        } else if (myWin) {
            return Integer.MAX_VALUE;
        } else if (oppoWin) {
            return Integer.MIN_VALUE;
        }
        // Marble in the middle worth 5
        // 5 in a row worth 100,000
        // 4 in a row worth 1,000
        // 3 in a row worth 100
        int score = 0;
        score += centerMarble(board);
        // Horizontal
        score += connectedX(board);
        // Vertical
        score += connectedY(board);
        // DiagonalDown
        score += connectedXY(board);

        return score;
    }

    private int minimax(int[] board, int depth, int alpha, int beta, boolean maximizingPlayer) {
//        if (myWin && oppoWin || isFull(board)) {
//            return 0;
//        } else if (myWin) {
//            return Integer.MAX_VALUE;
//        } else if (oppoWin) {
//            return Integer.MIN_VALUE;
        if (depth == 0 || isGameOver(board)) {
            return evaluation(board);
        } else if (maximizingPlayer) {
            // When depth is more than 0 and maximizing
            List<int[]> boards = possibleBoard(board, myPlayer);
            int newAlpha = alpha;
            for (int[] tempBoard : boards) {
                int score = minimax(tempBoard, depth - 1, alpha, beta, false);
                if (score > beta) {
                    return beta;
                }
                newAlpha = Math.max(newAlpha, score);
            }
            return newAlpha;
        } else {
            // When depth is more than 0 and minimize
            int newBeta = beta;
            List<int[]> boards = possibleBoard(board, oppoPlayer);
            for (int[] tempBoard : boards) {
                int score = minimax(tempBoard, depth - 1, alpha, beta, true);
                if (score <= alpha) {
                    return alpha;
                }
                newBeta = Math.min(newBeta, score);
            }
            return newBeta;
        }
    }

    private List<int[]> possibleBoard(int[] board, int player) {
        List<int[]> boards = new ArrayList<>();
        for (int i = 0; i < 36; i++) {
            // check board is empty
            if (board[i] == 2) {
                int[] placeField = deepCopy(board);
                placeField[i] = player;
                for (int q = 0; q < 4; q++) {
                    for (Boolean bool : bools) {
                        int[] tempBoard = deepCopy(placeField);
                        rotate(tempBoard, q, bool);
                        boards.add(tempBoard);
                    }
                }
            }
        }
        return boards;
    }


    private Move firstBranch(Board board, Marble marble) {
        int bestScore = Integer.MIN_VALUE;
        Move bestMove = null;
        for (int i = 0; i < 36; i++) {
            if (board.isEmptyField(i)) {
                Board placeField = board.deepCopy();
                placeField.setField(i, marble);
                for (Quadrant q : Quadrant.values()) {
                    for (Boolean bool : bools) {
                        Board tempBoard = placeField.deepCopy();
                        tempBoard.rotate(q, bool);
                        int score = minimax(convertBoard(tempBoard),
                                DEPTH - 1, -10000000, 1000000, false);
                        if (score > bestScore) {
                            bestScore = score;
                            bestMove = new Move(i, new Rotation(q, bool));
                        }
                    }
                }
            }
        }
        return bestMove;
    }


    private int[] convertBoard(Board board) {
        int[] converted = new int[36];
        for (int i = 0; i < 36; i++) {
            if (board.getField(i) == Marble.BLACK) {
                converted[i] = 0;
            } else if (board.getField(i) == Marble.WHITE) {
                converted[i] = 1;
            } else {
                converted[i] = 2;
            }
        }
        return converted;
    }

    private boolean has5Col(int[] board, int player) {
        for (int col = 0; col < 6; col++) {
            int connect = 0;

            for (int row = 0; row < 6; row++) {
                if (board[row * 6 + col] == player) {
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

    private boolean has5Row(int[] board, int player) {
        for (int row = 0; row < 6; row++) {
            int connect = 0;

            for (int col = 0; col < 6; col++) {
                if (board[row * 6 + col] == player) {
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

    private boolean has5InUpDiagonal(int[] board, int player) {
        boolean has = true;
        int[] offset = {35, 34, 29, 28};
        for (int j = 0; j < 4; j++) {
            for (int i = 4; i >= 0; i--) {
                if (board[offset[j] - (i * 7)] != player) {
                    has = false;
                    break;
                }
            }
            if (has) {
                return true;
            }
        }
        return false;
    }

    private boolean has5InDownDiagonal(int[] board, int player) {
        boolean has = true;
        int[] offset = {0, 1, 6, 7};
        for (int j = 0; j < 4; j++) {
            for (int i = 0; i < 5; i++) {
                if (board[i * 7 + offset[j]] != player) {
                    has = false;
                    break;
                }
            }
            if (has) {
                return true;
            }
        }
        return false;
    }

    private boolean has5Diagonal(int[] board, int player) {
        return has5InDownDiagonal(board, player) || has5InUpDiagonal(board, player);
    }

    private boolean isWinner(int[] board, int player) {
        return has5Row(board, player) || has5Col(board, player) || has5Diagonal(board, player);
    }

    private boolean hasWinner(int[] board) {
        return isWinner(board, 0) || isWinner(board, 1);
    }

    private boolean isGameOver(int[] board) {
        return isDraw(board) || hasWinner(board);
    }

    private boolean isDraw(int[] board) {
        if (isFull(board)) {
            boolean blackWins = isWinner(board, 0);
            boolean whiteWins = isWinner(board, 1);
            // Check whether there is only 1 winner, in this case there is no draw
            // Otherwise (both win or none), it is a draw
            return !(blackWins && !whiteWins || whiteWins && !blackWins);
        } else {
            // Board is not full, so not a draw
            return false;
        }
    }

    private boolean isFull(int[] board) {
        return getNumberOfEmptySpots(board) == 0;
    }

    private int getNumberOfEmptySpots(int[] board) {
        int count = 0;
        for (int i = 0; i < 36; i++) {
            if (board[i] == 2) {
                count++;
            }
        }
        return count;
    }

    private int[] deepCopy(int[] board) {
        int[] copy = new int[36];
        System.arraycopy(board, 0, copy, 0, 36);
        return copy;
    }

    // Quadrant 0 = tl, 1 = tr and so on
    private int[] getOffset(int quadrant) {
        if (quadrant == 1) {
            return new int[]{0, 0};
        } else if (quadrant == 2) {
            return new int[]{0, 3};
        } else if (quadrant == 3) {
            return new int[]{3, 0};
        } else {
            return new int[]{3, 3};
        }
    }

    private void rotate(int[] board, int quadrant, boolean clockwise) {
        int[] offset = getOffset(quadrant);
        int yo = offset[0];
        int xo = offset[1];

        // flip quadrant by line x = y
        for (int i = 0; i < 3; i++) {
            for (int j = i; j < 3; j++) {
                int cor = ((i + yo) * 6) + j + xo;
                int temp = board[cor];
                int cor2 = ((j + yo) * 6) + i + xo;
                board[cor] = board[cor2];
                board[cor2] = temp;
            }
        }

        if (clockwise) {
            // flip quadrant by line x = 0 when center of quadrant is (0,0)
            for (int i = 0; i < 3; i++) {
                int cor = ((i + yo) * 6) + xo;
                int cor2 = (i + yo * 6) + xo + 2;
                int temp = board[cor];
                board[cor] = board[cor2];
                board[cor2] = temp;
            }

        } else {
            // flip quadrant by line y = 0 when center of quadrant is (0,0)
            for (int i = 0; i < 3; i++) {
                int cor = (yo * 6) + xo + i;
                int temp = board[cor];
                int cor2 = ((yo + 2) * 6) + xo + i;
                board[cor] = board[cor2];
                board[cor2] = temp;
            }
        }
    }
}
