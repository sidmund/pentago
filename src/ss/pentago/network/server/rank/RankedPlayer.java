package ss.pentago.network.server.rank;

import java.util.Objects;

/**
 * RankedPlayer represents a Player's gameplay stats. It provides
 * methods for updating and querying their stats.
 */
public class RankedPlayer implements Comparable<RankedPlayer> {

    private final String username;

    private static final int INITIAL_ELO = 800;
    private int elo;

    /**
     * K is a constant used for ELO calculation. 30 by default.
     * If K is lower, the rating changes by a smaller fraction that if K were to be higher.
     */
    private static final int K = 30;

    private int totalGamesPlayed = 0;
    private int totalGamesWon = 0;

    /**
     * Create a new RankedPlayer with their ELO score set to {@link #INITIAL_ELO} by default.
     *
     * @param username the name of the player
     */
    public RankedPlayer(String username) {
        this.username = username;
        elo = INITIAL_ELO;
    }

    /**
     * Update the ELO score. Algorithm adapted from
     * <a href="https://www.geeksforgeeks.org/elo-rating-algorithm/">geeksforgeeks.org</a>.
     *
     * @param eloOpponent the opponent's ELO score
     * @param win         whether the match was a win
     */
    public void updateElo(int eloOpponent, boolean win) {
        double expected = 1.0 / (1.0 + Math.pow(10, (elo - eloOpponent) / 400.0));
        elo += K * ((win ? 1 : 0) - expected);

        totalGamesPlayed++;
        if (win) {
            totalGamesWon++;
        }
    }

    /**
     * @return the username
     */
    public String getUsername() {
        return username;
    }

    /**
     * @return the ELO score
     */
    public int getElo() {
        return elo;
    }

    /**
     * @return the win rate as a percentage
     */
    public int getWinRate() {
        return totalGamesPlayed == 0 ? 0 : (totalGamesWon * 100 / totalGamesPlayed);
    }

    /**
     * @return the total number of games played
     */
    public int getTotalGamesPlayed() {
        return totalGamesPlayed;
    }

    /**
     * @return the total number of games won
     */
    public int getTotalGamesWon() {
        return totalGamesWon;
    }

    /**
     * Comparison is reversed, so the RankedPlayers will get sorted in descending order by default.
     *
     * @param o the RankedPlayer to compare to
     * @return 0 if equal, -1 if this value is bigger, 1 if this value is smaller
     */
    @Override
    public int compareTo(RankedPlayer o) {
        return Integer.compare(o.elo, elo);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }

        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        RankedPlayer that = (RankedPlayer) o;
        return elo == that.elo && totalGamesPlayed == that.totalGamesPlayed
                && totalGamesWon == that.totalGamesWon && Objects.equals(username, that.username);
    }

    @Override
    public int hashCode() {
        return Objects.hash(username, elo, totalGamesPlayed, totalGamesWon);
    }
}
