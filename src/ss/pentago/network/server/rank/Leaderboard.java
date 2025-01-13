package ss.pentago.network.server.rank;

import java.util.*;

/**
 * Leaderboard represents the rankings on a Server.
 * It provides methods to query and update its status.
 */
public class Leaderboard {

    /**
     * The List to hold the rankings is kept sorted by ELO score.
     */
    private final List<RankedPlayer> rankings;

    /**
     * Create a new Leaderboard, initially empty.
     */
    public Leaderboard() {
        rankings = new ArrayList<>();
    }

    /**
     * Update the ELO scores of the winner and the loser.
     * If a user is not on the Leaderboard yet, they are added first.
     *
     * @param winner the winner
     * @param loser  the loser
     * @param isDraw whether it's a draw
     */
    /*@
    @ requires winner != null && loser != null && !winner.equals(loser);
    */
    public void updateRankings(String winner, String loser, boolean isDraw) {
        RankedPlayer p1 = getPlayer(winner);
        RankedPlayer p2 = getPlayer(loser);

        int p1Elo = p1.getElo();
        int p2Elo = p2.getElo();

        p1.updateElo(p2Elo, !isDraw);
        p2.updateElo(p1Elo, false);

        Collections.sort(rankings);
    }

    /**
     * Find the user by username in the database. If the user was not present,
     * they are added first and then returned.
     *
     * @param username player username
     * @return the RankedPlayer object with that username,
     * a new RankedPlayer if the user wasn't found
     */
    private RankedPlayer getPlayer(String username) {
        for (RankedPlayer rp : rankings) {
            if (rp.getUsername().equals(username)) {
                return rp;
            }
        }

        RankedPlayer rp = new RankedPlayer(username);
        rankings.add(rp);
        return rp;
    }

    /**
     * @return the set of ranked players sorted by their ELO scores
     */
    public List<RankedPlayer> getRankingSortedByElo() {
        return rankings;
    }
}
