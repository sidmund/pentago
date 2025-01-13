package ss.pentago.model.player;

import ss.pentago.model.player.ai.*;
import ss.pentago.model.player.strategy.*;
import ss.pentago.tui.menu.TUIInputField;
import ss.pentago.tui.menu.TUIMenu;
import ss.pentago.tui.menu.TUIMenuOption;

import java.util.Scanner;

/**
 * Factory class for Player generation.
 */
public class PlayerFactory {

    public static final int MIN_AI_DIFFICULTY = 1;
    public static final int MAX_AI_DIFFICULTY = 4;

    private PlayerFactory() {
    }

    // -- Human players ----

    /**
     * Create a new {@code HumanPlayer} with specified name,
     * hint AI and number of hints available.
     *
     * @param name   the player name
     * @param hinter the hint AI strategy
     * @param hints  the number of hints
     * @return new {@code HumanPlayer}
     */
    //@ requires name != null && hinter != null && hints >= 0;
    //@ ensures \result.getName().equals(name);
    public static HumanPlayer makeHumanPlayer(String name, Strategy hinter, int hints) {
        return new HumanPlayer(name, hinter, hints);
    }

    /**
     * Create a new dummy {@code HumanPlayer} with default name,
     * by default having 3 hints available and using NaiveAI as hint AI.
     * This is meant to be used by the Client to later set the username,
     * and be able to configure AI's after connecting to the server.
     *
     * @return new {@code HumanPlayer}
     */
    public static HumanPlayer makeDummyHumanPlayer() {
        return makeHumanPlayer("Dummy", makeNaiveStrategy(), 3);
    }

    /**
     * Create a new {@code HumanPlayer} with specified name,
     * by default having 3 hints available and using NaiveAI as hint AI.
     *
     * @param name the player name
     * @return new {@code HumanPlayer}
     */
    //@ requires name != null;
    //@ ensures \result.getName().equals(name);
    public static HumanPlayer makeHumanPlayer(String name) {
        return makeHumanPlayer(name, makeNaiveStrategy(), 3);
    }

    /**
     * Enter the player's name and create a new {@code HumanPlayer},
     * by default having 3 hints available and using NaiveAI as hint AI.
     *
     * @param scanner     the scanner
     * @param defaultName the name to use as default
     * @return new {@code HumanPlayer}
     */
    //@ requires scanner != null;
    public static HumanPlayer makeHumanPlayerFromInput(Scanner scanner, String defaultName) {
        return makeHumanPlayer(TUIInputField.askForString("What's your name?",
                defaultName, scanner));
    }

    /**
     * Enter the player's name and amount of hints,
     * and create a new {@code HumanPlayer}.
     * The hint AI is a Naive AI by default.
     *
     * @param scanner   the scanner
     * @param hintCount the amount of hints
     * @return new {@code HumanPlayer}
     */
    //@ requires scanner != null;
    public static HumanPlayer makeHumanPlayerFromInput(Scanner scanner, int hintCount) {
        return makeHumanPlayerFromInput(scanner, makeNaiveStrategy(), hintCount);
    }

    /**
     * Enter the player's name, specify the type of hint AI and number of hints,
     * and create a new {@code HumanPlayer}.
     *
     * @param scanner   the scanner
     * @param hinter    the type of hint AI strategy
     * @param hintCount the amount of hints
     * @return new {@code HumanPlayer}
     */
    //@ requires scanner != null;
    public static HumanPlayer makeHumanPlayerFromInput(
            Scanner scanner, Strategy hinter, int hintCount) {
        return makeHumanPlayer(
                TUIInputField.askForString("What's your name?", "Alice", scanner),
                hinter, hintCount);
    }

    // -- AI Players ----

    /**
     * @return new {@code NaiveAI}
     */
    public static NaiveAI makeNaiveAI() {
        return new NaiveAI();
    }

    /**
     * @return new {@code EasyAI}
     */
    public static EasyAI makeEasyAI() {
        return new EasyAI();
    }

    /**
     * @return new {@code MediumAI}
     */
    public static MediumAI makeMediumAI() {
        return new MediumAI();
    }

    /**
     * @return new {@code HardAI}
     */
    public static HardAI makeHardAI() {
        return new HardAI();
    }

    /**
     * @return new {@code NaiveStrategy}
     */
    public static NaiveStrategy makeNaiveStrategy() {
        return new NaiveStrategy();
    }

    /**
     * @return new {@code DirectWinStrategy}
     */
    public static DirectWinStrategy makeEasyStrategy() {
        return new DirectWinStrategy();
    }

    /**
     * @return new {@code MinMaxStrategy}
     */
    public static MinMaxStrategy makeMediumStrategy() {
        return new MinMaxStrategy();
    }

    /**
     * @return new {@code MinMaxHeuristicStrategy}
     */
    public static MinMaxHeuristicStrategy makeHardStrategy() {
        return new MinMaxHeuristicStrategy();
    }

    /**
     * Creates a new {@code AIPlayer} of specified difficulty.
     *
     * @param difficulty the difficulty
     * @return new {@code AIPlayer}
     */
    //@ requires difficulty >= MIN_AI_DIFFICULTY && difficulty < MAX_AI_DIFFICULTY;
    public static AIPlayer makeAI(int difficulty) {
        switch (difficulty) {
            case 4:
                return makeHardAI();
            case 3:
                return makeMediumAI();
            case 2:
                return makeEasyAI();
            case 1:
            default:
                return makeNaiveAI();
        }
    }

    /**
     * Creates a new {@code Strategy} of specified difficulty.
     *
     * @param difficulty the difficulty
     * @return new {@code Strategy}
     */
    //@ requires difficulty >= MIN_AI_DIFFICULTY && difficulty < MAX_AI_DIFFICULTY;
    public static Strategy makeAIStrategy(int difficulty) {
        switch (difficulty) {
            case 4:
                return makeHardStrategy();
            case 3:
                return makeMediumStrategy();
            case 2:
                return makeEasyStrategy();
            case 1:
            default:
                return makeNaiveStrategy();
        }
    }

    /**
     * Select the AI difficulty and create a new {@code AIPlayer}.
     *
     * @param menuTitle the title for the selecting AI difficulty menu
     * @param scanner   the scanner
     * @return new {@code AIPlayer}
     */
    //@ requires menuTitle != null && scanner != null;
    public static AIPlayer selectAIFromDifficultyMenu(String menuTitle, Scanner scanner) {
        final AIPlayer[] ai = new AIPlayer[1];
        new TUIMenu(menuTitle)
                .add(new TUIMenuOption("Naive") {
                    @Override
                    public void execute() {
                        ai[0] = makeAI(1);
                    }
                })
                .add(new TUIMenuOption("Easy") {
                    @Override
                    public void execute() {
                        ai[0] = makeAI(2);
                    }
                })
                .add(new TUIMenuOption("Medium") {
                    @Override
                    public void execute() {
                        ai[0] = makeAI(3);
                    }
                })
                .add(new TUIMenuOption("Hard") {
                    @Override
                    public void execute() {
                        ai[0] = makeAI(4);
                    }
                })
                .run(scanner);
        return ai[0];
    }
}
