package ss.pentago.tui.menu;

import ss.pentago.TUIClientLauncher;
import ss.pentago.file.Config;
import ss.pentago.file.FileHandler;
import ss.pentago.model.player.Player;
import ss.pentago.model.player.PlayerFactory;
import ss.pentago.tui.skin.BoardGridCharacter;
import ss.pentago.tui.skin.BoardGridStyle;
import ss.pentago.tui.skin.BoardSkin;
import ss.pentago.tui.skin.MarbleStyle;
import ss.pentago.util.LoggingLevel;
import ss.pentago.util.Randomizer;

import java.util.Map;
import java.util.Scanner;

/**
 * TUIClientMenus acts as a utility class to hold and run various configuration menus.
 */
public class TUIMenus {

    // SonarLint can't complain now
    private static final String BACK_TO_MAIN = "Back to main menu";
    private static final String KEEP_CURRENT = "Keep current: ";
    private static final String LOCALHOST = "localhost";

    private TUIMenus() {
    }

    /**
     * After selecting game play mode, choose who goes first.
     *
     * @param scanner the scanner to read input from
     * @param p1      the first player
     * @param p2      the second player
     */
    //@ requires scanner != null && p1 != null && p2 != null;
    private static void choosePlayOrder(Scanner scanner, Player p1, Player p2) {
        // Choose player order and play
        new TUIMenu("CHOOSE PLAY ORDER")
                .add(new TUIMenuOption("First entered player goes first") {
                    @Override
                    public void execute() {
                        TUIClientLauncher.playOffline(p1, p2, false);
                    }
                })
                .add(new TUIMenuOption("Second entered player goes first") {
                    @Override
                    public void execute() {
                        TUIClientLauncher.playOffline(p2, p1, false);
                    }
                })
                .add(new TUIMenuOption("Random") {
                    @Override
                    public void execute() {
                        TUIClientLauncher.playOffline(p1, p2, true);
                    }
                })
                .run(scanner);
    }

    /**
     * Select game play mode, either "Human vs Human", "Human vs AI", or "AI vs AI".
     *
     * @param scanner the scanner to get input from
     */
    //@ requires scanner != null;
    private static void playOffline(Scanner scanner) {
        new TUIMenu("HOW TO PLAY")
                .add(new TUIMenuOption("Human vs Human") {
                    @Override
                    public void execute() {
                        // make two human players with 0 hints each
                        choosePlayOrder(scanner,
                                PlayerFactory.makeHumanPlayerFromInput(scanner, "Alice"),
                                PlayerFactory.makeHumanPlayerFromInput(scanner, "Bob")
                        );
                    }
                })
                .add(new TUIMenuOption("Human vs AI") {
                    @Override
                    public void execute() {
                        // human player have 3 hints because they're playing against AI
                        choosePlayOrder(scanner,
                                PlayerFactory.makeHumanPlayerFromInput(scanner, 3),
                                PlayerFactory.selectAIFromDifficultyMenu("SELECT AI", scanner)
                        );
                    }
                })
                .add(new TUIMenuOption("AI vs AI") {
                    @Override
                    public void execute() {
                        choosePlayOrder(scanner,
                                PlayerFactory.selectAIFromDifficultyMenu(
                                        "SELECT FIRST AI", scanner),
                                PlayerFactory.selectAIFromDifficultyMenu(
                                        "SELECT SECOND AI", scanner)
                        );
                    }
                })
                .add(new TUIMenuOption(BACK_TO_MAIN) {
                    @Override
                    public void execute() {
                        // do nothing, just exit, will go back automatically
                    }
                })
                .run(scanner);
    }

    /**
     * Select a localhost server configuration, or specify a manual port.
     *
     * @param scanner the scanner to read input from
     * @return -1 when the user quit, a port number between 0-65536 otherwise
     */
    //@ requires scanner != null;
    public static int showServerPortMenu(Scanner scanner) {
        final int[] ports = new int[1];

        TUIMenu profiles = new TUIMenu("SELECT PORT TO RUN THIS 'LOCALHOST' SERVER AT");
        for (Map.Entry<String, String> profile : Config.getServerProfiles()) {
            if (profile.getValue().split(":")[0].equals(LOCALHOST)) {
                profiles.add(new TUIMenuOption(
                        String.format("%s (%s)", profile.getKey(), profile.getValue())) {
                    @Override
                    public void execute() {
                        ports[0] = Integer.parseInt(profile.getValue().split(":")[1]);
                    }
                });
            }
        }
        profiles.add(new TUIMenuOption("Configure manually") {
            @Override
            public void execute() {
                int port = TUIInputField.askForNumber("Server port, '0' for random free port",
                        0, 65536, 0, scanner);

                if (TUIInputField.askForBoolean("Store this server profile?", false, scanner)) {
                    String name = TUIInputField.askForString("Profile name?",
                            String.format("Server%d", Randomizer.randomInt(100)), scanner);
                    Config.addServerProfile(name, String.format("%s:%d", LOCALHOST, port));
                    FileHandler.saveConfig();
                }

                ports[0] = port;
            }
        });
        profiles.add(new TUIMenuOption("Quit") {
            @Override
            public void execute() {
                ports[0] = -1;
            }
        });
        profiles.run(scanner);

        return ports[0];
    }

    /**
     * Select a connection profile or configure the connection manually.
     *
     * @param scanner the scanner to read input from
     */
    //@ requires scanner != null;
    public static void showServerMenu(Scanner scanner) {
        TUIMenu profiles = new TUIMenu("SELECT SERVER CONFIGURATION");
        for (Map.Entry<String, String> profile : Config.getServerProfiles()) {
            profiles.add(new TUIMenuOption(
                    String.format("%s (%s)", profile.getKey(), profile.getValue())) {
                @Override
                public void execute() {
                    String[] address = profile.getValue().split(":");

                    Player player = showPlayOption(scanner);
                    if (TUIClientLauncher.playOnline(player,
                            address[0], Integer.parseInt(address[1]))) {
                        showServerMenu(scanner);
                    }
                }
            });
        }
        profiles.add(new TUIMenuOption("Configure manually") {
            @Override
            public void execute() {
                String hostname = TUIInputField.askForString("Server host name?",
                        LOCALHOST, scanner);
                int port = TUIInputField.askForNumber("Server port",
                        0, 65536, 0, scanner);

                if (TUIInputField.askForBoolean("Store this server profile?", false, scanner)) {
                    String name = TUIInputField.askForString("Profile name?",
                            String.format("Server%d", Randomizer.randomInt(100)), scanner);
                    Config.addServerProfile(name, String.format("%s:%d", hostname, port));
                    FileHandler.saveConfig();
                }

                Player player = showPlayOption(scanner);
                if (TUIClientLauncher.playOnline(player, hostname, port)) {
                    showServerMenu(scanner);
                }
            }
        });
        profiles.add(new TUIMenuOption(BACK_TO_MAIN) {
            @Override
            public void execute() {
                showMainMenu();
            }
        });
        profiles.run(scanner);
    }

    /**
     * Select the Board grid style.
     *
     * @param scanner the scanner to get input from
     */
    //@ requires scanner != null;
    private static void showGridStyleMenu(Scanner scanner) {
        TUIMenu gridStyleMenu = new TUIMenu("BOARD SKIN - GRID STYLE");
        for (BoardGridStyle gridStyle : BoardGridStyle.values()) {
            gridStyleMenu.add(new TUIMenuOption(String.format("%s%n%s", gridStyle,
                    new BoardSkin(gridStyle,
                            Config.BOARD_SKIN.getGridCharacter(),
                            Config.BOARD_SKIN.getAltGridCharacter(),
                            Config.BOARD_SKIN.getMarbleStyle(),
                            Config.BOARD_SKIN.hideNotation())
                            .getPreview(6))) {
                @Override
                public void execute() {
                    Config.BOARD_SKIN.setBoardGridStyle(gridStyle);
                }
            });
        }
        gridStyleMenu.add(new TUIMenuOption(
                String.format("%s%s", KEEP_CURRENT, Config.BOARD_SKIN.getBoardGridStyle())) {
            @Override
            public void execute() {
                // ignore
            }
        });
        gridStyleMenu.run(scanner);
    }

    /**
     * Select whether to show the "chess" notation along the side of the Board.
     *
     * @param scanner the scanner to get input from
     */
    //@ requires scanner != null;
    private static void showNotationMenu(Scanner scanner) {
        new TUIMenu("BOARD SKIN - NOTATION")
                .add(new TUIMenuOption("Show notation") {
                    @Override
                    public void execute() {
                        Config.BOARD_SKIN.setHideNotation(false);
                    }
                })
                .add(new TUIMenuOption("Hide notation") {
                    @Override
                    public void execute() {
                        Config.BOARD_SKIN.setHideNotation(true);
                    }
                })
                .add(new TUIMenuOption(String.format("%s%s", KEEP_CURRENT,
                        Config.BOARD_SKIN.hideNotation() ? "Hide" : "Show")) {
                    @Override
                    public void execute() {
                        // ignore
                    }
                })
                .run(scanner);
    }

    /**
     * Select the characters used in drawing the Board grid.
     *
     * @param scanner        the scanner to get input from
     * @param title          the title of the menu
     *                       (menu is used twice, for both main character and alt character)
     * @param isAltCharacter whether this menu is about the alt or the main character
     */
    //@ requires scanner != null && title != null;
    private static void showGridCharacterMenu(
            Scanner scanner, String title, boolean isAltCharacter) {
        TUIMenu gridCharMenu = new TUIMenu(title);
        for (BoardGridCharacter character : BoardGridCharacter.values()) {
            gridCharMenu.add(new TUIMenuOption(character.toString()) {
                @Override
                public void execute() {
                    if (isAltCharacter) {
                        Config.BOARD_SKIN.setAltGridCharacter(character);
                    } else {
                        Config.BOARD_SKIN.setGridCharacter(character);
                    }
                }
            });
        }
        gridCharMenu.add(new TUIMenuOption(String.format("%s%s",
                KEEP_CURRENT, isAltCharacter
                        ? Config.BOARD_SKIN.getAltGridCharacter()
                        : Config.BOARD_SKIN.getGridCharacter())) {
            @Override
            public void execute() {
                // ignore
            }
        });
        gridCharMenu.run(scanner);
    }

    /**
     * Select which Marble style to use.
     *
     * @param scanner the scanner to get input from
     */
    //@ requires scanner != null;
    private static void showSkinMenu(Scanner scanner) {
        TUIMenu gridCharMenu = new TUIMenu("BOARD SKIN - MARBLE STYLE");
        for (MarbleStyle marbleStyle : MarbleStyle.values()) {
            gridCharMenu.add(new TUIMenuOption(marbleStyle.toString()) {
                @Override
                public void execute() {
                    Config.BOARD_SKIN.setMarbleStyle(marbleStyle);

                    // ask for grid characters
                    showGridCharacterMenu(scanner, "BOARD SKIN - GRID CHARACTER 1", false);
                    showGridCharacterMenu(scanner, "BOARD SKIN - GRID CHARACTER 2", true);

                    // ask for notation
                    showNotationMenu(scanner);

                    // ask for grid style
                    showGridStyleMenu(scanner);
                }
            });
        }
        gridCharMenu.add(new TUIMenuOption(
                String.format("%s%s", KEEP_CURRENT, Config.BOARD_SKIN.getMarbleStyle())) {
            @Override
            public void execute() {
                // ask for grid characters
                showGridCharacterMenu(scanner, "BOARD SKIN - GRID CHARACTER 1", false);
                showGridCharacterMenu(scanner, "BOARD SKIN - GRID CHARACTER 2", true);

                // ask for notation
                showNotationMenu(scanner);

                // ask for grid style
                showGridStyleMenu(scanner);
            }
        });
        gridCharMenu.run(scanner);
    }

    private static void showExtensionsMenu(Scanner scanner) {
        TUIMenu extensions = new TUIMenu("MULTI PLAYER EXTENSIONS\n" +
                "    NB: the server must also support them to actually work");
        if (Config.CLIENT_CHAT_IMPLEMENTED) {
            extensions.add(new TUIMenuOption(
                    String.format("Chat: %s",
                            Config.doesClientSupportChat() ? "on" : "off")) {
                @Override
                public void execute() {
                    Config.setClientChatSupport(TUIInputField.askForBoolean(
                            "Enable chat support?",
                            true, scanner));
                    FileHandler.saveConfig();
                }
            });
        }
        if (Config.CLIENT_RANK_IMPLEMENTED) {
            extensions.add(new TUIMenuOption(
                    String.format("Leaderboard: %s",
                            Config.doesClientSupportRank() ? "on" : "off")) {
                @Override
                public void execute() {
                    Config.setClientRankSupport(TUIInputField.askForBoolean(
                            "Enable leaderboard support?", true, scanner));
                    FileHandler.saveConfig();
                }
            });
        }
        if (Config.CLIENT_AUTH_IMPLEMENTED) {
            extensions.add(new TUIMenuOption(
                    String.format("Authentication: %s",
                            Config.doesClientSupportAuth() ? "on" : "off")) {
                @Override
                public void execute() {
                    Config.setClientAuthSupport(TUIInputField.askForBoolean(
                            "Enable authentication support?", true, scanner));
                    FileHandler.saveConfig();
                }
            });
        }
        if (Config.CLIENT_CRYPT_IMPLEMENTED) {
            extensions.add(new TUIMenuOption(
                    String.format("Encryption: %s",
                            Config.doesClientSupportCrypt() ? "on" : "off")) {
                @Override
                public void execute() {
                    Config.setClientCryptSupport(TUIInputField.askForBoolean(
                            "Enable encryption support?", true, scanner));
                    FileHandler.saveConfig();
                }
            });
        }
        extensions.add(new TUIMenuOption("Back to Options") {
            @Override
            public void execute() {
                showOptionsMenu(scanner);
            }
        });
        extensions.run(scanner);
    }

    /**
     * Configure game options.
     *
     * @param scanner the scanner to get input from
     */
    //@ requires scanner != null;
    private static void showOptionsMenu(Scanner scanner) {
        TUIMenu options = new TUIMenu("OPTIONS");
        options.add(new TUIMenuOption(
                String.format("Change AI single player delay (currently %d ms)",
                        Config.getResponseDelaySinglePlayer())) {
            @Override
            public void execute() {
                Config.setResponseDelaySinglePlayer(
                        TUIInputField.askForNumber("AI single player delay",
                                0, 100000, 1000, scanner));
                FileHandler.saveConfig();
            }
        });
        options.add(new TUIMenuOption(
                String.format("Change AI multi player delay (currently %d ms)",
                        Config.getResponseDelayMultiPlayer())) {
            @Override
            public void execute() {
                Config.setResponseDelayMultiPlayer(
                        TUIInputField.askForNumber("AI multi player delay",
                                0, 100000, 1000, scanner));
                FileHandler.saveConfig();
            }
        });
        options.add(new TUIMenuOption(
                String.format("Change delay to disconnect opponent (currently %d ms)",
                        Config.getTimeUntilDisconnect())) {
            @Override
            public void execute() {
                Config.setTimeUntilDisconnect(
                        TUIInputField.askForNumber("Disconnect opponent delay",
                                0, 1000000000, 30000, scanner));
                FileHandler.saveConfig();
            }
        });
        options.add(new TUIMenuOption(
                String.format("Change logging level (currently '%s')",
                        Config.getLoggingLevel().toString())) {
            @Override
            public void execute() {
                Config.setLoggingLevel(
                        LoggingLevel.values()[TUIInputField.askForNumber(
                                "Logging level (lowest is show all, highest show nothing)",
                                1, LoggingLevel.values().length, 4, scanner) - 1]);
                FileHandler.saveConfig();
            }
        });
        options.add(new TUIMenuOption(
                String.format("Change board skin, current:%n%s",
                        Config.BOARD_SKIN.getPreview(6))) {
            @Override
            public void execute() {
                showSkinMenu(scanner);
                FileHandler.saveConfig();
            }
        });
        if (Config.CLIENT_AUTH_IMPLEMENTED || Config.CLIENT_CHAT_IMPLEMENTED
                || Config.CLIENT_RANK_IMPLEMENTED || Config.CLIENT_CRYPT_IMPLEMENTED) {
            options.add(new TUIMenuOption("Enable/Disable multi player extensions") {
                @Override
                public void execute() {
                    showExtensionsMenu(scanner);
                }
            });
        }
        options.add(new TUIMenuOption(BACK_TO_MAIN +
                "\n Note: If you want the default settings back, " +
                "just delete your config file") {
            @Override
            public void execute() {
                // do nothing, will go back automatically
            }
        });
        options.run(scanner);
    }

    /**
     * Displays menu to select how to run this client. <br>
     * 1. As a human, so the user has full control and can play games as they wish <br>
     * 2. As an AI, the client will run in automatic mode
     *
     * @param scanner the scanner to get the user's choice
     * @return the kind of player we want to play as
     */
    //@ requires scanner != null;
    public static Player showPlayOption(Scanner scanner) {
        final Player[] player = new Player[1];

        new TUIMenu("Play")
                .add(new TUIMenuOption("Manual") {
                    @Override
                    public void execute() {
                        player[0] = PlayerFactory.makeDummyHumanPlayer();
                    }
                })
                .add(new TUIMenuOption("Automatic") {
                    @Override
                    public void execute() {
                        player[0] = PlayerFactory.selectAIFromDifficultyMenu(
                                "Select AI Type", scanner);
                    }
                })
                .run(scanner);

        return player[0];
    }

    /**
     * Tells the user how to play the game.
     *
     * @param scanner the scanner to get the user's choice
     */
    //@ requires scanner != null;
    private static void showTutorial(Scanner scanner) {
        System.out.println("TUTORIAL - HOW TO PLAY PENTAGO");
        System.out.println();
        System.out.println("\tPentago has two players, black and white. Black goes first.");
        System.out.println();
        System.out.println("\tDuring the game, you place your marble anywhere you want.");
        System.out.println("\tYou do this by typing 'p' and specifying the position, like chess.");
        System.out.println("\tThen you rotate one of four sub boards.");
        System.out.println("\tYou do this by typing 'r' and specifying a sub board and direction.");
        System.out.println();
        System.out.println("\tYou win if you get 5 marbles in any row, column, or diagonal.");
        System.out.println("\tKeep in mind that you have to rotate after a placement, " +
                "so don't rejoice too soon!");
        System.out.println();
        System.out.println("\tYou can always type 'help' during gameplay to see what you can do.");
        System.out.println("\tAnd if you're stuck, you can always request a 'hint'.");
        System.out.println();
        TUIInputField.waitForEnter("Type 'Enter' to go back to the main menu", scanner);
    }

    /**
     * Show the Pentago main menu.
     */
    public static void showMainMenu() {
        // Make a new scanner each time when entering the main menu,
        // since returning from a game could have resulting in System.in having been closed
        Scanner scanner = new Scanner(System.in);

        new TUIMenu("WELCOME TO PENTAGO!")
                .add(new TUIMenuOption("Single player") {
                    @Override
                    public void execute() {
                        // launch the offline client and go back to main menu after game ends
                        playOffline(scanner);
                        showMainMenu();
                    }
                })
                .add(new TUIMenuOption("Multi player") {
                    @Override
                    public void execute() {
                        // setup the server connection and try to connect,
                        // go back to main menu after disconnect
                        showServerMenu(scanner);
                        showMainMenu();
                    }
                })
                .add(new TUIMenuOption("Options") {
                    @Override
                    public void execute() {
                        showOptionsMenu(scanner);
                        showMainMenu();
                    }
                })
                .add(new TUIMenuOption("Tutorial") {
                    @Override
                    public void execute() {
                        showTutorial(scanner);
                        showMainMenu();
                    }
                })
                .add(new TUIMenuOption("Quit") {
                    @Override
                    public void execute() {
                        /*
                            no threads or anything are running at this point,
                            this exit call is needed since some subroutines
                            of the main menu call showMainMenu and if we try to quit from it,
                            it will go back to where it left of at the submenu
                            even though nothing is left to do there
                         */
                        // once we quit the main menu, save the config
                        FileHandler.saveConfig();
                        System.exit(0);
                    }
                })
                .run(scanner);
    }
}
