package ss.pentago.file;

import ss.pentago.tui.skin.BoardGridCharacter;
import ss.pentago.tui.skin.BoardGridStyle;
import ss.pentago.tui.skin.BoardSkin;
import ss.pentago.tui.skin.MarbleStyle;
import ss.pentago.util.Logger;
import ss.pentago.util.LoggingLevel;

import java.io.*;
import java.util.Map;

/**
 * Handles storing and retrieving files on the user's system.
 * This is not covered by any tests,
 * because this is technically beyond the scope of this project.
 * However, it is found to be working by interacting with the TUI and game.
 */
public class FileHandler {

    private static final String CONFIG_FILENAME = "pentago.config";

    private static final char SECTION_MARKER = '#';
    private static final char SETTING_SEPARATOR = '=';
    private static final char VALUE_SEPARATOR = ',';

    private FileHandler() {
    }

    /**
     * Tries to parse the value to an int in the range 0 to max,
     * if that fails, return the defaultValue instead.
     *
     * @param setting      the setting whose value we are parsing
     * @param value        the string value to parse
     * @param max          the maximum (exclusive)
     * @param defaultValue the default value
     * @return the int value of the string value, otherwise the default value
     */
    //@ requires defaultValue >= 0 && defaultValue < max && setting != null && value != null;
    //@ ensures \result >= 0 && \result < max;
    private static int parseInt(String setting, String value, int max, int defaultValue) {
        try {
            int i = Integer.parseInt(value);
            if (i >= 0 && i < max) {
                return i;
            }
        } catch (NumberFormatException e) {
            // ignore
        }

        Logger.warn(FileHandler.class.getSimpleName(),
                "'%s' setting has an improper value: '%s', using default%n", setting, value);
        return defaultValue;
    }

    /**
     * Tries to parse multiple values to ints in the range 0 to max,
     * if that fails, it return defaultValues instead.
     *
     * @param setting       the setting whose values we are parsing
     * @param values        the string values to parse
     * @param max           the maximum (exclusive)
     * @param defaultValues the default values,
     *                      the length of this array indicates how many values we expect to parse
     * @return the int values of the string values, otherwise the default values
     */
    /*@
        requires setting != null;
        requires values != null && defaultValues != null && values.length == defaultValues.length;
        requires (\forall int i; i >= 0 && i < defaultValues.length;
                    defaultValues[i] >= 0 && defaultValues[i] < max);
        ensures \result.length == values.length;
    */
    private static int[] parseInts(
            String setting, String[] values, int max, int[] defaultValues) {
        if (values.length == defaultValues.length) {
            int[] results = new int[defaultValues.length];

            for (int i = 0; i < defaultValues.length; i++) {
                results[i] = parseInt(setting, values[i], max, defaultValues[i]);
            }

            return results;
        }

        return defaultValues;
    }

    /**
     * Helper method to parse a line containing a BoardSkin related setting.
     *
     * @param line the line to parse
     */
    //@ requires line != null;
    private static void parseSkin(String line) {
        String[] args = line.split(String.valueOf(SETTING_SEPARATOR));
        if (args.length != 2) {
            Logger.warn(FileHandler.class.getSimpleName(),
                    "skin setting not set '%s', ignoring%n", args[0]);
        } else {
            switch (args[0]) {
                case "style":
                    Config.BOARD_SKIN.setBoardGridStyle(BoardGridStyle.values()[
                            parseInt(args[0], args[1], BoardGridStyle.values().length, 2)
                            ]);
                    break;
                case "chars":
                    int[] chars = parseInts(args[0],
                            args[1].split(String.valueOf(VALUE_SEPARATOR)),
                            BoardGridCharacter.values().length, new int[]{3, 4});
                    Config.BOARD_SKIN
                            .setGridCharacter(BoardGridCharacter.values()[chars[0]]);
                    Config.BOARD_SKIN
                            .setAltGridCharacter(BoardGridCharacter.values()[chars[1]]);
                    break;
                case "marbles":
                    Config.BOARD_SKIN.setMarbleStyle(MarbleStyle.values()[
                            parseInt(args[0], args[1], MarbleStyle.values().length, 0)
                            ]);
                    break;
                case "notation":
                    Config.BOARD_SKIN
                            .setHideNotation(parseInt(args[0], args[1], 2, 1) == 0);
                    break;
                default:
                    Logger.warn(FileHandler.class.getSimpleName(),
                            "unknown skin setting '%s', ignoring%n", args[0]);
                    break;
            }
        }
    }

    /**
     * Helper method to parse a line containing a Server related setting.
     *
     * @param line the line to parse
     */
    //@ requires line != null;
    private static void parseServer(String line) {
        String[] args = line.split(String.valueOf(SETTING_SEPARATOR));
        if (args.length != 2) {
            Logger.warn(FileHandler.class.getSimpleName(),
                    "Server setting not set '%s', ignoring%n", args[0]);
        } else {
            switch (args[0]) {
                case "profile":
                    String[] profile = args[1].split(String.valueOf(VALUE_SEPARATOR));
                    if (profile.length != 2) {
                        Logger.warn(
                                "[FileHandler] Server profile not set '%s', ignoring%n", args[0]);
                    } else {
                        String[] address = profile[1].split(":");
                        int port = parseInt(args[0], address[1], 65536, 0);
                        if (!String.format("%d", port).equals(address[1])) {
                            Logger.warn(
                                    "[FileHandler] Server profile has incorrect port '%s', " +
                                            "defaulting to '0'%n", address[1]);
                        }
                        Config.addServerProfile(
                                profile[0], String.format("%s:%d", address[0], port));
                    }
                    break;
                case "timeUntilDisconnect":
                    Config.setTimeUntilDisconnect(
                            parseInt(args[0], args[1], 1000000000, 30000));
                    break;
                case "pingInterval":
                    Config.setPingInterval(
                            parseInt(args[0], args[1], 1000000000, 15000));
                    break;
                case "gmTickRate":
                    Config.setGameManagerTickRate(
                            parseInt(args[0], args[1], 1000000000, 1));
                    break;
                default:
                    Logger.warn(
                            "[FileHandler] unknown Server setting '%s', ignoring%n", args[0]);
                    break;
            }
        }
    }

    /**
     * Helper method to parse a line containing a Client related setting.
     *
     * @param line the line to parse
     */
    //@ requires line != null;
    private static void parseClient(String line) {
        String[] args = line.split(String.valueOf(SETTING_SEPARATOR));
        if (args.length != 2) {
            Logger.warn(FileHandler.class.getSimpleName(),
                    "Client setting not set '%s', ignoring%n", args[0]);
        } else {
            boolean unimplemented = false;
            switch (args[0]) {
                case "enableChat":
                    if (Config.CLIENT_CHAT_IMPLEMENTED) {
                        Config.setClientChatSupport(parseInt(args[0], args[1], 2, 1) == 1);
                    } else {
                        unimplemented = true;
                    }
                    break;
                case "enableRank":
                    if (Config.CLIENT_RANK_IMPLEMENTED) {
                        Config.setClientRankSupport(parseInt(args[0], args[1], 2, 1) == 1);
                    } else {
                        unimplemented = true;
                    }
                    break;
                case "enableAuth":
                    if (Config.CLIENT_AUTH_IMPLEMENTED) {
                        Config.setClientAuthSupport(parseInt(args[0], args[1], 2, 1) == 1);
                    } else {
                        unimplemented = true;
                    }
                    break;
                case "enableCrypt":
                    if (Config.CLIENT_CRYPT_IMPLEMENTED) {
                        Config.setClientCryptSupport(parseInt(args[0], args[1], 2, 1) == 1);
                    } else {
                        unimplemented = true;
                    }
                    break;
                default:
                    Logger.warn(FileHandler.class.getSimpleName(),
                            "unknown Server setting '%s', ignoring%n", args[0]);
                    break;
            }

            if (unimplemented) {
                Logger.warn(FileHandler.class.getSimpleName(),
                        "found unimplemented setting '%s'%n", args[0]);
            }
        }
    }

    /**
     * Helper method to parse a line containing a AI related setting.
     *
     * @param line the line to parse
     */
    //@ requires line != null;
    private static void parseAI(String line) {
        String[] args = line.split(String.valueOf(SETTING_SEPARATOR));
        if (args.length != 2) {
            Logger.warn(FileHandler.class.getSimpleName(),
                    "AI setting not set '%s', ignoring%n", args[0]);
        } else {
            switch (args[0]) {
                case "spDelay":
                    Config.setResponseDelaySinglePlayer(
                            parseInt(args[0], args[1], 100000, 1000));
                    break;
                case "mpDelay":
                    Config.setResponseDelayMultiPlayer(
                            parseInt(args[0], args[1], 100000, 1000));
                    break;
                default:
                    Logger.warn(FileHandler.class.getSimpleName(),
                            "unknown AI setting '%s', ignoring%n", args[0]);
                    break;
            }
        }
    }

    /**
     * Helper method to parse a line containing a Debug related setting.
     *
     * @param line the line to parse
     */
    //@ requires line != null;
    private static void parseDebug(String line) {
        String[] args = line.split(String.valueOf(SETTING_SEPARATOR));
        if (args.length != 2) {
            Logger.warn(FileHandler.class.getSimpleName(),
                    "Debug setting not set '%s', ignoring%n", args[0]);
        } else {
            // CheckStyle complains about too few case labels,
            // but this is structured in such a way so as to accommodate future settings
            switch (args[0]) {
                case "logLevel":
                    Config.setLoggingLevel(
                            LoggingLevel.values()[parseInt(args[0], args[1],
                                    LoggingLevel.values().length, 3)]);
                    break;
                default:
                    Logger.warn(FileHandler.class.getSimpleName(),
                            "unknown Debug setting '%s', ignoring%n", args[0]);
                    break;
            }
        }
    }

    /**
     * Read and parse the configuration file.
     *
     * @return true when file was successfully read, false otherwise
     */
    private static boolean readConfigFile() {
        try (var reader = new BufferedReader(new FileReader(CONFIG_FILENAME))) {

            String currentSection = null;

            for (String line = reader.readLine(); line != null; line = reader.readLine()) {
                // ignore empty lines
                if (line.equals("")) {
                    continue;
                }

                if (line.charAt(0) == SECTION_MARKER) {
                    // detect a new section
                    currentSection = line.substring(1).toUpperCase();
                } else if (currentSection == null) {
                    // it's not a section, but also the section wasn't ever set
                    Logger.warn(
                            "[FileHandler] the line '%s' is not under a section, ignoring%n", line);
                } else {
                    // parse the line as belonging to the current section
                    switch (currentSection) {
                        case "SERVER":
                            parseServer(line);
                            break;
                        case "CLIENT":
                            parseClient(line);
                            break;
                        case "SKIN":
                            parseSkin(line);
                            break;
                        case "AI":
                            parseAI(line);
                            break;
                        case "DEBUG":
                            parseDebug(line);
                            break;
                        default:
                            Logger.warn(FileHandler.class.getSimpleName(),
                                    "unknown section '%s', ignoring%n", currentSection);
                            break;
                    }
                }
            }

            return true;
        } catch (IOException e) {
            return false;
        }
    }

    /**
     * Utility method to generate the proper string for a configuration section.
     *
     * @param sectionName the name of the section
     * @return the properly formatted section
     */
    //@ requires sectionName != null;
    //@ ensures \result != null && \result.contains(sectionName);
    private static String makeSection(String sectionName) {
        return String.format("%s%s", SECTION_MARKER, sectionName);
    }

    /**
     * Utility method to generate the proper string for a specific setting.
     *
     * @param settingName the name of the section
     * @param values      optional vararg to populate the setting with
     * @return the properly formatted section
     */
    /*@
        requires settingName != null;
        ensures \result != null && \result.contains(settingName);
        ensures values != null ==> (\forall int i; i >= 0 && i < values.length;
                                        \result.contains(String.valueOf(values[i])));
    */
    private static String makeSetting(String settingName, Object... values) {

        StringBuilder sb = new StringBuilder();
        sb.append(String.format("%s%s", settingName, SETTING_SEPARATOR));

        for (Object value : values) {
            sb.append(String.format("%s%s", value.toString(), VALUE_SEPARATOR));
        }

        String result = sb.toString();
        if (values.length > 0) {
            result = result.substring(0, sb.length() - 1);
        }

        return result;

    }

    /**
     * Retrieve {@link Config}'s values and write them to the configuration file.
     *
     * @return true when file was successfully written, false otherwise
     */
    private static boolean writeConfigFile() {
        try (var writer = new PrintWriter(new FileWriter(CONFIG_FILENAME))) {

            // Write server config
            writer.println(makeSection("SERVER"));
            for (Map.Entry<String, String> entry : Config.getServerProfiles()) {
                writer.println(makeSetting("profile", entry.getKey(), entry.getValue()));
            }
            writer.println(makeSetting("timeUntilDisconnect", Config.getTimeUntilDisconnect()));
            writer.println(makeSetting("pingInterval", Config.getPingInterval()));
            writer.println(makeSetting("gmTickRate", Config.getGameManagerTickRate()));
            writer.println();

            // Write client config
            writer.println(makeSection("CLIENT"));
            if (Config.CLIENT_CHAT_IMPLEMENTED) {
                writer.println(makeSetting("enableChat", Config.doesClientSupportChat() ? 1 : 0));
            }
            if (Config.CLIENT_RANK_IMPLEMENTED) {
                writer.println(makeSetting("enableRank", Config.doesClientSupportRank() ? 1 : 0));
            }
            if (Config.CLIENT_AUTH_IMPLEMENTED) {
                writer.println(makeSetting("enableAuth", Config.doesClientSupportAuth() ? 1 : 0));
            }
            if (Config.CLIENT_CRYPT_IMPLEMENTED) {
                writer.println(makeSetting("enableCrypt", Config.doesClientSupportCrypt() ? 1 : 0));
            }
            writer.println();

            // Write AI config
            writer.println(makeSection("AI"));
            writer.println(makeSetting("spDelay", Config.getResponseDelaySinglePlayer()));
            writer.println(makeSetting("mpDelay", Config.getResponseDelayMultiPlayer()));
            writer.println();

            // Write BoardSkin config
            BoardSkin skin = Config.BOARD_SKIN;
            writer.println(makeSection("SKIN"));
            writer.println(makeSetting("style", skin.getBoardGridStyle().ordinal()));
            writer.println(makeSetting("chars",
                    skin.getGridCharacter().ordinal(), skin.getAltGridCharacter().ordinal()));
            writer.println(makeSetting("marbles", skin.getMarbleStyle().ordinal()));
            writer.println(makeSetting("notation", skin.hideNotation() ? 0 : 1));
            writer.println();

            // Write Debug config
            writer.println(makeSection("DEBUG"));
            writer.println(makeSetting("logLevel", Config.getLoggingLevel().ordinal()));

            writer.flush();

            return true;
        } catch (IOException e) {
            return false;
        }
    }

    /**
     * Read the config file. If it doesn't exist, nothing happens, defaults will be used instead.
     */
    public static void loadConfig() {
        if (readConfigFile()) {
            Logger.info(FileHandler.class.getSimpleName(),
                    "Configuration loaded from file");
        } else {
            Logger.warn(FileHandler.class.getSimpleName(),
                    "Could not load config file, using defaults");
        }
    }

    /**
     * Save the config file. If saving fails, any configured settings will simply be lost,
     * and the next time the program is run, defaults will be used.
     */
    public static void saveConfig() {
        if (writeConfigFile()) {
            Logger.info(FileHandler.class.getSimpleName(), "Configuration saved to file");
        } else {
            Logger.warn(FileHandler.class.getSimpleName(), "Could not save to config file, " +
                    "any settings you configured will be lost");
        }
    }
}
