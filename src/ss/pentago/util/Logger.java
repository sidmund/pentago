package ss.pentago.util;

import ss.pentago.file.Config;
import ss.pentago.tui.Colors;

import java.io.PrintStream;

/**
 * Basic Logger.
 */
public class Logger {

    private static final PrintStream LOG = System.out;

    private Logger() {
    }

    private static void print(Object source,  String message, String color) {
        LOG.printf("%s[%s] %s%s%n", color, source.toString(), message, Colors.RESET);
    }

    public static void info(Object source, String message) {
        if (Config.getLoggingLevel().ordinal() < 1) {
            print(source, message, Colors.CYAN);
        }
    }

    public static void info(Object source, String format, Object... args) {
        if (Config.getLoggingLevel().ordinal() < 2) {
            info(source, String.format(format, args));
        }
    }

    public static void warn(Object source, String message) {
        if (Config.getLoggingLevel().ordinal() < 2) {
            print(source, message, Colors.YELLOW);
        }
    }

    public static void warn(Object source, String format, Object... args) {
        warn(source, String.format(format, args));
    }

    public static void error(Object source, String message) {
        if (Config.getLoggingLevel().ordinal() < 3) {
            print(source, message, Colors.RED);
        }
    }

    public static void error(Object source, String format, Object... args) {
        if (Config.getLoggingLevel().ordinal() < 3) {
            error(source, String.format(format, args));
        }
    }
}
