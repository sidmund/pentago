package ss.pentago.tui.menu;

import java.util.Arrays;
import java.util.Scanner;

/**
 * TUIInputField provides a convenient way to group together to ask the user for certain input
 * in startup and configuration menus, not gameplay input.
 * This class provides methods to ask for a string, an integer, and a boolean (a 'yes/no' question).
 */
public class TUIInputField {

    private TUIInputField() {
    }

    /**
     * Ask for a string.
     *
     * @param question     the question, if null, defaults to "Text?"
     * @param defaultValue the default value
     * @param scanner      the scanner
     * @return the entered string, or defaultValue when 'Enter' has been pressed,
     * or null when no input can be obtained (scanner is null) and the default is null
     * or default when the scanner is null but not the default
     */
    /*@
        requires question != null && defaultValue != null && scanner != null;
        ensures scanner == null && defaultValue == null ==> \result == null;
        ensures \result != null || \result == defaultValue;
    */
    public static String askForString(
            String question, String defaultValue, Scanner scanner) {
        if (scanner == null) {
            return defaultValue;
        }

        String s = null;

        while (s == null) {
            System.out.printf("%s ('Enter' to use default '%s'): ",
                    question == null ? "Text?" : question, defaultValue);
            s = scanner.nextLine();
            if (s.isBlank()) {
                return defaultValue;
            }
        }

        return s;
    }

    /**
     * Ask the user for a number.
     *
     * @param question     the question, if null, defaults to "Number?"
     * @param min          the minimum amount (inclusive)
     * @param max          the maximum amount (exclusive)
     * @param defaultValue the default amount to use, if this value is smaller than min or
     *                     bigger than or equal to max, it is set to min
     * @param scanner      the scanner
     * @return a number between {@code min} and {@code max} (exclusive),
     * or defaultValue when 'Enter' has been pressed or {@code max >= min} or scanner is null
     */
    /*@
        requires question != null && scanner != null
                && min < max && defaultValue >= min && defaultValue < max;
        ensures min >= max ==> \result == defaultValue;
        ensures defaultValue < min || defaultValue >= max ==> \result == min;
        ensures scanner == null ==> \result == defaultValue;
        ensures \result >= min && \result < max;
    */
    public static int askForNumber(
            String question, int min, int max, int defaultValue, Scanner scanner) {
        if (min >= max) {
            return defaultValue;
        } else if (defaultValue < min || defaultValue >= max) {
            return min;
        } else if (scanner == null) {
            return defaultValue;
        }

        // start with some invalid value
        int result = min - 1;

        do {
            System.out.printf("%s (between %d and %d, 'Enter' to use default '%d'): ",
                    question == null ? "Number?" : question, min, max, defaultValue);
            String input = scanner.nextLine();
            if (input.isBlank()) {
                // pressed 'Enter'
                return defaultValue;
            } else {
                try {
                    result = Integer.parseInt(input);
                } catch (NumberFormatException e) {
                    // ignore, ask for number again
                }
            }
        }
        while (result < min || result >= max);

        return result;
    }

    /**
     * Ask the user for a boolean value.
     *
     * @param question     the yes/no question, if null defaults to "Yes/no?"
     * @param defaultValue the default value to use
     * @param scanner      the scanner
     * @return defaultValue when 'Enter' has been pressed, true/false otherwise
     */
    /*@
        requires question != null && scanner != null;
        ensures \result || !\result;
     */
    public static boolean askForBoolean(
            String question, boolean defaultValue, Scanner scanner) {
        if (scanner == null) {
            return defaultValue;
        }

        // NB these arrays must be sorted, since we use Arrays.binarySearch
        String[] trueAnswers = {"1", "true", "y", "yes"};
        String[] falseAnswers = {"0", "false", "n", "no"};

        do {
            System.out.printf("%s ('Enter' to use default '%s'): ",
                    question == null ? "Yes/no?" : question, defaultValue ? "yes" : "no");
            String input = scanner.nextLine().toLowerCase();
            if (input.isBlank()) {
                // press enter, just return default
                return defaultValue;
            } else {
                if (Arrays.binarySearch(trueAnswers, input) >= 0) {
                    return true;
                } else if (Arrays.binarySearch(falseAnswers, input) >= 0) {
                    return false;
                }
                // ignore, keep asking
            }
        }
        while (true);
    }

    /**
     * Ask the user to press enter. This method exits when enter has been pressed.
     *
     * @param message the message to show them, if null defaults to "Press 'Enter'"
     * @param scanner the scanner
     */
    /*@
        requires message != null && scanner != null;
     */
    public static void waitForEnter(String message, Scanner scanner) {
        if (scanner == null) {
            return;
        }

        System.out.printf("%s: ",
                message == null ? "Press 'Enter'" : message);

        scanner.nextLine();
    }
}
