package ss.pentago.tui.menu;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * TUIMenu provides a convenient way to create selection menus.<br>
 * The class is meant to be used (instantiated) this way (e.g.),
 * where {@code scanner} should be a System.in Scanner:
 * <pre>
 *     new TUIMenu("MENU TITLE")
 *          .add(new TUIMenuOption("Option") {
 *              public void execute() {
 *                  // do something
 *              }
 *          })
 *          .add(new TUIMenuOption("Other option") {
 *              public void execute() {
 *                  // do something else
 *              }
 *          })
 *          .run(scanner);
 * </pre>
 */
public class TUIMenu {

    //@ private invariant title != null;

    private final String title;
    private final List<TUIMenuOption> options;

    /**
     * Constructs a new TUIMenu with specified title.
     *
     * @param title the title
     */
    public TUIMenu(String title) {
        this.title = title.toUpperCase();
        options = new ArrayList<>();
    }

    /**
     * Add a new TUIMenuOption to this TUIMenu,
     * ideally chain this call to the constructor.
     *
     * @param option the option
     * @return the TUIMenu the option was added to for easy chaining
     */
    /*@
        requires option != null;
        ensures \old(options.size()) + 1 == options.size();
        ensures options.get(options.size() - 1) == option;
        ensures (\forall int i; i >= 0 && i < options.size() - 1;
                 \old(options.get(i)) == options.get(i));
    */
    public TUIMenu add(TUIMenuOption option) {
        options.add(option);
        return this;
    }

    /**
     * Shows the TUIMenu to System.out.
     */
    //@ pure
    private void showMenu() {
        System.out.println(title);
        for (int i = 0; i < options.size(); i++) {
            System.out.printf("%2d. %s%n", i + 1, options.get(i).getDisplayName());
        }
    }

    /**
     * Obtains the choice of the user,
     * this method keeps running until the user
     * has selected a valid option.
     *
     * @param scanner the System.in scanner
     */
    //@ ensures \result >= 0 && \result < options.size();
    private int getUserSelection(Scanner scanner) {
        int choice;
        do {
            System.out.print("?: ");
            String input = scanner.nextLine();
            try {
                choice = Integer.parseInt(input);
            } catch (NumberFormatException e) {
                // ignore
                choice = 0;
            }
        } while (choice < 1 || choice > options.size());

        return choice - 1;
    }

    /**
     * Runs the menu by showing it, requesting user input,
     * and invoking the corresponding action.
     * Nothing will happen if the menu has no options.
     * As long as an invalid choice is specified,
     * the menu will keep asking the user for input.
     *
     * @param scanner the System.in scanner
     */
    public void run(Scanner scanner) {
        if (options.isEmpty()) {
            return;
        }

        showMenu();
        int choice = getUserSelection(scanner);
        options.get(choice).execute();
    }
}
