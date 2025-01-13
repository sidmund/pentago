package ss.pentago.tui.menu;

/**
 * TUIMenuOption represents a menu option in a TUIMenu.
 * The method in this class are meant to be overridden upon instantiation.
 */
public abstract class TUIMenuOption {

    //@ private invariant displayName != null;

    private final String displayName;

    /**
     * Create a new TUIMenuOption with specified display name.
     *
     * @param displayName the name to display when showing the TUIMenu
     */
    //@ requires displayName != null && this.displayName == displayName;
    protected TUIMenuOption(String displayName) {
        this.displayName = displayName;
    }

    /**
     * Executes the menu option.
     * This method should be overridden when a new TUIMenuOption is created.
     */
    public abstract void execute();

    /**
     * @return the name to display when showing the TUIMenu
     */
    public String getDisplayName() {
        return displayName;
    }
}
