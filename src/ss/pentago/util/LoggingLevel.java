package ss.pentago.util;

public enum LoggingLevel {

    /**
     * Display info, warning and error messages.
     */
    ALL("Show everything"),

    /**
     * Display error and warning messages.
     */
    WARN("Show warnings and errors only"),

    /**
     * Display only error messages.
     */
    ERROR("Show only errors"),

    /**
     * Display nothing.
     */
    IGNORE("Show nothing");

    private final String desc;

    LoggingLevel(String desc) {
        this.desc = desc;
    }

    @Override
    public String toString() {
        return desc;
    }
}
