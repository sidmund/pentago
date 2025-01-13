package ss.pentago.network.protocol;

import ss.pentago.util.Logger;

/**
 * ProtocolHandler standardizes the communicates between clients and server
 * and abstracts it away from specific Client or Server implementations.
 */
public interface ProtocolHandler {

    /**
     * Receive a protocol command from either server or client, parse it,
     * and perform a relevant reply.
     *
     * @param command the protocol command
     */
    //@ requires command != null;
    void receive(String command);

    /**
     * Check the received extensions and enable those in common.
     *
     * @param extensions the array of supported extensions
     */
    void setupExtensions(String[] extensions);

    /**
     * Send an error message somewhere.
     *
     * @param error the error description
     */
    void sendError(String error);

    /**
     * Check the length of the arguments. Calls {@link #sendError(String)}
     * when the length requirement is not met.
     *
     * @param args the arguments to check
     * @param min  the minimum length
     * @param max  the maximum length (exclusive)
     * @return true when the length is within [min,max)
     */
    //@ requires args != null && min >= 0 && min < max;
    //@ ensures \result ==> args.length >= min && args.length < max;
    default boolean checkArgumentLengthMinMax(String[] args, int min, int max) {
        if (args.length >= min && args.length < max) {
            return true;
        } else {
            sendError(String.format("number of arguments should be between %d and %d.",
                    min, max));
            return false;
        }
    }

    /**
     * Check the length of the arguments. Calls {@link #sendError(String)}
     * when the length requirement is not met.
     *
     * @param args the arguments to check
     * @param min  the minimum length
     * @return true when the length is at least the minimum
     */
    //@ requires args != null;
    //@ ensures \result ==> args.length >= min;
    default boolean checkArgumentLengthMin(String[] args, int min) {
        if (args.length >= min) {
            return true;
        } else {
            sendError(String.format("number of arguments should be at least: %d", min));
            return false;
        }
    }

    /**
     * Check the length of the arguments. Calls {@link #sendError(String)}
     * when the length requirement is not met.
     *
     * @param args   the arguments to check
     * @param length the exact length required
     * @return true when the length is exactly the same as length
     */
    //@ requires args != null && length > 0;
    //@ ensures \result ==> args.length == length;
    default boolean checkArgumentLengthExact(String[] args, int length) {
        if (args.length != length) {
            sendError(String.format("expected number of arguments: %d", length));
            return false;
        }
        return true;
    }

    /**
     * Log the message sent for debugging.
     *
     * @param message the message
     */
    default void printDebugMessageSent(String message) {
        Logger.info(this, "sent: '%s'", message);
    }

    /**
     * Log the message received for debugging.
     *
     * @param message the message
     */
    default void printDebugMessageReceived(String message) {
        Logger.info(this, "received: '%s'", message);
    }

}
