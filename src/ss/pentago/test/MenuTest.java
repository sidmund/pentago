package ss.pentago.test;

import org.junit.jupiter.api.Test;
import ss.pentago.tui.menu.TUIInputField;
import ss.pentago.tui.menu.TUIMenu;
import ss.pentago.tui.menu.TUIMenuOption;

import java.io.IOException;
import java.io.PipedReader;
import java.io.PipedWriter;
import java.io.PrintWriter;
import java.util.Scanner;

import static org.junit.jupiter.api.Assertions.*;

/**
 * MenuTest tests the TUIMenu and indirectly the TUIMenuOption.
 */
public class MenuTest {

    /**
     * Test whether menu selection works (and thus indirectly
     * that menu items are correctly created and rendered,
     * and that input parsing works).
     * Note that since we are not manually entering, the input
     * is not visible, however we can see in the test output that
     * that the "?:" for getting input appears. For receiving invalid
     * input it prints it again, so we can see that it doesn't break
     * on invalid input.
     *
     * @throws IOException if an I/O error occurs
     */
    @Test
    public void testMenu() throws IOException {
        final int[] setting = {0};

        TUIMenu menu = new TUIMenu("Test Menu");
        menu.add(new TUIMenuOption("Option A") {
            @Override
            public void execute() {
                setting[0] = 1;
            }
        });
        menu.add(new TUIMenuOption("Option B") {
            @Override
            public void execute() {
                setting[0] = 2;
            }
        });

        try (PipedReader reader = new PipedReader();
             PipedWriter writer = new PipedWriter(reader);
             PrintWriter pw = new PrintWriter(writer, true);
             Scanner scanner = new Scanner(reader)) {

            pw.println("1");
            menu.run(scanner);
            assertEquals(1, setting[0]);

            pw.println("2");
            menu.run(scanner);
            assertEquals(2, setting[0]);

            // Invalid input just keeps the menu running,
            // so we can only test that before writing a valid input
            pw.println("a");
            pw.println("0");
            pw.println("1");
            // should first find an invalid value, then the valid one
            // thus updating the setting
            menu.run(scanner);
            assertEquals(1, setting[0]);
        }
    }

    /**
     * Test the TUIInputField method {@code askForNumber}.
     *
     * @throws IOException if an I/O error occurs
     */
    @Test
    public void testIntField() throws IOException {
        try (PipedReader reader = new PipedReader();
             PipedWriter writer = new PipedWriter(reader);
             PrintWriter pw = new PrintWriter(writer, true);
             Scanner scanner = new Scanner(reader)) {

            int res;

            pw.println("1");

            // -- invalid --

            // question 'null' should default to something sensible
            // null as scanner should make it default to 3, since obviously it cannot read the "1"
            res = TUIInputField.askForNumber(null, 0, 5, 3, null);
            assertEquals(3, res);

            // should return 3, since the bounds are invalid
            res = TUIInputField.askForNumber(null, 0, -5, 3, scanner);
            assertEquals(3, res);

            // should also return 3
            res = TUIInputField.askForNumber(null, 0, -5, 3, null);
            assertEquals(3, res);

            // should return 0, since defaultValue is bigger than the bounds
            res = TUIInputField.askForNumber(null, 0, 5, 8, scanner);
            assertEquals(0, res);

            // should still return 0, even if scanner is null
            res = TUIInputField.askForNumber(null, 0, 5, 8, null);
            assertEquals(0, res);

            // -- valid --

            // can now finally read that "1" in the buffer
            res = TUIInputField.askForNumber(null, 0, 5, 3, scanner);
            assertEquals(1, res);

            // pressing 'Enter' should go to default
            pw.println();
            res = TUIInputField.askForNumber(null, 0, 5, 3, scanner);
            assertEquals(3, res);
        }
    }

    /**
     * Test the TUIInputField method {@code askForBoolean}.
     *
     * @throws IOException if an I/O error occurs
     */
    @Test
    public void testBooleanField() throws IOException {
        try (PipedReader reader = new PipedReader();
             PipedWriter writer = new PipedWriter(reader);
             PrintWriter pw = new PrintWriter(writer, true);
             Scanner scanner = new Scanner(reader)) {

            boolean res;

            pw.println("1");

            // -- invalid --

            // question 'null' should default to something sensible
            // should default to false
            res = TUIInputField.askForBoolean(null, true, null);
            assertTrue(res);

            // -- valid input --

            // can now finally read that "1" in the buffer
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertTrue(res);

            // test all allowed 'true' values
            pw.println("true");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertTrue(res);
            pw.println("yes");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertTrue(res);
            pw.println("YES");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertTrue(res);
            pw.println("y");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertTrue(res);

            // test all allowed 'false' values
            pw.println("false");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertFalse(res);
            pw.println("0");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertFalse(res);
            pw.println("NO");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertFalse(res);
            pw.println("n");
            res = TUIInputField.askForBoolean(null, false, scanner);
            assertFalse(res);

            // pressing 'Enter' should go to default
            pw.println();
            res = TUIInputField.askForBoolean(null, true, scanner);
            assertTrue(res);
        }
    }

    /**
     * Test the TUIInputField method {@code askForString}.
     *
     * @throws IOException if an I/O error occurs
     */
    @Test
    public void testStringField() throws IOException {
        try (PipedReader reader = new PipedReader();
             PipedWriter writer = new PipedWriter(reader);
             PrintWriter pw = new PrintWriter(writer, true);
             Scanner scanner = new Scanner(reader)) {

            String res;

            pw.println("foo");

            // -- invalid --

            // question 'null' should default to something sensible
            // should default to 'bar'
            res = TUIInputField.askForString(null, "bar", null);
            assertEquals("bar", res);

            res = TUIInputField.askForString(null, null, null);
            assertNull(res);

            // -- valid input --

            // can now finally read that "foo" in the buffer
            res = TUIInputField.askForString(null, null, scanner);
            assertEquals("foo", res);

            pw.println("bar");
            res = TUIInputField.askForString(null, "fubar", scanner);
            assertEquals("bar", res);

            // pressing 'Enter' should go to default
            pw.println();
            res = TUIInputField.askForString(null, "foobar", scanner);
            assertEquals("foobar", res);
        }
    }
}
