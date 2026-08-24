package idxdiff.mariadb;

import java.util.ArrayList;
import java.util.List;

import idxdiff.common.query.ExpectedErrors;

public final class MariaDBErrors {

    private MariaDBErrors() {
    }

    public static List<String> getCommonErrors() {
        ArrayList<String> errors = new ArrayList<>();

        errors.add("is out of range");
        // regex
        errors.add("unmatched parentheses");
        errors.add("nothing to repeat at offset");
        errors.add("missing )");
        errors.add("missing terminating ]");
        errors.add("range out of order in character class");
        errors.add("unrecognized character after ");
        errors.add("Got error '(*VERB) not recognized or malformed");
        errors.add("must be followed by");
        errors.add("malformed number or name after");
        errors.add("digit expected after");
        errors.add("Regex error");
        errors.add("Lock wait timeout exceeded");

        return errors;
    }

    public static void addCommonErrors(ExpectedErrors errors) {
        errors.add("is out of range");
        // regex
        errors.add("unmatched parentheses");
        errors.add("nothing to repeat at offset");
        errors.add("missing )");
        errors.add("missing terminating ]");
        errors.add("range out of order in character class");
        errors.add("unrecognized character after ");
        errors.add("Got error '(*VERB) not recognized or malformed");
        errors.add("must be followed by");
        errors.add("malformed number or name after");
        errors.add("digit expected after");
        errors.add("Regex error");
        errors.add("Lock wait timeout exceeded");
    }

    public static List<String> getInsertErrors() {
        ArrayList<String> errors = new ArrayList<>();
        errors.add("Out of range");
        errors.add("Duplicate entry"); // violates UNIQUE constraint
        errors.add("cannot be null"); // violates NOT NULL constraint
        errors.add("Incorrect integer value"); // e.g., insert TEXT into an int value
        errors.add("Data truncated for column"); // int + plus string into int
        errors.add("doesn't have a default value"); // no default value
        errors.add("The value specified for generated column"); // trying to insert into a generated column
        errors.add("Incorrect double value");
        errors.add("Incorrect string value");
        return errors;
    }

    public static void addInsertErrors(ExpectedErrors errors) {
        errors.addAll(getInsertErrors());
    }

    /** Index-specific errors for the Index Oracle */
    public static List<String> getIndexErrors() {
        ArrayList<String> errors = new ArrayList<>();
        errors.add("You have an error in your SQL syntax");
        errors.add("Unknown column");
        errors.add("doesn't exist");
        errors.add("does not exist");
        errors.add("cannot be null");
        errors.add("division by zero");
        errors.add("BIGINT value is out of range");
        errors.add("DOUBLE value is out of range");
        errors.add("Data truncated for column");
        errors.add("not in GROUP BY clause");
        errors.add("incompatible with sql_mode=only_full_group_by");
        errors.add("nonaggregated column");
        errors.add("Functional index");
        errors.add("used in key specification");
        errors.add("Specified key was too long");
        errors.add("BLOB or TEXT");
        errors.add("Too many keys specified");
        errors.add("Duplicate key name");
        errors.add("Can't DROP");
        errors.add("already exists");
        errors.add("Column count");
        errors.add("Subquery returns more than 1 row");
        errors.add("column is ambiguous");
        errors.add("Can't group on");
        errors.add("Lost connection");
        errors.add("Query execution was interrupted");
        errors.add("Too many connections");
        errors.add("max_allowed_packet");
        errors.add("Deadlock");
        errors.add("Lock wait timeout");
        errors.add("lock(s)");
        errors.add("Duplicate entry");
        errors.add("doesn't have a default value");
        errors.add("Not a valid escape sequence");
        errors.add("Unknown database");
        // Replaced broad "is out of range" with specific type-based strings
        errors.add("DECIMAL value is out of range");
        errors.add("BIGINT UNSIGNED value is out of range");
        errors.add("Key/Index cannot be defined on a virtual generated column");
        // Phase B: Additional errors for new modes (13-23)
        errors.add("Unknown optimizer_switch");
        errors.add("Invalid value for");
        errors.add("STRAIGHT_JOIN");
        errors.add("Correlation name");
        // REMOVED: "Unknown table" — may mask table-vanishing bugs (MySQL index oracle also removed this)
        // REMOVED: "Table crashed" — should expose index corruption bugs, not suppress them
        // REMOVED: "record file is crashed" — same reason as above
        // Phase C: Additional errors for MariaDB-only modes (24-28)
        errors.add("join_cache_level");
        errors.add("rowid_filter");
        errors.add("not_null_range_scan");
        errors.add("condition_pushdown_for_derived");
        errors.add("condition_pushdown_for_subquery");
        errors.add("index_merge_intersection");
        errors.add("index_merge_sort_intersection");
        errors.add("Unknown system variable");
        // REMOVED: "Unexpected EOF" — may mask data file corruption bugs
        return errors;
    }

}
