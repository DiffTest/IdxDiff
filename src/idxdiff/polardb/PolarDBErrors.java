package idxdiff.polardb;

import idxdiff.common.query.ExpectedErrors;
import idxdiff.mysql.MySQLErrors;

public final class PolarDBErrors {

    private PolarDBErrors() {
    }

    public static void addIndexErrors(ExpectedErrors errors) {
        MySQLErrors.addExpressionErrors(errors);
        MySQLErrors.addInsertUpdateErrors(errors);

        // Standard MySQL index/syntax errors
        errors.add("You have an error in your SQL syntax");
        errors.add("Unknown column");
        errors.add("doesn't exist");
        errors.add("does not exist");
        errors.add("cannot be null");
        errors.add("division by zero");
        errors.add("BIGINT value is out of range");
        errors.add("BIGINT UNSIGNED value is out of range");
        errors.add(" DOUBLE value is out of range");
        errors.add("Illegal double");
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
        errors.add("Key reference and table reference");
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
        errors.add("functional index dependency and cannot be dropped");
        errors.add("Unknown database");
        errors.add("cannot be invisible");

        // PolarDB-X specific incompatibility error codes
        // These are expected SQL-layer incompatibilities, not index correctness bugs.
        // PXC-4006: unsupported SQL syntax or DDL feature
        errors.add("PXC-4006");
        // PXC-5007: unsupported function or expression
        errors.add("PXC-5007");
        // PXC-1019: unsupported DDL type (e.g., INVISIBLE INDEX, FULLTEXT)
        errors.add("PXC-1019");
        // PXC-4002: syntax not supported in distributed mode
        errors.add("PXC-4002");
        // PXC-4007: not supported in current version
        errors.add("PXC-4007");
        // ERR_TDDL_ prefix: PolarDB-X internal TDDL errors (optimizer, planner)
        errors.add("ERR_TDDL_");
        // Generic PXC fallback for any other PolarDB-X incompatibility not listed above
        errors.add("PXC-");
    }
}
