package idxdiff.mariadb.gen;

import java.util.List;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Set;

import idxdiff.Randomly;
import idxdiff.common.DBMSCommon;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mariadb.MariaDBSchema;
import idxdiff.mariadb.MariaDBSchema.MariaDBColumn;
import idxdiff.mariadb.MariaDBSchema.MariaDBTable;

public final class MariaDBIndexGenerator {

    private MariaDBIndexGenerator() {
    }

    private static void addCommonIndexErrors(ExpectedErrors errors) {
        errors.add("Key/Index cannot be defined on a virtual generated column");
        errors.add("Specified key was too long");
        errors.add("BLOB or TEXT");
        errors.add("Too many keys specified");
        errors.add("Duplicate key name");
        errors.add("already exists");
        errors.add("Duplicate entry");
        errors.add("Identifier name"); // identifier too long (max 64 chars in MariaDB)
    }

    /**
     * Truncate an identifier name to fit within MariaDB's 64-character limit.
     * Keeps the prefix and suffix (hash), truncates the middle part if needed.
     */
    private static String truncateIdentifier(String prefix, String colName, String suffix, int maxLen) {
        String full = prefix + colName + suffix;
        if (full.length() <= maxLen) {
            return full;
        }
        // Truncate colName to fit: prefix + truncatedCol + suffix <= maxLen
        int maxColLen = maxLen - prefix.length() - suffix.length();
        if (maxColLen < 4) {
            // Fallback: just use hash-based name
            return prefix + Math.abs(colName.hashCode() % 100000) + suffix;
        }
        String truncatedCol = colName.substring(0, maxColLen);
        return prefix + truncatedCol + suffix;
    }

    public static SQLQueryAdapter generate(MariaDBSchema s) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        StringBuilder sb = new StringBuilder("CREATE ");
        if (Randomly.getBoolean()) {
            sb.append("UNIQUE ");
        }
        sb.append("INDEX ");
        sb.append("i");
        sb.append(DBMSCommon.createColumnName(Randomly.smallNumber()));
        if (Randomly.getBoolean()) {
            sb.append(" USING ");
            sb.append(Randomly.fromOptions("BTREE", "HASH"));
        }

        sb.append(" ON ");
        MariaDBTable randomTable = s.getRandomTable();
        sb.append(randomTable.getName());
        sb.append("(");
        List<MariaDBColumn> columns = Randomly.nonEmptySubset(randomTable.getColumns());
        for (int i = 0; i < columns.size(); i++) {
            if (i != 0) {
                sb.append(", ");
            }
            sb.append(columns.get(i).getName());
            if (Randomly.getBoolean()) {
                sb.append(" ");
                sb.append(Randomly.fromOptions("ASC", "DESC"));
            }
        }
        sb.append(")");

        return new SQLQueryAdapter(sb.toString(), errors, true);
    }

    /** Create a random index on a specific table (for Index Oracle) */
    public static SQLQueryAdapter generateForTable(MariaDBTable table, Set<String> existingSignatures) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        StringBuilder sb = new StringBuilder("CREATE ");
        boolean unique = Randomly.getBoolean();
        if (unique) {
            sb.append("UNIQUE ");
        }
        String idxName = "idx_" + DBMSCommon.createColumnName(Randomly.smallNumber());
        sb.append("INDEX ");
        sb.append(idxName);
        if (Randomly.getBoolean()) {
            sb.append(" USING ");
            sb.append(Randomly.fromOptions("BTREE", "HASH"));
        }
        sb.append(" ON ");
        sb.append(table.getName());
        sb.append("(");
        List<MariaDBColumn> columns = Randomly.nonEmptySubset(table.getColumns());
        StringBuilder colSpec = new StringBuilder();
        for (int i = 0; i < columns.size(); i++) {
            if (i != 0) {
                sb.append(", ");
                colSpec.append(",");
            }
            sb.append(columns.get(i).getName());
            colSpec.append(columns.get(i).getName());
            if (Randomly.getBoolean()) {
                sb.append(" ");
                String order = Randomly.fromOptions("ASC", "DESC");
                sb.append(order);
                colSpec.append(order);
            }
        }
        sb.append(")");

        String signature = (unique ? "U:" : "") + colSpec.toString();
        if (existingSignatures.contains(signature)) {
            return null;
        }

        return new SQLQueryAdapter(sb.toString(), errors, true);
    }

    /** Create an index on a specific column */
    public static SQLQueryAdapter createIndexOnColumn(MariaDBTable table, MariaDBColumn col) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        String colName = col.getName();
        String hash = "_" + Math.abs(colName.hashCode() % 1000);
        String idxName = truncateIdentifier("idx_", colName, hash, 64);
        return new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + table.getName() + " (" + col.getName() + ");",
                errors, true);
    }

    /** Create a prefix index on a VARCHAR column */
    public static SQLQueryAdapter createPrefixIndex(MariaDBTable table, MariaDBColumn col, int prefixLen) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        String colName = col.getName();
        String hash = "_" + Math.abs(colName.hashCode() % 1000);
        String idxName = truncateIdentifier("prefix_", colName, hash, 64);
        return new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + table.getName()
                        + " (" + col.getName() + "(" + prefixLen + "));",
                errors, true);
    }

    /** Create a UNIQUE index on a column */
    public static SQLQueryAdapter createUniqueIndex(MariaDBTable table, MariaDBColumn col) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        errors.add("Duplicate entry");
        String colName = col.getName();
        String hash = "_" + Math.abs(colName.hashCode() % 1000);
        String idxName = truncateIdentifier("uniq_", colName, hash, 64);
        return new SQLQueryAdapter(
                "CREATE UNIQUE INDEX " + idxName + " ON " + table.getName() + " (" + col.getName() + ");",
                errors, true);
    }

    /** Create a FULLTEXT index on a column */
    public static SQLQueryAdapter createFullTextIndex(MariaDBTable table, MariaDBColumn col) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        String colName = col.getName();
        String hash = "_" + Math.abs(colName.hashCode() % 1000);
        String idxName = truncateIdentifier("ft_", colName, hash, 64);
        return new SQLQueryAdapter(
                "CREATE FULLTEXT INDEX " + idxName + " ON " + table.getName() + " (" + col.getName() + ");",
                errors, true);
    }

    // ==================== Index Generator Enhancements ====================

    /**
     * MariaDB supports indexes on expressions via virtual computed columns:
     * 1) ALTER TABLE ADD COLUMN ... AS (expression) VIRTUAL
     * 2) CREATE INDEX ON table (virtual_column)
     * Expressions: LOWER(col), UPPER(col), CONCAT(col, '_suf'), LEFT(col, 5), SUBSTRING(col, 1, 3)
     */
    public static SQLQueryAdapter createExpressionIndex(MariaDBTable table, MariaDBColumn col) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        errors.add("Unknown column");
        errors.add("functional index");
        errors.add("Expression");
        errors.add("Generated column");
        errors.add("cannot be used");
        errors.add("Duplicate column");

        String tblName = table.getName();
        String colName = col.getName();

        String expr = Randomly.fromOptions(
                "LOWER(" + colName + ")",
                "UPPER(" + colName + ")",
                "CONCAT(" + colName + ", '_suf')",
                "LEFT(" + colName + ", 5)",
                "SUBSTRING(" + colName + ", 1, 3)"
        );

        String virtualColName = "vcol_" + Math.abs(colName.hashCode() % 1000);

        // Step 1: ALTER TABLE to add virtual column
        return new SQLQueryAdapter(
                "ALTER TABLE " + tblName + " ADD COLUMN " + virtualColName
                        + " VARCHAR(100) GENERATED ALWAYS AS (" + expr + ") VIRTUAL;",
                errors, true);
    }

    /**
     * Phase F1 companion: Create an index on a virtual column after it's been added.
     */
    public static SQLQueryAdapter createIndexOnVirtualColumn(MariaDBTable table, String virtualColName) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        errors.add("Unknown column");
        errors.add("functional index");
        String idxName = "expr_" + Math.abs(virtualColName.hashCode() % 1000);
        return new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + table.getName() + " (" + virtualColName + ");",
                errors, true);
    }

    /**
     * Phase F2: Generate a composite index with 2-3 columns.
     * Prioritizes multi-column indexes for better composite index testing.
     */
    public static SQLQueryAdapter generateCompositeIndex(MariaDBTable table, Set<String> existingSignatures) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        StringBuilder sb = new StringBuilder("CREATE ");
        boolean unique = Randomly.getBoolean();
        if (unique) {
            sb.append("UNIQUE ");
        }
        String idxName = "comp_" + DBMSCommon.createColumnName(Randomly.smallNumber());
        sb.append("INDEX ");
        sb.append(idxName);
        if (Randomly.getBoolean()) {
            sb.append(" USING ");
            sb.append(Randomly.fromOptions("BTREE", "HASH"));
        }
        sb.append(" ON ");
        sb.append(table.getName());
        sb.append("(");

        // Generate 2-3 column composite index
        int nr = Math.min(table.getColumns().size(), Randomly.fromOptions(2, 2, 3));
        List<MariaDBColumn> columns = Randomly.nonEmptySubset(table.getColumns());
        while (columns.size() > nr) {
            columns.remove(columns.size() - 1);
        }
        if (columns.size() < 2 && table.getColumns().size() >= 2) {
            List<MariaDBColumn> shuffled = new ArrayList<>(table.getColumns());
            Collections.shuffle(shuffled);
            columns = shuffled.subList(0, Math.min(2, shuffled.size()));
        }

        StringBuilder colSpec = new StringBuilder();
        for (int i = 0; i < columns.size(); i++) {
            if (i != 0) {
                sb.append(", ");
                colSpec.append(",");
            }
            sb.append(columns.get(i).getName());
            colSpec.append(columns.get(i).getName());
            if (Randomly.getBoolean()) {
                String order = Randomly.fromOptions("ASC", "DESC");
                sb.append(" ");
                sb.append(order);
                colSpec.append(order);
            }
        }
        sb.append(")");

        String signature = (unique ? "U:" : "") + colSpec.toString();
        if (existingSignatures.contains(signature)) {
            return null;
        }

        return new SQLQueryAdapter(sb.toString(), errors, true);
    }

    /**
     * Phase F3: Create an index with VISIBLE/INVISIBLE option.
     * MariaDB 10.6+ supports CREATE INDEX ... INVISIBLE.
     */
    public static SQLQueryAdapter createIndexWithVisibility(MariaDBTable table, MariaDBColumn col) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        errors.add("INVISIBLE");
        errors.add("VISIBLE");

        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "vis_" + Math.abs(colName.hashCode() % 10000);
        boolean invisible = Randomly.getBoolean();

        return new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ")"
                        + (invisible ? " INVISIBLE" : " VISIBLE") + ";",
                errors, true);
    }

    /**
     * Phase F3: Toggle an existing index between VISIBLE and INVISIBLE.
     * Uses ALTER TABLE ... ALTER INDEX ... syntax.
     */
    public static SQLQueryAdapter toggleIndexVisibility(MariaDBTable table, String idxName, boolean invisible) {
        ExpectedErrors errors = new ExpectedErrors();
        addCommonIndexErrors(errors);
        errors.add("INVISIBLE");
        errors.add("VISIBLE");

        return new SQLQueryAdapter(
                "ALTER TABLE " + table.getName() + " ALTER INDEX " + idxName
                        + (invisible ? " INVISIBLE" : " VISIBLE") + ";",
                errors, true);
    }
}