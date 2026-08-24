package idxdiff.mysql.gen.datadef;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mysql.MySQLBugs;
import idxdiff.mysql.MySQLErrors;
import idxdiff.mysql.MySQLGlobalState;
import idxdiff.mysql.MySQLSchema;
import idxdiff.mysql.MySQLSchema.MySQLColumn;
import idxdiff.mysql.MySQLSchema.MySQLDataType;
import idxdiff.mysql.MySQLSchema.MySQLTable;
import idxdiff.mysql.MySQLSchema.MySQLTable.MySQLEngine;
import idxdiff.mysql.MySQLVisitor;
import idxdiff.mysql.ast.MySQLExpression;
import idxdiff.mysql.gen.MySQLExpressionGenerator;

public class MySQLIndexGenerator {

    private final Randomly r;
    private StringBuilder sb = new StringBuilder();
    private boolean columnIsPrimaryKey;
    private boolean containsInPlace;
    private boolean isUnique;
    private MySQLSchema schema;
    private final MySQLGlobalState globalState;

    public MySQLIndexGenerator(MySQLSchema schema, Randomly r, MySQLGlobalState globalState) {
        this.schema = schema;
        this.r = r;
        this.globalState = globalState;
    }

    public static SQLQueryAdapter create(MySQLGlobalState globalState) {
        return new MySQLIndexGenerator(globalState.getSchema(), globalState.getRandomly(), globalState).create();
    }

    public SQLQueryAdapter create() {
        ExpectedErrors errors = new ExpectedErrors();
        MySQLErrors.addExpressionErrors(errors);
        sb.append("CREATE ");
        isUnique = false;
        if (Randomly.getBoolean()) {
            // "FULLTEXT" TODO Column 'c3' cannot be part of FULLTEXT index
            // A SPATIAL index may only contain a geometrical type column
            sb.append("UNIQUE ");
            isUnique = true;
            errors.add("Duplicate entry");
        }
        sb.append("INDEX ");
        sb.append(globalState.getSchema().getFreeIndexName());
        indexType();
        sb.append(" ON ");
        MySQLTable table = schema.getRandomTable();
        // ARCHIVE engine only allows 1 key (PRIMARY KEY), which already exists.
        // Skip CREATE INDEX on ARCHIVE tables to avoid "Too many keys specified" errors.
        if (table.getEngine() == MySQLEngine.ARCHIVE) {
            return new SQLQueryAdapter("SELECT 1", errors, false);
        }
        MySQLExpressionGenerator gen = new MySQLExpressionGenerator(globalState).setColumns(table.getColumns());
        sb.append(table.getName());
        sb.append("(");
        // Prefer column-based indexes (80%) over expression-based (20%)
        // Column-based indexes are index-friendly for simple WHERE conditions
        boolean useColumnBased = !(table.getEngine() == MySQLEngine.INNO_DB && Randomly.getBooleanWithRatherLowProbability());
        if (!useColumnBased) {
            // Exclude AUTO_INCREMENT columns from functional index expressions —
            // MySQL rejects functional indexes that reference AUTO_INCREMENT columns.
            List<MySQLColumn> exprColumns = new ArrayList<>();
            for (MySQLColumn c : table.getColumns()) {
                if (!c.isAutoIncrement()) {
                    exprColumns.add(c);
                }
            }
            if (exprColumns.isEmpty()) {
                // All columns are AUTO_INCREMENT, fall back to column-based index
                useColumnBased = true;
            } else {
                gen.setColumns(exprColumns);
                for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
                    if (i != 0) {
                        sb.append(", ");
                    }
                    sb.append("(");
                    MySQLExpression randExpr = gen.generateExpression();
                    sb.append(MySQLVisitor.asString(randExpr));
                    sb.append(")");

                }
            }
        }
        if (useColumnBased) {
            // For UNIQUE indexes, exclude AUTO_INCREMENT columns
            // to prevent MySQL "auto_increment resequencing" error.
            // Non-unique indexes on AUTO_INCREMENT columns are fine.
            List<MySQLColumn> candidateColumns = new ArrayList<>();
            for (MySQLColumn c : table.getColumns()) {
                if (!isUnique || !c.isAutoIncrement()) {
                    candidateColumns.add(c);
                }
            }
            if (candidateColumns.isEmpty()) {
                // All columns are AUTO_INCREMENT — cannot create UNIQUE index on them.
                // Fall back to a harmless no-op query.
                return new SQLQueryAdapter("SELECT 1", errors, false);
            }

            // Composite index: 50% chance of 2-3 columns for multi-column index testing
            List<MySQLColumn> randomColumn;
            if (Randomly.getBoolean()) {
                // Multi-column composite index: pick 2-3 columns specifically
                int numCols = Math.min(candidateColumns.size(), Randomly.fromOptions(2, 2, 3));
                randomColumn = new ArrayList<>();
                List<MySQLColumn> shuffled = new ArrayList<>(candidateColumns);
                Collections.shuffle(shuffled);
                for (int i = 0; i < numCols && i < shuffled.size(); i++) {
                    randomColumn.add(shuffled.get(i));
                }
            } else {
                randomColumn = new ArrayList<>();
                List<MySQLColumn> shuffled = new ArrayList<>(candidateColumns);
                Collections.shuffle(shuffled);
                int numCols = Math.min(candidateColumns.size(), Randomly.smallNumber() + 1);
                for (int i = 0; i < numCols; i++) {
                    randomColumn.add(shuffled.get(i));
                }
            }
            int i = 0;
            for (MySQLColumn c : randomColumn) {
                if (i++ != 0) {
                    sb.append(", ");
                }
                if (c.isPrimaryKey()) {
                    columnIsPrimaryKey = true;
                }
                sb.append(c.getName());
                if (Randomly.getBoolean() && c.getType() == MySQLDataType.VARCHAR) {
                    sb.append("(");
                    if (MySQLBugs.bug114534) {
                        sb.append(r.getInteger(2, 5));
                    } else {
                        sb.append(r.getInteger(1, 5));
                    }
                    sb.append(")");
                }
                if (Randomly.getBoolean()) {
                    sb.append(" ");
                    sb.append(Randomly.fromOptions("ASC", "DESC"));
                }
            }
        }
        sb.append(")");
        indexOption();
        algorithmOption();
        String string = sb.toString();
        sb = new StringBuilder();
        if (containsInPlace) {
            errors.add("ALGORITHM=INPLACE is not supported");
        }
        if (table.getEngine() == MySQLEngine.ARCHIVE) {
            errors.add("Table handler doesn't support NULL in given index.");
        }
        errors.add("A primary key index cannot be invisible");
        errors.add("Functional index on a column is not supported. Consider using a regular index instead.");
        errors.add("cannot refer to an auto-increment column");
        errors.add("auto_increment resequencing");
        errors.add("Incorrect usage of spatial/fulltext/hash index and explicit index order");
        errors.add("The storage engine for the table doesn't support descending indexes");
        errors.add("must include all columns");
        errors.add("cannot index the expression");
        errors.add("Data truncation: Truncated incorrect");
        errors.add("a disallowed function.");
        errors.add("Data truncation");
        errors.add("Cannot create a functional index on an expression that returns a BLOB or TEXT.");
        errors.add("used in key specification without a key length");
        errors.add("can't be used in key specification with the used table type");
        errors.add("Specified key was too long");
        errors.add("out of range");
        errors.add("Data truncated for functional index");
        errors.add("used in key specification without a key length");
        errors.add("Row size too large"); // seems to happen together with MIN_ROWS in the table declaration
        errors.add("Too many keys specified; max 64 keys allowed");
        errors.add("Duplicate key name");
        return new SQLQueryAdapter(string, errors, true);
    }

    private void algorithmOption() {
        if (Randomly.getBoolean()) {
            sb.append(" ALGORITHM");
            if (Randomly.getBoolean()) {
                sb.append("=");
            }
            sb.append(" ");
            String fromOptions = Randomly.fromOptions("DEFAULT", "INPLACE", "COPY");
            if (fromOptions.contentEquals("INPLACE")) {
                containsInPlace = true;
            }
            sb.append(fromOptions);
        }
    }

    private void indexOption() {
        if (Randomly.getBoolean()) {
            sb.append(" ");
            if (columnIsPrimaryKey) {
                // The explicit primary key cannot be made invisible.
                sb.append("VISIBLE");
            } else {
                sb.append(Randomly.fromOptions("VISIBLE", "INVISIBLE"));
            }
        }
    }

    private void indexType() {
        if (Randomly.getBoolean()) {
            sb.append(" USING ");
            sb.append(Randomly.fromOptions("BTREE", "HASH"));
        }
    }

    public void setNewSchema(MySQLSchema schema) {
        this.schema = schema;
    }
}
