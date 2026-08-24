package idxdiff.postgres.gen;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import idxdiff.Randomly;
import idxdiff.common.DBMSCommon;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.postgres.PostgresGlobalState;
import idxdiff.postgres.PostgresSchema;
import idxdiff.postgres.PostgresSchema.PostgresColumn;
import idxdiff.postgres.PostgresSchema.PostgresDataType;
import idxdiff.postgres.PostgresSchema.PostgresTable;
import idxdiff.postgres.PostgresVisitor;
import idxdiff.postgres.ast.PostgresExpression;

public class PostgresTableGenerator {

    private final String tableName;
    private boolean columnCanHavePrimaryKey;
    private boolean columnHasPrimaryKey;
    private final StringBuilder sb = new StringBuilder();
    private boolean isTemporaryTable;
    private boolean isPartitionedTable;
    private final PostgresSchema newSchema;
    private final List<PostgresColumn> columnsToBeAdded = new ArrayList<>();
    protected final ExpectedErrors errors = new ExpectedErrors();
    private final PostgresTable table;
    private final boolean generateOnlyKnown;
    private final PostgresGlobalState globalState;

    public PostgresTableGenerator(String tableName, PostgresSchema newSchema, boolean generateOnlyKnown,
            PostgresGlobalState globalState) {
        this.tableName = tableName;
        this.newSchema = newSchema;
        this.generateOnlyKnown = generateOnlyKnown;
        this.globalState = globalState;
        table = new PostgresTable(tableName, columnsToBeAdded, null, null, null, false, false);
        errors.add("invalid input syntax for");
        errors.add("is not unique");
        errors.add("integer out of range");
        errors.add("division by zero");
        errors.add("cannot create partitioned table as inheritance child");
        errors.add("cannot cast");
        errors.add("ERROR: functions in index expression must be marked IMMUTABLE");
        errors.add("functions in partition key expression must be marked IMMUTABLE");
        errors.add("functions in index predicate must be marked IMMUTABLE");
        errors.add("has no default operator class for access method");
        errors.add("does not exist for access method");
        errors.add("does not accept data type");
        errors.add("but default expression is of type text");
        errors.add("has pseudo-type unknown");
        errors.add("no collation was derived for partition key column");
        errors.add("inherits from generated column but specifies identity");
        errors.add("inherits from generated column but specifies default");
        PostgresCommon.addCommonExpressionErrors(errors);
        PostgresCommon.addCommonTableErrors(errors);
    }

    public static SQLQueryAdapter generate(String tableName, PostgresSchema newSchema, boolean generateOnlyKnown,
            PostgresGlobalState globalState) {
        return new PostgresTableGenerator(tableName, newSchema, generateOnlyKnown, globalState).generate();
    }

    protected SQLQueryAdapter generate() {
        columnCanHavePrimaryKey = true;
        sb.append("CREATE");
        if (Randomly.getBoolean()) {
            sb.append(" ");
            isTemporaryTable = true;
            sb.append(Randomly.fromOptions("TEMPORARY", "TEMP"));
        } else if (Randomly.getBoolean()) {
            sb.append(" UNLOGGED");
        }
        sb.append(" TABLE");
        if (Randomly.getBoolean()) {
            sb.append(" IF NOT EXISTS");
        }
        sb.append(" ");
        sb.append(tableName);
        if (Randomly.getBoolean() && !newSchema.getDatabaseTables().isEmpty()) {
            createLike();
        } else {
            createStandard();
        }
        return new SQLQueryAdapter(sb.toString(), errors, true);
    }

    private void createStandard() throws AssertionError {
        // [FIX] Decide partitioning BEFORE creating columns, because PostgreSQL does not
        // support PRIMARY KEY constraints on partitioned tables (PG < 11).
        decidePartitioning();
        if (isPartitionedTable) {
            // [FIX] Prevent any PRIMARY KEY constraints on partitioned tables
            columnCanHavePrimaryKey = false;
        }
        sb.append("(");
        // [P0-FIX] Ensure at least 2 columns, and column 0 is always SERIAL PRIMARY KEY
        // This gives index oracle a meaningful PK column to work with
        int nrColumns = Math.max(2, Randomly.smallNumber() + 1);
        // Column 0: SERIAL PRIMARY KEY (skip PK if table will be partitioned)
        createIndexFriendlyFirstColumn();
        for (int i = 1; i < nrColumns; i++) {
            sb.append(", ");
            String name = DBMSCommon.createColumnName(i);
            createColumn(name);
        }
        if (Randomly.getBoolean()) {
            errors.add("constraints on temporary tables may reference only temporary tables");
            errors.add("constraints on unlogged tables may reference only permanent or unlogged tables");
            errors.add("constraints on permanent tables may reference only permanent tables");
            errors.add("cannot be implemented");
            errors.add("there is no unique constraint matching given keys for referenced table");
            errors.add("cannot reference partitioned table");
            errors.add("unsupported ON COMMIT and foreign key combination");
            errors.add("ERROR: invalid ON DELETE action for foreign key constraint containing generated column");
            errors.add("exclusion constraints are not supported on partitioned tables");
            PostgresCommon.addTableConstraints(columnHasPrimaryKey, sb, table, globalState, errors);
        }
        sb.append(")");
        generateInherits();
        generatePartitionBy();
        generateUsing();
        if (!isPartitionedTable) {
            PostgresCommon.generateWith(sb, globalState, errors);
        }
        if (Randomly.getBoolean() && isTemporaryTable) {
            sb.append(" ON COMMIT ");
            sb.append(Randomly.fromOptions("PRESERVE ROWS", "DELETE ROWS", "DROP"));
            sb.append(" ");
        }
    }

    private void createLike() {
        sb.append("(");
        sb.append("LIKE ");
        sb.append(newSchema.getRandomTable().getName());
        if (Randomly.getBoolean()) {
            for (int i = 0; i < Randomly.smallNumber(); i++) {
                String option = Randomly.fromOptions("DEFAULTS", "CONSTRAINTS", "INDEXES", "STORAGE", "COMMENTS",
                        "GENERATED", "IDENTITY", "STATISTICS", "STORAGE", "ALL");
                sb.append(" ");
                sb.append(Randomly.fromOptions("INCLUDING", "EXCLUDING"));
                sb.append(" ");
                sb.append(option);
            }
        }
        sb.append(")");
    }

    /**
     * [FIX] Decide upfront whether this table will be partitioned, so that column
     * generation can avoid producing PRIMARY KEY constraints (which are not allowed
     * on partitioned tables in PG < 11).
     */
    private void decidePartitioning() {
        isPartitionedTable = !Randomly.getBoolean();
    }

    /**
     * [P0-FIX] Create the first column as SERIAL PRIMARY KEY.
     * SERIAL auto-creates a sequence and INT column. PRIMARY KEY ensures
     * index oracle modes have a deterministic indexed column to work with.
     * [FIX] Skip PRIMARY KEY for partitioned tables — PG does not support it.
     */
    private void createIndexFriendlyFirstColumn() {
        String name = DBMSCommon.createColumnName(0);
        sb.append(name);
        if (isPartitionedTable) {
            // PostgreSQL < 11 does not support PRIMARY KEY on partitioned tables
            sb.append(" SERIAL");
        } else {
            sb.append(" SERIAL PRIMARY KEY");
            columnHasPrimaryKey = true;
        }
        PostgresColumn c = new PostgresColumn(name, PostgresDataType.INT);
        c.setTable(table);
        columnsToBeAdded.add(c);
    }

    private void createColumn(String name) throws AssertionError {
        sb.append(name);
        sb.append(" ");
        PostgresDataType type = PostgresDataType.getRandomType();
        boolean serial = PostgresCommon.appendDataType(type, sb, true, generateOnlyKnown, globalState.getCollates());
        PostgresColumn c = new PostgresColumn(name, type);
        c.setTable(table);
        columnsToBeAdded.add(c);
        sb.append(" ");
        if (Randomly.getBoolean()) {
            createColumnConstraint(type, serial);
        }
    }

    private void generatePartitionBy() {
        // [FIX] Use the pre-decided partitioning flag instead of re-randomizing.
        // The decision was made in decidePartitioning() before column generation,
        // so that PRIMARY KEY constraints can be avoided for partitioned tables.
        if (!isPartitionedTable) {
            return;
        }
        sb.append(" PARTITION BY ");
        // TODO "RANGE",
        String partitionOption = Randomly.fromOptions("RANGE", "LIST", "HASH");
        sb.append(partitionOption);
        sb.append("(");
        errors.add("unrecognized parameter");
        errors.add("cannot use constant expression");
        errors.add("cannot add NO INHERIT constraint to partitioned table");
        errors.add("unrecognized parameter");
        errors.add("unsupported PRIMARY KEY constraint with partition key definition");
        errors.add("which is part of the partition key.");
        errors.add("unsupported UNIQUE constraint with partition key definition");
        errors.add("does not accept data type");
        int n = partitionOption.contentEquals("LIST") ? 1 : Randomly.smallNumber() + 1;
        PostgresCommon.addCommonExpressionErrors(errors);
        for (int i = 0; i < n; i++) {
            if (i != 0) {
                sb.append(", ");
            }
            sb.append("(");
            PostgresExpression expr = PostgresExpressionGenerator.generateExpression(globalState, columnsToBeAdded);
            sb.append(PostgresVisitor.asString(expr));
            sb.append(")");
            if (Randomly.getBoolean()) {
                sb.append(globalState.getRandomOpclass());
                errors.add("does not exist for access method");
            }
        }
        sb.append(")");
    }

    private void generateUsing() {
        /*
         * Postgres does not allow specifying USING clause for partitioned tables since they don't have any storage
         * associated with them
         */
        if (isPartitionedTable) {
            return;
        }
        if (Randomly.getBoolean()) {
            return;
        }
        String accessMethod = globalState.getRandomTableAccessMethod();
        if (accessMethod == null) {
            return;
        }
        sb.append(" USING ");
        sb.append(accessMethod);
    }

    private void generateInherits() {
        if (Randomly.getBoolean() && !newSchema.getDatabaseTablesWithoutViews().isEmpty()) {
            sb.append(" INHERITS(");
            sb.append(newSchema.getDatabaseTablesRandomSubsetNotEmpty().stream().map(t -> t.getName())
                    .collect(Collectors.joining(", ")));
            sb.append(")");
            errors.add("has a type conflict");
            errors.add("has a generation conflict");
            errors.add("cannot create partitioned table as inheritance child");
            errors.add("cannot inherit from temporary relation");
            errors.add("cannot inherit from partitioned table");
            errors.add("has a collation conflict");
            errors.add("inherits conflicting default values");
            errors.add("specifies generation expression");
        }
    }

    private enum ColumnConstraint {
        NULL_OR_NOT_NULL, UNIQUE, PRIMARY_KEY, DEFAULT, CHECK, GENERATED
    };

    private void createColumnConstraint(PostgresDataType type, boolean serial) {
        List<ColumnConstraint> constraintSubset = Randomly.nonEmptySubset(ColumnConstraint.values());
        if (Randomly.getBoolean()) {
            // make checks constraints less likely
            constraintSubset.remove(ColumnConstraint.CHECK);
        }
        if (!columnCanHavePrimaryKey || columnHasPrimaryKey) {
            constraintSubset.remove(ColumnConstraint.PRIMARY_KEY);
        }
        if (constraintSubset.contains(ColumnConstraint.GENERATED)
                && constraintSubset.contains(ColumnConstraint.DEFAULT)) {
            // otherwise: ERROR: both default and identity specified for column
            constraintSubset.remove(Randomly.fromOptions(ColumnConstraint.GENERATED, ColumnConstraint.DEFAULT));
        }
        if (constraintSubset.contains(ColumnConstraint.GENERATED) && type != PostgresDataType.INT) {
            // otherwise: ERROR: identity column type must be smallint, integer, or bigint
            constraintSubset.remove(ColumnConstraint.GENERATED);
        }
        if (serial) {
            constraintSubset.remove(ColumnConstraint.GENERATED);
            constraintSubset.remove(ColumnConstraint.DEFAULT);
            constraintSubset.remove(ColumnConstraint.NULL_OR_NOT_NULL);

        }
        for (ColumnConstraint c : constraintSubset) {
            sb.append(" ");
            switch (c) {
            case NULL_OR_NOT_NULL:
                sb.append(Randomly.fromOptions("NOT NULL", "NULL"));
                errors.add("conflicting NULL/NOT NULL declarations");
                break;
            case UNIQUE:
                sb.append("UNIQUE");
                break;
            case PRIMARY_KEY:
                sb.append("PRIMARY KEY");
                columnHasPrimaryKey = true;
                break;
            case DEFAULT:
                sb.append("DEFAULT");
                sb.append(" (");
                sb.append(PostgresVisitor.asString(PostgresExpressionGenerator.generateExpression(globalState, type)));
                sb.append(")");
                // CREATE TEMPORARY TABLE t1(c0 smallint DEFAULT ('566963878'));
                errors.add("out of range");
                errors.add("is a generated column");
                break;
            case CHECK:
                sb.append("CHECK (");
                sb.append(PostgresVisitor.asString(PostgresExpressionGenerator.generateExpression(globalState,
                        columnsToBeAdded, PostgresDataType.BOOLEAN)));
                sb.append(")");
                if (Randomly.getBoolean()) {
                    sb.append(" NO INHERIT");
                }
                errors.add("out of range");
                break;
            case GENERATED:
                sb.append("GENERATED ");
                if (Randomly.getBoolean()) {
                    sb.append(" ALWAYS AS (");
                    sb.append(PostgresVisitor.asString(
                            PostgresExpressionGenerator.generateExpression(globalState, columnsToBeAdded, type)));
                    sb.append(") STORED");
                    errors.add("A generated column cannot reference another generated column.");
                    errors.add("cannot use generated column in partition key");
                    errors.add("generation expression is not immutable");
                    errors.add("cannot use column reference in DEFAULT expression");
                } else {
                    sb.append(Randomly.fromOptions("ALWAYS", "BY DEFAULT"));
                    sb.append(" AS IDENTITY");
                }
                break;
            default:
                throw new AssertionError(sb);
            }
        }
    }

}
