package idxdiff.postgres;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLIntegrityConstraintViolationException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.postgresql.util.PSQLException;

import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.SQLConnection;
import idxdiff.common.DBMSCommon;
import idxdiff.common.schema.AbstractRelationalTable;
import idxdiff.common.schema.AbstractRowValue;
import idxdiff.common.schema.AbstractSchema;
import idxdiff.common.schema.AbstractTableColumn;
import idxdiff.common.schema.AbstractTables;
import idxdiff.common.schema.TableIndex;
import idxdiff.postgres.PostgresSchema.PostgresTable;
import idxdiff.postgres.PostgresSchema.PostgresTable.TableType;
import idxdiff.postgres.ast.PostgresConstant;

public class PostgresSchema extends AbstractSchema<PostgresGlobalState, PostgresTable> {

    private final String databaseName;

    public enum PostgresDataType {
        INT, BOOLEAN, TEXT, DECIMAL, FLOAT, REAL, RANGE, MONEY, BIT, INET;

        public static PostgresDataType getRandomType() {
            List<PostgresDataType> dataTypes = new ArrayList<>(Arrays.asList(values()));
            if (PostgresProvider.generateOnlyKnown) {
                dataTypes.remove(PostgresDataType.DECIMAL);
                dataTypes.remove(PostgresDataType.FLOAT);
                dataTypes.remove(PostgresDataType.REAL);
                dataTypes.remove(PostgresDataType.INET);
                dataTypes.remove(PostgresDataType.RANGE);
                dataTypes.remove(PostgresDataType.MONEY);
                dataTypes.remove(PostgresDataType.BIT);
            }
            return Randomly.fromList(dataTypes);
        }
    }

    public static class PostgresColumn extends AbstractTableColumn<PostgresTable, PostgresDataType> {

        private final boolean isGenerated;
        private final boolean hasSequenceDefault;

        public PostgresColumn(String name, PostgresDataType columnType, boolean isGenerated, boolean hasSequenceDefault) {
            super(name, null, columnType);
            this.isGenerated = isGenerated;
            this.hasSequenceDefault = hasSequenceDefault;
        }

        public PostgresColumn(String name, PostgresDataType columnType) {
            this(name, columnType, false, false);
        }

        public boolean isGenerated() {
            return isGenerated;
        }

        /**
         * Returns true if this column has a nextval()-based default (SERIAL, BIGSERIAL, IDENTITY).
         * Such columns should NOT receive explicit values in INSERT — let the sequence handle them.
         */
        public boolean hasSequenceDefault() {
            return hasSequenceDefault;
        }

        public static PostgresColumn createDummy(String name) {
            return new PostgresColumn(name, PostgresDataType.INT, false, false);
        }

    }

    public static class PostgresTables extends AbstractTables<PostgresTable, PostgresColumn> {

        public PostgresTables(List<PostgresTable> tables) {
            super(tables);
        }

        public PostgresRowValue getRandomRowValue(SQLConnection con) throws SQLException {
            String randomRow = String.format("SELECT %s FROM %s ORDER BY RANDOM() LIMIT 1", columnNamesAsString(
                    c -> c.getTable().getName() + "." + c.getName() + " AS " + c.getTable().getName() + c.getName()),
                    // columnNamesAsString(c -> "typeof(" + c.getTable().getName() + "." +
                    // c.getName() + ")")
                    tableNamesAsString());
            Map<PostgresColumn, PostgresConstant> values = new HashMap<>();
            try (Statement s = con.createStatement()) {
                ResultSet randomRowValues = s.executeQuery(randomRow);
                if (!randomRowValues.next()) {
                    throw new AssertionError("could not find random row! " + randomRow + "\n");
                }
                for (int i = 0; i < getColumns().size(); i++) {
                    PostgresColumn column = getColumns().get(i);
                    int columnIndex = randomRowValues.findColumn(column.getTable().getName() + column.getName());
                    assert columnIndex == i + 1;
                    PostgresConstant constant;
                    if (randomRowValues.getString(columnIndex) == null) {
                        constant = PostgresConstant.createNullConstant();
                    } else {
                        switch (column.getType()) {
                        case INT:
                            constant = PostgresConstant.createIntConstant(randomRowValues.getLong(columnIndex));
                            break;
                        case BOOLEAN:
                            constant = PostgresConstant.createBooleanConstant(randomRowValues.getBoolean(columnIndex));
                            break;
                        case TEXT:
                            constant = PostgresConstant.createTextConstant(randomRowValues.getString(columnIndex));
                            break;
                        default:
                            throw new IgnoreMeException();
                        }
                    }
                    values.put(column, constant);
                }
                assert !randomRowValues.next();
                return new PostgresRowValue(this, values);
            } catch (PSQLException e) {
                throw new IgnoreMeException();
            }

        }

    }

    public static PostgresDataType getColumnType(String typeString) {
        switch (typeString) {
        case "smallint":
        case "integer":
        case "bigint":
            return PostgresDataType.INT;
        case "boolean":
            return PostgresDataType.BOOLEAN;
        case "text":
        case "character":
        case "character varying":
        case "name":
        case "regclass":
            return PostgresDataType.TEXT;
        case "numeric":
            return PostgresDataType.DECIMAL;
        case "double precision":
            return PostgresDataType.FLOAT;
        case "real":
            return PostgresDataType.REAL;
        case "int4range":
            return PostgresDataType.RANGE;
        case "money":
            return PostgresDataType.MONEY;
        case "bit":
        case "bit varying":
            return PostgresDataType.BIT;
        case "inet":
            return PostgresDataType.INET;
        default:
            throw new AssertionError(typeString);
        }
    }

    public static class PostgresRowValue extends AbstractRowValue<PostgresTables, PostgresColumn, PostgresConstant> {

        protected PostgresRowValue(PostgresTables tables, Map<PostgresColumn, PostgresConstant> values) {
            super(tables, values);
        }

    }

    public static class PostgresTable
            extends AbstractRelationalTable<PostgresColumn, PostgresIndex, PostgresGlobalState> {

        public enum TableType {
            STANDARD, TEMPORARY
        }

        private final TableType tableType;
        private final List<PostgresStatisticsObject> statistics;
        private final boolean isInsertable;
        private final boolean isPartitioned;

        public PostgresTable(String tableName, List<PostgresColumn> columns, List<PostgresIndex> indexes,
                TableType tableType, List<PostgresStatisticsObject> statistics, boolean isView, boolean isInsertable) {
            super(tableName, columns, indexes, isView);
            this.statistics = statistics;
            this.isInsertable = isInsertable;
            this.tableType = tableType;
            // TODO: simple adapter for other implementations
            this.isPartitioned = false;
        }

        public PostgresTable(String tableName, List<PostgresColumn> columns, List<PostgresIndex> indexes,
                TableType tableType, List<PostgresStatisticsObject> statistics, boolean isView, boolean isInsertable,
                boolean isPartitioned) {
            super(tableName, columns, indexes, isView);
            this.statistics = statistics;
            this.isInsertable = isInsertable;
            this.tableType = tableType;
            this.isPartitioned = isPartitioned;
        }

        public List<PostgresStatisticsObject> getStatistics() {
            return statistics;
        }

        public TableType getTableType() {
            return tableType;
        }

        public boolean isInsertable() {
            return isInsertable;
        }

        public boolean isPartitioned() {
            return isPartitioned;
        }

    }

    public static final class PostgresStatisticsObject {
        private final String name;

        public PostgresStatisticsObject(String name) {
            this.name = name;
        }

        public String getName() {
            return name;
        }
    }

    public static final class PostgresIndex extends TableIndex {
        private final List<String> columnNames;
        private final boolean isUnique;

        private PostgresIndex(String indexName, List<String> columnNames, boolean isUnique) {
            super(indexName);
            this.columnNames = columnNames != null ? columnNames : new ArrayList<>();
            this.isUnique = isUnique;
        }

        public static PostgresIndex create(String indexName, List<String> columnNames, boolean isUnique) {
            return new PostgresIndex(indexName, columnNames, isUnique);
        }

        public static PostgresIndex create(String indexName) {
            return new PostgresIndex(indexName, new ArrayList<>(), false);
        }

        @Override
        public String getIndexName() {
            if (super.getIndexName().contentEquals("PRIMARY")) {
                return "`PRIMARY`";
            } else {
                return super.getIndexName();
            }
        }

        public List<String> getColumnNames() {
            return columnNames;
        }

        public boolean isUnique() {
            return isUnique;
        }
    }

    public static PostgresSchema fromConnection(SQLConnection con, String databaseName) throws SQLException {
        try {
            List<PostgresTable> databaseTables = new ArrayList<>();
            try (Statement s = con.createStatement()) {
                try (ResultSet rs = s.executeQuery(
                        "SELECT t.table_name, t.table_schema, t.table_type, t.is_insertable_into, c.relkind FROM information_schema.tables t JOIN pg_class c ON c.relname = t.table_name JOIN pg_namespace n ON n.oid = c.relnamespace AND n.nspname = t.table_schema WHERE t.table_schema='public' OR t.table_schema LIKE 'pg_temp_%' ORDER BY t.table_name;")) {
                    while (rs.next()) {
                        String tableName = rs.getString("table_name");
                        String tableTypeSchema = rs.getString("table_schema");
                        boolean isInsertable = rs.getBoolean("is_insertable_into");
                        String relkind = rs.getString("relkind");
                        boolean isPartitioned = "p".equals(relkind);
                        // Use relkind from pg_class to reliably detect views:
                        // 'v' = view, 'm' = materialized view
                        // Previously used matchesViewName() which only checked if name starts with "v",
                        // causing false negatives for views with other naming patterns.
                        boolean isView = "v".equals(relkind) || "m".equals(relkind);
                        PostgresTable.TableType tableType = getTableType(tableTypeSchema);
                        List<PostgresColumn> databaseColumns = getTableColumns(con, tableName);
                        List<PostgresIndex> indexes = getIndexes(con, tableName);
                        List<PostgresStatisticsObject> statistics = getStatistics(con);
                        PostgresTable t = new PostgresTable(tableName, databaseColumns, indexes, tableType, statistics,
                                isView, isInsertable, isPartitioned);
                        for (PostgresColumn c : databaseColumns) {
                            c.setTable(t);
                        }
                        databaseTables.add(t);
                    }
                }
            }
            return new PostgresSchema(databaseTables, databaseName);
        } catch (SQLIntegrityConstraintViolationException e) {
            throw new AssertionError(e);
        }
    }

    protected static List<PostgresStatisticsObject> getStatistics(SQLConnection con) throws SQLException {
        List<PostgresStatisticsObject> statistics = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery("SELECT stxname FROM pg_statistic_ext ORDER BY stxname;")) {
                while (rs.next()) {
                    statistics.add(new PostgresStatisticsObject(rs.getString("stxname")));
                }
            }
        }
        return statistics;
    }

    protected static PostgresTable.TableType getTableType(String tableTypeStr) throws AssertionError {
        PostgresTable.TableType tableType;
        if (tableTypeStr.contentEquals("public")) {
            tableType = TableType.STANDARD;
        } else if (tableTypeStr.startsWith("pg_temp")) {
            tableType = TableType.TEMPORARY;
        } else {
            throw new AssertionError(tableTypeStr);
        }
        return tableType;
    }

    protected static List<PostgresIndex> getIndexes(SQLConnection con, String tableName) throws SQLException {
        // Query pg_indexes for name, then pg_attribute for column details
        Map<String, List<String>> indexColumns = new HashMap<>();
        Map<String, Boolean> indexUnique = new HashMap<>();

        // Get column details from pg_attribute + pg_index for accurate column info + uniqueness
        try (Statement s = con.createStatement()) {
            String detailQuery = String.format(
                "SELECT i.relname AS indexname, a.attname AS columnname, NOT idx.indisunique AS non_unique "
                + "FROM pg_index idx "
                + "JOIN pg_class t ON t.oid = idx.indrelid "
                + "JOIN pg_class i ON i.oid = idx.indexrelid "
                + "JOIN pg_attribute a ON a.attrelid = t.oid AND a.attnum = ANY(idx.indkey) "
                + "JOIN pg_namespace n ON n.oid = t.relnamespace "
                + "WHERE t.relname = '%s' AND (n.nspname = 'public' OR n.nspname LIKE 'pg_temp_%%') "
                + "ORDER BY i.relname, a.attnum;",
                tableName);
            try (ResultSet rs = s.executeQuery(detailQuery)) {
                while (rs.next()) {
                    String idxName = rs.getString("indexname");
                    String colName = rs.getString("columnname");
                    boolean nonUnique = rs.getBoolean("non_unique");
                    if (DBMSCommon.matchesIndexName(idxName)) {
                        indexColumns.computeIfAbsent(idxName, k -> new ArrayList<>()).add(colName);
                        indexUnique.putIfAbsent(idxName, !nonUnique);
                    }
                }
            }
        }

        List<PostgresIndex> indexes = new ArrayList<>();
        for (Map.Entry<String, List<String>> entry : indexColumns.entrySet()) {
            String idxName = entry.getKey();
            List<String> cols = entry.getValue();
            boolean unique = indexUnique.getOrDefault(idxName, false);
            indexes.add(PostgresIndex.create(idxName, cols, unique));
        }

        // Fallback: if pg_attribute query found nothing, use pg_indexes
        if (indexes.isEmpty()) {
            try (Statement s = con.createStatement()) {
                try (ResultSet rs = s.executeQuery(String.format(
                        "SELECT indexname FROM pg_indexes WHERE tablename='%s' ORDER BY indexname;", tableName))) {
                    while (rs.next()) {
                        String indexName = rs.getString("indexname");
                        if (DBMSCommon.matchesIndexName(indexName)) {
                            indexes.add(PostgresIndex.create(indexName));
                        }
                    }
                }
            }
        }
        return indexes;
    }

    protected static List<PostgresColumn> getTableColumns(SQLConnection con, String tableName) throws SQLException {
        List<PostgresColumn> columns = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s
                    .executeQuery("select column_name, data_type, is_generated, column_default from INFORMATION_SCHEMA.COLUMNS where table_name = '"
                            + tableName + "' ORDER BY column_name")) {
                while (rs.next()) {
                    String columnName = rs.getString("column_name");
                    String dataType = rs.getString("data_type");
                    String isGenerated = rs.getString("is_generated");
                    boolean generated = "ALWAYS".equalsIgnoreCase(isGenerated);
                    // Detect SERIAL/IDENTITY columns by checking column_default for nextval().
                    // SERIAL columns have nextval('seq'::regclass) as default.
                    // These should NOT receive explicit INSERT values — the sequence handles them,
                    // and explicit values can trigger CHECK constraints with POWER/exponentiation
                    // causing underflow/overflow errors (e.g., POWER(-23700, -23700)).
                    String columnDefault = rs.getString("column_default");
                    boolean seqDefault = columnDefault != null && columnDefault.contains("nextval(");
                    PostgresColumn c = new PostgresColumn(columnName, getColumnType(dataType), generated, seqDefault);
                    columns.add(c);
                }
            }
        }
        return columns;
    }

    public PostgresSchema(List<PostgresTable> databaseTables, String databaseName) {
        super(databaseTables);
        this.databaseName = databaseName;
    }

    public PostgresTables getRandomTableNonEmptyTables() {
        return new PostgresTables(Randomly.nonEmptySubset(getDatabaseTables()));
    }

    public String getDatabaseName() {
        return databaseName;
    }

}
