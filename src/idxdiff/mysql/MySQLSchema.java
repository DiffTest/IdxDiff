package idxdiff.mysql;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLIntegrityConstraintViolationException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import idxdiff.Randomly;
import idxdiff.SQLConnection;
import idxdiff.common.schema.AbstractRelationalTable;
import idxdiff.common.schema.AbstractRowValue;
import idxdiff.common.schema.AbstractSchema;
import idxdiff.common.schema.AbstractTableColumn;
import idxdiff.common.schema.AbstractTables;
import idxdiff.common.schema.TableIndex;
import idxdiff.mysql.MySQLSchema.MySQLTable;
import idxdiff.mysql.MySQLSchema.MySQLTable.MySQLEngine;
import idxdiff.mysql.ast.MySQLConstant;

public class MySQLSchema extends AbstractSchema<MySQLGlobalState, MySQLTable> {

    private static final int NR_SCHEMA_READ_TRIES = 10;

    public enum MySQLDataType {
        INT, BIGINT, VARCHAR, FLOAT, DOUBLE, DECIMAL;

        public static MySQLDataType getRandom(MySQLGlobalState globalState) {
            return Randomly.fromOptions(values());
        }

        public boolean isNumeric() {
            switch (this) {
            case INT:
            case BIGINT:
            case DOUBLE:
            case FLOAT:
            case DECIMAL:
                return true;
            case VARCHAR:
                return false;
            default:
                throw new AssertionError(this);
            }
        }

    }

    public static class MySQLColumn extends AbstractTableColumn<MySQLTable, MySQLDataType> {

        private final boolean isPrimaryKey;
        private final boolean isAutoIncrement;
        private final int precision;

        public enum CollateSequence {
            NOCASE, RTRIM, BINARY;

            public static CollateSequence random() {
                return Randomly.fromOptions(values());
            }
        }

        public MySQLColumn(String name, MySQLDataType columnType, boolean isPrimaryKey, boolean isAutoIncrement,
                int precision) {
            super(name, null, columnType);
            this.isPrimaryKey = isPrimaryKey;
            this.isAutoIncrement = isAutoIncrement;
            this.precision = precision;
        }

        public int getPrecision() {
            return precision;
        }

        @Override
        public boolean isPrimaryKey() {
            return isPrimaryKey;
        }

        public boolean isAutoIncrement() {
            return isAutoIncrement;
        }

    }

    public static class MySQLTables extends AbstractTables<MySQLTable, MySQLColumn> {

        public MySQLTables(List<MySQLTable> tables) {
            super(tables);
        }

        public MySQLRowValue getRandomRowValue(SQLConnection con) throws SQLException {
            String randomRow = String.format("SELECT %s FROM %s ORDER BY RAND() LIMIT 1", columnNamesAsString(
                    c -> c.getTable().getName() + "." + c.getName() + " AS " + c.getTable().getName() + c.getName()),
                    // columnNamesAsString(c -> "typeof(" + c.getTable().getName() + "." +
                    // c.getName() + ")")
                    tableNamesAsString());
            Map<MySQLColumn, MySQLConstant> values = new HashMap<>();
            try (Statement s = con.createStatement()) {
                ResultSet randomRowValues = s.executeQuery(randomRow);
                if (!randomRowValues.next()) {
                    throw new AssertionError("could not find random row! " + randomRow + "\n");
                }
                for (int i = 0; i < getColumns().size(); i++) {
                    MySQLColumn column = getColumns().get(i);
                    Object value;
                    int columnIndex = randomRowValues.findColumn(column.getTable().getName() + column.getName());
                    assert columnIndex == i + 1;
                    MySQLConstant constant;
                    if (randomRowValues.getString(columnIndex) == null) {
                        constant = MySQLConstant.createNullConstant();
                    } else {
                        switch (column.getType()) {
                        case INT:
                        case BIGINT:
                            value = randomRowValues.getLong(columnIndex);
                            constant = MySQLConstant.createIntConstant((long) value);
                            break;
                        case VARCHAR:
                            value = randomRowValues.getString(columnIndex);
                            constant = MySQLConstant.createStringConstant((String) value);
                            break;
                        default:
                            throw new AssertionError(column.getType());
                        }
                    }
                    values.put(column, constant);
                }
                assert !randomRowValues.next();
                return new MySQLRowValue(this, values);
            }

        }

    }

    private static MySQLDataType getColumnType(String typeString) {
        switch (typeString) {
        case "tinyint":
        case "smallint":
        case "mediumint":
        case "int":
            return MySQLDataType.INT;
        case "bigint":
            return MySQLDataType.BIGINT;
        case "varchar":
        case "tinytext":
        case "mediumtext":
        case "text":
        case "longtext":
            return MySQLDataType.VARCHAR;
        case "double":
            return MySQLDataType.DOUBLE;
        case "float":
            return MySQLDataType.FLOAT;
        case "decimal":
            return MySQLDataType.DECIMAL;
        default:
            throw new AssertionError(typeString);
        }
    }

    public static class MySQLRowValue extends AbstractRowValue<MySQLTables, MySQLColumn, MySQLConstant> {

        MySQLRowValue(MySQLTables tables, Map<MySQLColumn, MySQLConstant> values) {
            super(tables, values);
        }

    }

    public static class MySQLTable extends AbstractRelationalTable<MySQLColumn, MySQLIndex, MySQLGlobalState> {

        public enum MySQLEngine {
            INNO_DB("InnoDB"), MY_ISAM("MyISAM"), MEMORY("MEMORY"), HEAP("HEAP"), CSV("CSV"), MERGE("MERGE"),
            ARCHIVE("ARCHIVE"), FEDERATED("FEDERATED");

            private String s;

            MySQLEngine(String s) {
                this.s = s;
            }

            public static MySQLEngine get(String val) {
                return Stream.of(values()).filter(engine -> engine.s.equalsIgnoreCase(val)).findFirst().get();
            }

        }

        private final MySQLEngine engine;

        public MySQLTable(String tableName, List<MySQLColumn> columns, List<MySQLIndex> indexes, MySQLEngine engine) {
            super(tableName, columns, indexes, false /* TODO: support views */);
            this.engine = engine;
        }

        public MySQLEngine getEngine() {
            return engine;
        }

    }

    public static final class MySQLIndex extends TableIndex {

        private final List<String> columnNames;
        private final boolean isUnique;
        private final String indexType;

        private MySQLIndex(String indexName, List<String> columnNames, boolean isUnique, String indexType) {
            super(indexName);
            this.columnNames = columnNames != null ? columnNames : new ArrayList<>();
            this.isUnique = isUnique;
            this.indexType = indexType;
        }

        public static MySQLIndex create(String indexName, List<String> columnNames, boolean isUnique, String indexType) {
            return new MySQLIndex(indexName, columnNames, isUnique, indexType);
        }

        /** Backward-compatible factory for when column info is unavailable */
        public static MySQLIndex create(String indexName) {
            return new MySQLIndex(indexName, new ArrayList<>(), false, "BTREE");
        }

        @Override
        public String getIndexName() {
            if (super.getIndexName().contentEquals("PRIMARY")) {
                return "`PRIMARY`";
            } else {
                return super.getIndexName();
            }
        }

        /** Get the column names covered by this index (in order) */
        public List<String> getColumnNames() {
            return columnNames;
        }

        /** Is this a unique index? */
        public boolean isUnique() {
            return isUnique;
        }

        /** Get the index type (BTREE, HASH, etc.) */
        public String getIndexType() {
            return indexType;
        }
    }

    public static MySQLSchema fromConnection(SQLConnection con, String databaseName) throws SQLException {
        Exception ex = null;
        /* the loop is a workaround for https://bugs.mysql.com/bug.php?id=95929 */
        for (int i = 0; i < NR_SCHEMA_READ_TRIES; i++) {
            try {
                List<MySQLTable> databaseTables = new ArrayList<>();
                try (Statement s = con.createStatement()) {
                    try (ResultSet rs = s.executeQuery(
                            "select TABLE_NAME, ENGINE from information_schema.TABLES where table_schema = '"
                                    + databaseName + "';")) {
                        while (rs.next()) {
                            String tableName = rs.getString("TABLE_NAME");
                            String tableEngineStr = rs.getString("ENGINE");
                            MySQLEngine engine = MySQLEngine.get(tableEngineStr);
                            List<MySQLColumn> databaseColumns = getTableColumns(con, tableName, databaseName);
                            List<MySQLIndex> indexes = getIndexes(con, tableName, databaseName);
                            MySQLTable t = new MySQLTable(tableName, databaseColumns, indexes, engine);
                            for (MySQLColumn c : databaseColumns) {
                                c.setTable(t);
                            }
                            databaseTables.add(t);
                        }
                    }
                }
                return new MySQLSchema(databaseTables);
            } catch (SQLIntegrityConstraintViolationException e) {
                ex = e;
            }
        }
        throw new AssertionError(ex);
    }

    private static List<MySQLIndex> getIndexes(SQLConnection con, String tableName, String databaseName)
            throws SQLException {
        // Use a map to aggregate columns per index (multi-column indexes have multiple rows)
        Map<String, List<String>> indexColumns = new HashMap<>();
        Map<String, Boolean> indexUnique = new HashMap<>();
        Map<String, String> indexTypeMap = new HashMap<>();

        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery(String.format(
                    "SELECT INDEX_NAME, COLUMN_NAME, NON_UNIQUE, INDEX_TYPE "
                    + "FROM INFORMATION_SCHEMA.STATISTICS "
                    + "WHERE TABLE_SCHEMA = '%s' AND TABLE_NAME='%s' "
                    + "ORDER BY INDEX_NAME, SEQ_IN_INDEX;",
                    databaseName, tableName))) {
                while (rs.next()) {
                    String indexName = rs.getString("INDEX_NAME");
                    String colName = rs.getString("COLUMN_NAME");
                    boolean nonUnique = rs.getBoolean("NON_UNIQUE");
                    String idxType = rs.getString("INDEX_TYPE");

                    indexColumns.computeIfAbsent(indexName, k -> new ArrayList<>()).add(colName);
                    indexUnique.putIfAbsent(indexName, !nonUnique);
                    indexTypeMap.putIfAbsent(indexName, idxType);
                }
            }
        }

        List<MySQLIndex> indexes = new ArrayList<>();
        for (Map.Entry<String, List<String>> entry : indexColumns.entrySet()) {
            String idxName = entry.getKey();
            List<String> cols = entry.getValue();
            boolean unique = indexUnique.getOrDefault(idxName, false);
            String type = indexTypeMap.getOrDefault(idxName, "BTREE");
            indexes.add(MySQLIndex.create(idxName, cols, unique, type));
        }
        return indexes;
    }

    private static List<MySQLColumn> getTableColumns(SQLConnection con, String tableName, String databaseName)
            throws SQLException {
        List<MySQLColumn> columns = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery("select * from information_schema.columns where table_schema = '"
                    + databaseName + "' AND TABLE_NAME='" + tableName + "'")) {
                while (rs.next()) {
                    String columnName = rs.getString("COLUMN_NAME");
                    String dataType = rs.getString("DATA_TYPE");
                    int precision = rs.getInt("NUMERIC_PRECISION");
                    boolean isPrimaryKey = rs.getString("COLUMN_KEY").equals("PRI");
                    String extra = rs.getString("EXTRA");
                    boolean isAutoIncrement = extra != null && extra.contains("auto_increment");
                    MySQLColumn c = new MySQLColumn(columnName, getColumnType(dataType), isPrimaryKey, isAutoIncrement, precision);
                    columns.add(c);
                }
            }
        }
        return columns;
    }

    public MySQLSchema(List<MySQLTable> databaseTables) {
        super(databaseTables);
    }

    public MySQLTables getRandomTableNonEmptyTables() {
        return new MySQLTables(Randomly.nonEmptySubset(getDatabaseTables()));
    }

}
