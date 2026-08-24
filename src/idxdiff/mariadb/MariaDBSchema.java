package idxdiff.mariadb;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLIntegrityConstraintViolationException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import idxdiff.Randomly;
import idxdiff.SQLConnection;
import idxdiff.common.schema.AbstractRelationalTable;
import idxdiff.common.schema.AbstractSchema;
import idxdiff.common.schema.AbstractTableColumn;
import idxdiff.common.schema.TableIndex;
import idxdiff.mariadb.MariaDBProvider.MariaDBGlobalState;
import idxdiff.mariadb.MariaDBSchema.MariaDBTable;
import idxdiff.mariadb.MariaDBSchema.MariaDBTable.MariaDBEngine;

public class MariaDBSchema extends AbstractSchema<MariaDBGlobalState, MariaDBTable> {

    private static final int NR_SCHEMA_READ_TRIES = 10;

    public enum MariaDBDataType {
        INT, VARCHAR, REAL, BOOLEAN;
    }

    public static class MariaDBColumn extends AbstractTableColumn<MariaDBTable, MariaDBDataType> {

        private final boolean isPrimaryKey;
        private final int precision;

        public enum CollateSequence {
            NOCASE, RTRIM, BINARY;

            public static CollateSequence random() {
                return Randomly.fromOptions(values());
            }
        }

        public MariaDBColumn(String name, MariaDBDataType columnType, boolean isPrimaryKey, int precision) {
            super(name, null, columnType);
            this.isPrimaryKey = isPrimaryKey;
            this.precision = precision;
        }

        public int getPrecision() {
            return precision;
        }

        @Override
        public boolean isPrimaryKey() {
            return isPrimaryKey;
        }

        public static MariaDBColumn createDummy(String name) {
            return new MariaDBColumn(name, MariaDBDataType.INT, false, 1);
        }

    }

    public static class MariaDBTables {
        private final List<MariaDBTable> tables;
        private final List<MariaDBColumn> columns;

        public MariaDBTables(List<MariaDBTable> tables) {
            this.tables = tables;
            columns = new ArrayList<>();
            for (MariaDBTable t : tables) {
                columns.addAll(t.getColumns());
            }
        }

        public String tableNamesAsString() {
            return tables.stream().map(t -> t.getName()).collect(Collectors.joining(", "));
        }

        public List<MariaDBTable> getTables() {
            return tables;
        }

        public List<MariaDBColumn> getColumns() {
            return columns;
        }

        public String columnNamesAsString() {
            return getColumns().stream().map(t -> t.getTable().getName() + "." + t.getName())
                    .collect(Collectors.joining(", "));
        }

        public String columnNamesAsString(Function<MariaDBColumn, String> function) {
            return getColumns().stream().map(function).collect(Collectors.joining(", "));
        }
    }

    private static MariaDBDataType getColumnType(String typeString) {
        switch (typeString) {
        case "tinyint":
        case "smallint":
        case "mediumint":
        case "int":
        case "bigint":
            return MariaDBDataType.INT;
        case "varchar":
        case "tinytext":
        case "mediumtext":
        case "text":
        case "longtext":
        case "char":
            return MariaDBDataType.VARCHAR;
        case "real":
        case "double":
        case "float":
        case "decimal":
        case "numeric":
            return MariaDBDataType.REAL;
        default:
            throw new AssertionError(typeString);
        }
    }

    public static class MariaDBTable extends AbstractRelationalTable<MariaDBColumn, MariaDBIndex, MariaDBGlobalState> {

        public enum MariaDBEngine {

            INNO_DB("InnoDB"), MY_ISAM("MyISAM"), ARIA("Aria");

            private String s;

            MariaDBEngine(String s) {
                this.s = s;
            }

            public String getTextRepresentation() {
                return s;
            }

            public static MariaDBEngine get(String val) {
                return Stream.of(values()).filter(engine -> engine.s.equalsIgnoreCase(val)).findFirst().get();
            }

            public static MariaDBEngine getRandomEngine() {
                return Randomly.fromOptions(MariaDBEngine.values());
            }

        }

        private final MariaDBEngine engine;

        public MariaDBTable(String tableName, List<MariaDBColumn> columns, List<MariaDBIndex> indexes,
                MariaDBEngine engine) {
            super(tableName, columns, indexes, false);
            this.engine = engine;
        }

        public MariaDBEngine getEngine() {
            return engine;
        }

    }

    public static final class MariaDBIndex extends TableIndex {
        private final List<String> columnNames;
        private final boolean isUnique;
        private final String indexType;
        private final List<Integer> prefixLengths;
        private final List<Boolean> isDesc;

        private MariaDBIndex(String indexName, List<String> columnNames, boolean isUnique, String indexType,
                List<Integer> prefixLengths, List<Boolean> isDesc) {
            super(indexName);
            this.columnNames = columnNames;
            this.isUnique = isUnique;
            this.indexType = indexType;
            this.prefixLengths = prefixLengths;
            this.isDesc = isDesc;
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
            return Collections.unmodifiableList(columnNames);
        }

        public boolean isUnique() {
            return isUnique;
        }

        public String getIndexType() {
            return indexType;
        }

        public List<Integer> getPrefixLengths() {
            return Collections.unmodifiableList(prefixLengths);
        }

        public List<Boolean> getIsDesc() {
            return Collections.unmodifiableList(isDesc);
        }

        public boolean isPrimaryKey() {
            return super.getIndexName().equals("PRIMARY");
        }

        public boolean isPrefixIndex() {
            return prefixLengths.stream().anyMatch(l -> l > 0);
        }

        public boolean isFullTextIndex() {
            return "FULLTEXT".equalsIgnoreCase(indexType);
        }
    }

    public static MariaDBSchema fromConnection(SQLConnection con, String databaseName) throws SQLException {
        Exception ex = null;
        for (int i = 0; i < NR_SCHEMA_READ_TRIES; i++) {
            try {
                List<MariaDBTable> databaseTables = new ArrayList<>();
                try (Statement s = con.createStatement()) {
                    try (ResultSet rs = s.executeQuery(
                            "select TABLE_NAME, ENGINE from information_schema.TABLES where table_schema = '"
                                    + databaseName + "';")) {
                        while (rs.next()) {
                            String tableName = rs.getString("TABLE_NAME");
                            String tableEngineStr = rs.getString("ENGINE");
                            MariaDBEngine engine = MariaDBEngine.get(tableEngineStr);
                            List<MariaDBColumn> databaseColumns = getTableColumns(con, tableName, databaseName);
                            List<MariaDBIndex> indexes = getIndexes(con, tableName, databaseName);
                            MariaDBTable t = new MariaDBTable(tableName, databaseColumns, indexes, engine);
                            for (MariaDBColumn c : databaseColumns) {
                                c.setTable(t);
                            }
                            databaseTables.add(t);
                        }
                    }
                }
                return new MariaDBSchema(databaseTables);
            } catch (SQLIntegrityConstraintViolationException e) {
                ex = e;
            }
        }
        throw new AssertionError(ex);
    }

    private static List<MariaDBIndex> getIndexes(SQLConnection con, String tableName, String databaseName)
            throws SQLException {
        Map<String, IndexBuilder> indexBuilderMap = new HashMap<>();
        try (Statement s = con.createStatement()) {
            String sql = "SELECT INDEX_NAME, COLUMN_NAME, SEQ_IN_INDEX, NON_UNIQUE, "
                    + "INDEX_TYPE, SUB_PART, COLLATION "
                    + "FROM INFORMATION_SCHEMA.STATISTICS WHERE TABLE_SCHEMA = '" + databaseName
                    + "' AND TABLE_NAME='" + tableName + "' ORDER BY INDEX_NAME, SEQ_IN_INDEX;";
            try (ResultSet rs = s.executeQuery(sql)) {
                while (rs.next()) {
                    String indexName = rs.getString("INDEX_NAME");
                    String columnName = rs.getString("COLUMN_NAME");
                    boolean nonUnique = rs.getBoolean("NON_UNIQUE");
                    String indexType = rs.getString("INDEX_TYPE");
                    int subPart = rs.getInt("SUB_PART");
                    if (rs.wasNull()) {
                        subPart = 0;
                    }
                    String collation = rs.getString("COLLATION");
                    indexBuilderMap.computeIfAbsent(indexName,
                            k -> new IndexBuilder(indexName, !nonUnique, indexType));
                    indexBuilderMap.get(indexName).addColumn(columnName, subPart, "D".equals(collation));
                }
            }
        }
        List<MariaDBIndex> indexes = new ArrayList<>();
        for (IndexBuilder builder : indexBuilderMap.values()) {
            indexes.add(builder.build());
        }
        return indexes;
    }

    private static class IndexBuilder {
        final String indexName;
        final boolean isUnique;
        final String indexType;
        final List<String> columnNames = new ArrayList<>();
        final List<Integer> prefixLengths = new ArrayList<>();
        final List<Boolean> isDesc = new ArrayList<>();

        IndexBuilder(String indexName, boolean isUnique, String indexType) {
            this.indexName = indexName;
            this.isUnique = isUnique;
            this.indexType = indexType;
        }

        void addColumn(String columnName, int subPart, boolean desc) {
            columnNames.add(columnName);
            prefixLengths.add(subPart);
            isDesc.add(desc);
        }

        MariaDBIndex build() {
            return new MariaDBIndex(indexName,
                    Collections.unmodifiableList(new ArrayList<>(columnNames)), isUnique, indexType,
                    Collections.unmodifiableList(new ArrayList<>(prefixLengths)),
                    Collections.unmodifiableList(new ArrayList<>(isDesc)));
        }
    }

    private static List<MariaDBColumn> getTableColumns(SQLConnection con, String tableName, String databaseName)
            throws SQLException {
        List<MariaDBColumn> columns = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery("select * from information_schema.columns where table_schema = '"
                    + databaseName + "' AND TABLE_NAME='" + tableName + "'")) {
                while (rs.next()) {
                    String columnName = rs.getString("COLUMN_NAME");
                    String dataType = rs.getString("DATA_TYPE");
                    int precision = rs.getInt("NUMERIC_PRECISION");
                    boolean isPrimaryKey = rs.getString("COLUMN_KEY").equals("PRI");
                    MariaDBColumn c = new MariaDBColumn(columnName, getColumnType(dataType), isPrimaryKey, precision);
                    columns.add(c);
                }
            }
        }
        return columns;
    }

    public MariaDBSchema(List<MariaDBTable> databaseTables) {
        super(databaseTables);
    }

    public MariaDBTables getRandomTableNonEmptyTables() {
        return new MariaDBTables(Randomly.nonEmptySubset(getDatabaseTables()));
    }

}