package idxdiff.tidb;

import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import idxdiff.Randomly;
import idxdiff.SQLConnection;
import idxdiff.common.schema.AbstractRelationalTable;
import idxdiff.common.schema.AbstractSchema;
import idxdiff.common.schema.AbstractTableColumn;
import idxdiff.common.schema.AbstractTables;
import idxdiff.common.schema.TableIndex;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema.TiDBTable;

public class TiDBSchema extends AbstractSchema<TiDBGlobalState, TiDBTable> {

    public enum TiDBDataType {

        INT, TEXT, BOOL, FLOATING, CHAR, DECIMAL, NUMERIC, BLOB, DATE;

        private final boolean isPrimitive;

        TiDBDataType() {
            isPrimitive = true;
        }

        TiDBDataType(boolean isPrimitive) {
            this.isPrimitive = isPrimitive;
        }

        public static TiDBDataType getRandom() {
            return Randomly.fromOptions(values());
        }

        public boolean isPrimitive() {
            return isPrimitive;
        }

        public boolean isNumeric() {
            switch (this) {
            case INT:
            case DECIMAL:
            case FLOATING:
            case BOOL:
            case NUMERIC:
                return true;
            case CHAR:
            case TEXT:
            case BLOB:
            case DATE:
                return false;
            default:
                throw new AssertionError(this);
            }
        }

        public boolean canHaveDefault() {
            switch (this) {
            case INT:
            case DECIMAL:
            case FLOATING:
            case BOOL:
            case CHAR:
            case DATE:
                return true;
            case NUMERIC:
            case TEXT:
            case BLOB:
                return false;
            default:
                throw new AssertionError(this);
            }
        }

        /**
         * Returns true if values of the source type can be safely assigned to a column of this target type
         * without causing a "cannot convert datum" error in TiDB.
         */
        public boolean isCompatibleWith(TiDBDataType source) {
            return getCompatibleSourceTypes().contains(source);
        }

        /**
         * Returns the set of source types that can be safely assigned to a column of this target type.
         * Based on TiDB/MySQL implicit type conversion rules.
         */
        public List<TiDBDataType> getCompatibleSourceTypes() {
            switch (this) {
            case INT:
            case FLOATING:
            case DECIMAL:
            case NUMERIC:
            case BOOL:
                // Numeric types are inter-convertible; MySQL also converts strings to numbers
                return Arrays.asList(INT, FLOATING, DECIMAL, NUMERIC, BOOL, TEXT, CHAR);
            case TEXT:
            case CHAR:
            case BLOB:
                // String/blob types accept all types (MySQL converts everything to string)
                return Arrays.asList(INT, FLOATING, DECIMAL, NUMERIC, BOOL, TEXT, CHAR, BLOB, DATE);
            case DATE:
                // DATE only accepts strings (parsed as date literals) and DATE itself.
                // Numeric types (INT, FLOATING, etc.) are NOT compatible with DATE.
                return Arrays.asList(TEXT, CHAR, DATE);
            default:
                throw new AssertionError(this);
            }
        }
    }

    public static class TiDBCompositeDataType {

        private final TiDBDataType dataType;

        private final int size;

        public TiDBCompositeDataType(TiDBDataType dataType) {
            this.dataType = dataType;
            this.size = -1;
        }

        public TiDBCompositeDataType(TiDBDataType dataType, int size) {
            this.dataType = dataType;
            this.size = size;
        }

        public TiDBDataType getPrimitiveDataType() {
            return dataType;
        }

        public int getSize() {
            if (size == -1) {
                throw new AssertionError(this);
            }
            return size;
        }

        public static TiDBCompositeDataType getInt(int size) {
            return new TiDBCompositeDataType(TiDBDataType.INT, size);
        }

        public static TiDBCompositeDataType getRandom() {
            TiDBDataType primitiveType = TiDBDataType.getRandom();
            int size = -1;
            switch (primitiveType) {
            case INT:
                size = Randomly.fromOptions(1, 2, 4, 8);
                break;
            case FLOATING:
                size = Randomly.fromOptions(4, 8);
                break;
            default:
                break;
            }
            return new TiDBCompositeDataType(primitiveType, size);
        }

        @Override
        public String toString() {
            switch (getPrimitiveDataType()) {
            case INT:
                switch (size) {
                case 1:
                    return "TINYINT";
                case 2:
                    return "SMALLINT";
                case 3:
                    return "MEDIUMINT";
                case 4:
                    return "INTEGER";
                case 8:
                    return "BIGINT";
                default:
                    throw new AssertionError(size);
                }
            case FLOATING:
                switch (size) {
                case 4:
                    return "FLOAT";
                case 8:
                    return "DOUBLE";
                default:
                    throw new AssertionError(size);
                }
            default:
                return getPrimitiveDataType().toString();
            }
        }

    }

    public static class TiDBColumn extends AbstractTableColumn<TiDBTable, TiDBCompositeDataType> {

        private final boolean isPrimaryKey;
        private final boolean isNullable;
        private final boolean hasDefault;
        private final boolean isGenerated;
        private final boolean isAutoIncrement;

        public TiDBColumn(String name, TiDBCompositeDataType columnType, boolean isPrimaryKey, boolean isNullable,
                boolean hasDefault) {
            this(name, columnType, isPrimaryKey, isNullable, hasDefault, false, false);
        }

        public TiDBColumn(String name, TiDBCompositeDataType columnType, boolean isPrimaryKey, boolean isNullable,
                boolean hasDefault, boolean isGenerated) {
            this(name, columnType, isPrimaryKey, isNullable, hasDefault, isGenerated, false);
        }

        public TiDBColumn(String name, TiDBCompositeDataType columnType, boolean isPrimaryKey, boolean isNullable,
                boolean hasDefault, boolean isGenerated, boolean isAutoIncrement) {
            super(name, null, columnType);
            this.isPrimaryKey = isPrimaryKey;
            this.isNullable = isNullable;
            this.hasDefault = hasDefault;
            this.isGenerated = isGenerated;
            this.isAutoIncrement = isAutoIncrement;
        }

        @Override
        public boolean isPrimaryKey() {
            return isPrimaryKey;
        }

        public boolean isNullable() {
            return isNullable;
        }

        public boolean hasDefault() {
            return hasDefault;
        }

        public boolean isGenerated() {
            return isGenerated;
        }

        public boolean isAutoIncrement() {
            return isAutoIncrement;
        }

    }

    public static class TiDBTables extends AbstractTables<TiDBTable, TiDBColumn> {

        public TiDBTables(List<TiDBTable> tables) {
            super(tables);
        }

    }

    public TiDBSchema(List<TiDBTable> databaseTables) {
        super(databaseTables);
    }

    public TiDBTables getRandomTableNonEmptyTables() {
        return new TiDBTables(Randomly.nonEmptySubset(getDatabaseTables()));
    }

    public int getIndexCount() {
        int count = 0;
        for (TiDBTable table : getDatabaseTables()) {
            count += table.getIndexes().size();
        }
        return count;
    }

    private static TiDBCompositeDataType getColumnType(String typeString) {
        String trimmedStringType = typeString.replace(" zerofill", "").replace(" unsigned", "");
        if (trimmedStringType.contains("decimal")) {
            return new TiDBCompositeDataType(TiDBDataType.DECIMAL);
        }
        if (trimmedStringType.startsWith("var_string") || trimmedStringType.contains("binary")
                || trimmedStringType.startsWith("varchar")) {
            return new TiDBCompositeDataType(TiDBDataType.TEXT);
        }
        if (trimmedStringType.startsWith("char")) {
            return new TiDBCompositeDataType(TiDBDataType.CHAR);
        }
        TiDBDataType primitiveType;
        int size = -1;
        if (trimmedStringType.startsWith("bigint")) {
            primitiveType = TiDBDataType.INT;
            size = 8;
        } else {
            switch (trimmedStringType) {
            case "text":
            case "mediumtext":
            case "longtext":
            case "tinytext":
                primitiveType = TiDBDataType.TEXT;
                break;
            case "float":
                size = 4;
                primitiveType = TiDBDataType.FLOATING;
                break;
            case "double":
            case "double(8,6)": // workaround to address https://github.com/idxdiff/idxdiff/issues/669
            case "double(23,16)":
                size = 8;
                primitiveType = TiDBDataType.FLOATING;
                break;
            case "tinyint(1)":
                primitiveType = TiDBDataType.BOOL;
                size = 1;
                break;
            case "null":
                primitiveType = TiDBDataType.INT;
                size = 1;
                break;
            case "tinyint":
            case "tinyint(2)":
            case "tinyint(3)":
            case "tinyint(4)":
                primitiveType = TiDBDataType.INT;
                size = 1;
                break;
            case "smallint":
            case "smallint(5)":
            case "smallint(6)":
                primitiveType = TiDBDataType.INT;
                size = 2;
                break;
            case "int":
            case "int(10)":
            case "int(11)":
                primitiveType = TiDBDataType.INT;
                size = 4;
                break;
            case "blob":
            case "mediumblob":
            case "longblob":
            case "tinyblob":
                primitiveType = TiDBDataType.BLOB;
                break;
            case "date":
                primitiveType = TiDBDataType.DATE;
                break;
            case "datetime":
            case "datetime(6)": // workaround to address https://github.com/idxdiff/idxdiff/issues/669
            case "timestamp":
            case "time":
            case "year":
                primitiveType = TiDBDataType.NUMERIC;
                break;
            default:
                throw new AssertionError(trimmedStringType);
            }
        }
        return new TiDBCompositeDataType(primitiveType, size);
    }

    public static class TiDBTable extends AbstractRelationalTable<TiDBColumn, TableIndex, TiDBGlobalState> {

        private final boolean isPartitioned;
        // Columns referenced by expression indexes (cannot be dropped/renamed/modified)
        private Set<String> columnsWithExprIndexDeps = Collections.emptySet();

        public TiDBTable(String tableName, List<TiDBColumn> columns, List<TableIndex> indexes, boolean isView) {
            this(tableName, columns, indexes, isView, false);
        }

        public TiDBTable(String tableName, List<TiDBColumn> columns, List<TableIndex> indexes, boolean isView,
                boolean isPartitioned) {
            super(tableName, columns, indexes, isView);
            this.isPartitioned = isPartitioned;
        }

        public boolean isPartitioned() {
            return isPartitioned;
        }

        /**
         * Set the columns that have expression index dependencies.
         * Called after table construction when loading schema from the database.
         */
        public void setColumnsWithExprIndexDeps(Set<String> columnNames) {
            this.columnsWithExprIndexDeps = columnNames != null ? columnNames : Collections.emptySet();
        }

        /**
         * Returns true if the given column is referenced by an expression index on this table.
         * Such columns cannot be dropped, renamed, or have their type changed via ALTER TABLE.
         */
        public boolean hasExpressionIndexDependency(String columnName) {
            return columnsWithExprIndexDeps.contains(columnName);
        }

    }

    public static TiDBSchema fromConnection(SQLConnection con, String databaseName) throws SQLException {
        List<TiDBTable> databaseTables = new ArrayList<>();
        List<String> tableNames = getTableNames(con);
        for (String tableName : tableNames) {
            List<TiDBColumn> databaseColumns = getTableColumns(con, tableName);
            // Ignore invalid views
            if (databaseColumns.isEmpty()) {
                continue;
            }
            List<TableIndex> indexes = getIndexes(con, tableName);
            boolean isView = matchesViewName(tableName);
            boolean isPartitioned = isPartitionedTable(con, databaseName, tableName);
            TiDBTable t = new TiDBTable(tableName, databaseColumns, indexes, isView, isPartitioned);
            // Detect expression index column dependencies
            Set<String> exprIndexDeps = getExprIndexColumnDeps(con, tableName, databaseColumns);
            t.setColumnsWithExprIndexDeps(exprIndexDeps);
            for (TiDBColumn c : databaseColumns) {
                c.setTable(t);
            }
            databaseTables.add(t);

        }
        return new TiDBSchema(databaseTables);
    }

    private static List<String> getTableNames(SQLConnection con) throws SQLException {
        List<String> tableNames = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            ResultSet tableRs = s.executeQuery("SHOW TABLES");
            while (tableRs.next()) {
                String tableName = tableRs.getString(1);
                tableNames.add(tableName);
            }
        }
        return tableNames;
    }

    private static List<TableIndex> getIndexes(SQLConnection con, String tableName) throws SQLException {
        List<TableIndex> indexes = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery(String.format("SHOW INDEX FROM %s", tableName))) {
                while (rs.next()) {
                    String indexName = rs.getString("Key_name");
                    indexes.add(TableIndex.create(indexName));
                }
            }
        }
        return indexes;
    }

    /**
     * Extract column names referenced by expression indexes on the given table.
     * In TiDB's SHOW INDEX output, expression indexes have NULL as Column_name and
     * the expression text in the Expression column. We parse column references from
     * the expression text. TiDB may store references in either backtick-quoted format
     * (`tableName`.`columnName`) or unquoted format (tableName.columnName).
     */
    private static Set<String> getExprIndexColumnDeps(SQLConnection con, String tableName,
            List<TiDBColumn> tableColumns) {
        Set<String> deps = new HashSet<>();
        Set<String> columnNames = tableColumns.stream().map(c -> c.getName()).collect(Collectors.toSet());
        // Match column references in both backtick-quoted and unquoted formats:
        // `tableName`.`columnName` or tableName.columnName
        Pattern colRefPattern = Pattern.compile("`?([^`.(\\s]+)`?\\.`?([^`.(\\s]+)`?");
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery(String.format("SHOW INDEX FROM `%s`", tableName))) {
                while (rs.next()) {
                    String columnName = rs.getString("Column_name");
                    // Expression indexes have NULL Column_name
                    if (columnName == null) {
                        String expression = rs.getString("Expression");
                        if (expression != null) {
                            Matcher m = colRefPattern.matcher(expression);
                            while (m.find()) {
                                String refCol = m.group(2);
                                if (columnNames.contains(refCol)) {
                                    deps.add(refCol);
                                }
                            }
                        }
                    }
                }
            }
        } catch (SQLException e) {
            // Ignore — expression index detection is best-effort
        }
        return deps;
    }

    private static boolean isPartitionedTable(SQLConnection con, String databaseName, String tableName)
            throws SQLException {
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery(String.format(
                    "SELECT COUNT(*) FROM information_schema.partitions WHERE table_schema = '%s' AND table_name = '%s' AND partition_name IS NOT NULL",
                    databaseName, tableName))) {
                if (rs.next()) {
                    return rs.getInt(1) > 0;
                }
            }
        } catch (SQLException e) {
            // If the query fails, assume not partitioned
        }
        return false;
    }

    private static List<TiDBColumn> getTableColumns(SQLConnection con, String tableName) throws SQLException {
        List<TiDBColumn> columns = new ArrayList<>();
        try (Statement s = con.createStatement()) {
            try (ResultSet rs = s.executeQuery("SHOW COLUMNS FROM " + tableName)) {
                while (rs.next()) {
                    String columnName = rs.getString("Field");
                    String dataType = rs.getString("Type");
                    boolean isNullable = rs.getString("Null").contentEquals("YES");
                    boolean isPrimaryKey = rs.getString("Key").contains("PRI");
                    boolean hasDefault = rs.getString("Default") != null;
                    String extra = rs.getString("Extra");
                    boolean isGenerated = extra != null
                            && (extra.contains("VIRTUAL GENERATED") || extra.contains("STORED GENERATED"));
                    boolean isAutoIncrement = extra != null && extra.contains("auto_increment");
                    TiDBColumn c = new TiDBColumn(columnName, getColumnType(dataType), isPrimaryKey, isNullable,
                            hasDefault, isGenerated, isAutoIncrement);
                    columns.add(c);
                }
            }
        } catch (SQLException e) { // Happens when
        }
        return columns;
    }

}
