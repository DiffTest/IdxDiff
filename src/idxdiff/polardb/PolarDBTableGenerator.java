package idxdiff.polardb;

import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mysql.MySQLGlobalState;
import idxdiff.mysql.MySQLSchema.MySQLDataType;

public final class PolarDBTableGenerator {
    private PolarDBTableGenerator() {}
    public static SQLQueryAdapter generate(MySQLGlobalState g, String name) {
        ExpectedErrors e = new ExpectedErrors();
        e.add("already exists"); e.add("Duplicate column name");
        e.add("Drop primary key");  // PolarDB-X doesn't support DROP PRIMARY KEY
        StringBuilder sb = new StringBuilder("CREATE TABLE ").append(name).append(" (");
        int n = Randomly.smallNumber() + 2;
        sb.append("c0 INT NOT NULL AUTO_INCREMENT PRIMARY KEY");
        for (int i = 1; i < n; i++) {
            sb.append(", c").append(i).append(" ");
            MySQLDataType t = MySQLDataType.getRandom(g);
            sb.append(typeStr(t));
            if (Randomly.getBoolean() && t != MySQLDataType.VARCHAR) sb.append(" NOT NULL");
        }
        sb.append(") ENGINE=InnoDB;");
        return new SQLQueryAdapter(sb.toString(), e, true);
    }
    private static String typeStr(MySQLDataType t) {
        switch (t) {
        case INT: return "INT"; case BIGINT: return "BIGINT";
        case VARCHAR:
            // Use utf8mb4 charset to support Collation index tests (mode 34)
            return "VARCHAR(" + Randomly.fromOptions(32, 64, 128) + ") CHARACTER SET utf8mb4";
        case DOUBLE: return "DOUBLE"; case FLOAT: return "FLOAT";
        case DECIMAL: return "DECIMAL(10,2)"; default: return "INT";
        }
    }
}
