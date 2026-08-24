package idxdiff.mariadb.ast;

import idxdiff.Randomly;

public class MariaDBCastOperation implements MariaDBExpression {

    private final MariaDBExpression expr;
    private final MariaDBCastType type;

    public enum MariaDBCastType {
        SIGNED, UNSIGNED, CHAR, BINARY, DATE, DATETIME, TIME, DECIMAL;

        public static MariaDBCastType getRandom() {
            return Randomly.fromOptions(values());
        }
    }

    public MariaDBCastOperation(MariaDBExpression expr, MariaDBCastType type) {
        this.expr = expr;
        this.type = type;
    }

    public MariaDBExpression getExpr() {
        return expr;
    }

    public MariaDBCastType getCastType() {
        return type;
    }

}