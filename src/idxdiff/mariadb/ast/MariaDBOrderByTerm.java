package idxdiff.mariadb.ast;

import idxdiff.Randomly;

public class MariaDBOrderByTerm implements MariaDBExpression {

    private final MariaDBExpression expr;
    private final MariaDBOrder order;

    public enum MariaDBOrder {
        ASC, DESC;

        public static MariaDBOrder getRandomOrder() {
            return Randomly.fromOptions(values());
        }
    }

    public MariaDBOrderByTerm(MariaDBExpression expr, MariaDBOrder order) {
        this.expr = expr;
        this.order = order;
    }

    public MariaDBExpression getExpr() {
        return expr;
    }

    public MariaDBOrder getOrder() {
        return order;
    }

}