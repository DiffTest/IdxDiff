package idxdiff.mariadb.ast;

public class MariaDBBetweenOperation implements MariaDBExpression {

    private final MariaDBExpression expr;
    private final MariaDBExpression left;
    private final MariaDBExpression right;
    private final boolean isNegated;

    public MariaDBBetweenOperation(MariaDBExpression expr, MariaDBExpression left, MariaDBExpression right,
            boolean isNegated) {
        this.expr = expr;
        this.left = left;
        this.right = right;
        this.isNegated = isNegated;
    }

    public MariaDBExpression getExpr() {
        return expr;
    }

    public MariaDBExpression getLeft() {
        return left;
    }

    public MariaDBExpression getRight() {
        return right;
    }

    public boolean isNegated() {
        return isNegated;
    }

}