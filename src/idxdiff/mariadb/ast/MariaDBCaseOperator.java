package idxdiff.mariadb.ast;

import java.util.List;

public class MariaDBCaseOperator implements MariaDBExpression {

    private final MariaDBExpression switchCondition;
    private final List<MariaDBExpression> whenExprs;
    private final List<MariaDBExpression> thenExprs;
    private final MariaDBExpression elseExpr;

    public MariaDBCaseOperator(MariaDBExpression switchCondition, List<MariaDBExpression> whenExprs,
            List<MariaDBExpression> thenExprs, MariaDBExpression elseExpr) {
        this.switchCondition = switchCondition;
        this.whenExprs = whenExprs;
        this.thenExprs = thenExprs;
        this.elseExpr = elseExpr;
    }

    public MariaDBExpression getSwitchCondition() {
        return switchCondition;
    }

    public List<MariaDBExpression> getWhenExprs() {
        return whenExprs;
    }

    public List<MariaDBExpression> getThenExprs() {
        return thenExprs;
    }

    public MariaDBExpression getElseExpr() {
        return elseExpr;
    }

}