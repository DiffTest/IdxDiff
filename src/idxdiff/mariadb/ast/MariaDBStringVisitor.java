package idxdiff.mariadb.ast;

import java.util.List;

public class MariaDBStringVisitor extends MariaDBVisitor {

    private final StringBuilder sb = new StringBuilder();

    public String getString() {
        return sb.toString();
    }

    @Override
    public void visit(MariaDBConstant c) {
        sb.append(c.toString());
    }

    @Override
    public void visit(MariaDBPostfixUnaryOperation op) {
        sb.append("(");
        visit(op.getRandomWhereCondition());
        sb.append(" ");
        sb.append(op.getOperator().getTextRepresentation());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBColumnName c) {
        sb.append(c.getColumn().getFullQualifiedName());
    }

    @Override
    public void visit(MariaDBSelectStatement s) {
        sb.append("SELECT ");
        switch (s.getSelectType()) {
        case ALL:
            sb.append("ALL ");
            break;
        case DISTINCT:
            sb.append("DISTINCT ");
            break;
        case DISTINCTROW:
            sb.append("DISTINCTROW ");
            break;
        default:
            throw new AssertionError();
        }
        if (s.getColumns().isEmpty()) {
            sb.append("*");
        } else {
            for (int i = 0; i < s.getColumns().size(); i++) {
                if (i != 0) {
                    sb.append(", ");
                }
                visit(s.getColumns().get(i));
            }
        }
        if (s.getFromList() != null && !s.getFromList().isEmpty()) {
            sb.append(" FROM ");
            for (int i = 0; i < s.getFromList().size(); i++) {
                if (i != 0) {
                    sb.append(", ");
                }
                visit(s.getFromList().get(i));
            }
        }
        List<MariaDBJoin> joinClauses = s.getJoinClauses();
        if (joinClauses != null) {
            for (MariaDBJoin join : joinClauses) {
                visit(join);
            }
        }
        if (s.getWhereCondition() != null) {
            sb.append(" WHERE ");
            visit(s.getWhereCondition());
        }
        if (s.getGroupBys() != null && !s.getGroupBys().isEmpty()) {
            sb.append(" GROUP BY ");
            for (int i = 0; i < s.getGroupBys().size(); i++) {
                if (i != 0) {
                    sb.append(", ");
                }
                visit(s.getGroupBys().get(i));
            }
        }
        if (s.getOrderByClauses() != null && !s.getOrderByClauses().isEmpty()) {
            sb.append(" ORDER BY ");
            for (int i = 0; i < s.getOrderByClauses().size(); i++) {
                if (i != 0) {
                    sb.append(", ");
                }
                visit(s.getOrderByClauses().get(i));
            }
        }
        if (s.getLimitClause() != null) {
            sb.append(" LIMIT ");
            sb.append(s.getLimitClause());
        }
        if (s.getOffsetClause() != null) {
            sb.append(" OFFSET ");
            sb.append(s.getOffsetClause());
        }
    }

    @Override
    public void visit(MariaDBText t) {
        visit(t.getExpr());
        sb.append(t.getText());
    }

    @Override
    public void visit(MariaDBAggregate aggr) {
        sb.append(aggr.getAggr());
        sb.append("(");
        visit(aggr.getExpr());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBBinaryOperator comp) {
        sb.append("(");
        visit(comp.getLeft());
        sb.append(" ");
        sb.append(comp.getOp().getTextRepresentation());
        sb.append(" ");
        visit(comp.getRight());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBUnaryPrefixOperation op) {
        sb.append("(");
        sb.append(op.getOp().textRepresentation);
        sb.append(" ");
        visit(op.getExpr());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBFunction func) {
        sb.append(func.getFunc().getFunctionName());
        sb.append("(");
        for (int i = 0; i < func.getArgs().size(); i++) {
            if (i != 0) {
                sb.append(", ");
            }
            visit(func.getArgs().get(i));
        }
        sb.append(")");
    }

    @Override
    public void visit(MariaDBInOperation op) {
        sb.append("(");
        visit(op.getExpr());
        if (op.isNegated()) {
            sb.append(" NOT");
        }
        sb.append(" IN (");
        for (int i = 0; i < op.getList().size(); i++) {
            if (i != 0) {
                sb.append(", ");
            }
            visit(op.getList().get(i));
        }
        sb.append("))");
    }

    @Override
    public void visit(MariaDBJoin join) {
        sb.append(" ");
        sb.append(join.getType());
        sb.append(" ");
        sb.append(join.getTable().getName());
        if (join.getOnClause() != null) {
            sb.append(" ON ");
            visit(join.getOnClause());
        }
    }

    @Override
    public void visit(MariaDBTableReference t) {
        sb.append(t.getTable().getName());
    }

    @Override
    public void visit(MariaDBBetweenOperation op) {
        sb.append("(");
        visit(op.getExpr());
        if (op.isNegated()) {
            sb.append(" NOT");
        }
        sb.append(" BETWEEN ");
        visit(op.getLeft());
        sb.append(" AND ");
        visit(op.getRight());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBCaseOperator op) {
        sb.append("CASE ");
        if (op.getSwitchCondition() != null) {
            visit(op.getSwitchCondition());
            sb.append(" ");
        }
        for (int i = 0; i < op.getWhenExprs().size(); i++) {
            sb.append("WHEN ");
            visit(op.getWhenExprs().get(i));
            sb.append(" THEN ");
            visit(op.getThenExprs().get(i));
            sb.append(" ");
        }
        if (op.getElseExpr() != null) {
            sb.append("ELSE ");
            visit(op.getElseExpr());
            sb.append(" ");
        }
        sb.append("END");
    }

    @Override
    public void visit(MariaDBCastOperation op) {
        sb.append("CAST(");
        visit(op.getExpr());
        sb.append(" AS ");
        sb.append(op.getCastType().toString());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBExists op) {
        sb.append("EXISTS (");
        visit(op.getSubquery());
        sb.append(")");
    }

    @Override
    public void visit(MariaDBOrderByTerm op) {
        visit(op.getExpr());
        sb.append(" ");
        sb.append(op.getOrder().toString());
    }
}