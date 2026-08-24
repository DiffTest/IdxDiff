package idxdiff.tidb.visitor;

import idxdiff.tidb.ast.TiDBAggregate;
import idxdiff.tidb.ast.TiDBCase;
import idxdiff.tidb.ast.TiDBCastOperation;
import idxdiff.tidb.ast.TiDBColumnReference;
import idxdiff.tidb.ast.TiDBConstant;
import idxdiff.tidb.ast.TiDBExpression;
import idxdiff.tidb.ast.TiDBFunctionCall;
import idxdiff.tidb.ast.TiDBJoin;
import idxdiff.tidb.ast.TiDBSelect;
import idxdiff.tidb.ast.TiDBTableReference;
import idxdiff.tidb.ast.TiDBText;

public interface TiDBVisitor {

    default void visit(TiDBExpression expr) {
        if (expr instanceof TiDBConstant) {
            visit((TiDBConstant) expr);
        } else if (expr instanceof TiDBColumnReference) {
            visit((TiDBColumnReference) expr);
        } else if (expr instanceof TiDBSelect) {
            visit((TiDBSelect) expr);
        } else if (expr instanceof TiDBTableReference) {
            visit((TiDBTableReference) expr);
        } else if (expr instanceof TiDBFunctionCall) {
            visit((TiDBFunctionCall) expr);
        } else if (expr instanceof TiDBJoin) {
            visit((TiDBJoin) expr);
        } else if (expr instanceof TiDBText) {
            visit((TiDBText) expr);
        } else if (expr instanceof TiDBAggregate) {
            visit((TiDBAggregate) expr);
        } else if (expr instanceof TiDBCastOperation) {
            visit((TiDBCastOperation) expr);
        } else if (expr instanceof TiDBCase) {
            visit((TiDBCase) expr);
        } else {
            throw new AssertionError(expr.getClass());
        }
    }

    void visit(TiDBCase caseExpr);

    void visit(TiDBCastOperation cast);

    void visit(TiDBAggregate aggr);

    void visit(TiDBFunctionCall call);

    void visit(TiDBConstant expr);

    void visit(TiDBColumnReference expr);

    void visit(TiDBTableReference expr);

    void visit(TiDBSelect select);

    void visit(TiDBJoin join);

    void visit(TiDBText text);

    static String asString(TiDBExpression expr) {
        TiDBToStringVisitor v = new TiDBToStringVisitor();
        v.visit(expr);
        return v.getString();
    }

}
