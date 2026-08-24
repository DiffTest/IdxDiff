package idxdiff.mysql;

import idxdiff.mysql.ast.MySQLAggregate;
import idxdiff.mysql.ast.MySQLBetweenOperation;
import idxdiff.mysql.ast.MySQLBinaryComparisonOperation;
import idxdiff.mysql.ast.MySQLBinaryLogicalOperation;
import idxdiff.mysql.ast.MySQLBinaryOperation;
import idxdiff.mysql.ast.MySQLCaseOperator;
import idxdiff.mysql.ast.MySQLCastOperation;
import idxdiff.mysql.ast.MySQLCollate;
import idxdiff.mysql.ast.MySQLColumnReference;
import idxdiff.mysql.ast.MySQLComputableFunction;
import idxdiff.mysql.ast.MySQLConstant;
import idxdiff.mysql.ast.MySQLExists;
import idxdiff.mysql.ast.MySQLExpression;
import idxdiff.mysql.ast.MySQLInOperation;
import idxdiff.mysql.ast.MySQLJoin;
import idxdiff.mysql.ast.MySQLOrderByTerm;
import idxdiff.mysql.ast.MySQLSelect;
import idxdiff.mysql.ast.MySQLStringExpression;
import idxdiff.mysql.ast.MySQLTableReference;
import idxdiff.mysql.ast.MySQLText;
import idxdiff.mysql.ast.MySQLUnaryPostfixOperation;

public interface MySQLVisitor {

    void visit(MySQLTableReference ref);

    void visit(MySQLConstant constant);

    void visit(MySQLColumnReference column);

    void visit(MySQLUnaryPostfixOperation column);

    void visit(MySQLComputableFunction f);

    void visit(MySQLBinaryLogicalOperation op);

    void visit(MySQLSelect select);

    void visit(MySQLBinaryComparisonOperation op);

    void visit(MySQLCastOperation op);

    void visit(MySQLInOperation op);

    void visit(MySQLBinaryOperation op);

    void visit(MySQLOrderByTerm op);

    void visit(MySQLExists op);

    void visit(MySQLStringExpression op);

    void visit(MySQLBetweenOperation op);

    void visit(MySQLCollate collate);

    void visit(MySQLJoin join);

    void visit(MySQLText text);

    void visit(MySQLAggregate aggregate);

    void visit(MySQLCaseOperator caseOp);

    default void visit(MySQLExpression expr) {
        if (expr instanceof MySQLConstant) {
            visit((MySQLConstant) expr);
        } else if (expr instanceof MySQLColumnReference) {
            visit((MySQLColumnReference) expr);
        } else if (expr instanceof MySQLUnaryPostfixOperation) {
            visit((MySQLUnaryPostfixOperation) expr);
        } else if (expr instanceof MySQLComputableFunction) {
            visit((MySQLComputableFunction) expr);
        } else if (expr instanceof MySQLBinaryLogicalOperation) {
            visit((MySQLBinaryLogicalOperation) expr);
        } else if (expr instanceof MySQLSelect) {
            visit((MySQLSelect) expr);
        } else if (expr instanceof MySQLBinaryComparisonOperation) {
            visit((MySQLBinaryComparisonOperation) expr);
        } else if (expr instanceof MySQLCastOperation) {
            visit((MySQLCastOperation) expr);
        } else if (expr instanceof MySQLInOperation) {
            visit((MySQLInOperation) expr);
        } else if (expr instanceof MySQLBinaryOperation) {
            visit((MySQLBinaryOperation) expr);
        } else if (expr instanceof MySQLOrderByTerm) {
            visit((MySQLOrderByTerm) expr);
        } else if (expr instanceof MySQLExists) {
            visit((MySQLExists) expr);
        } else if (expr instanceof MySQLJoin) {
            visit((MySQLJoin) expr);
        } else if (expr instanceof MySQLStringExpression) {
            visit((MySQLStringExpression) expr);
        } else if (expr instanceof MySQLBetweenOperation) {
            visit((MySQLBetweenOperation) expr);
        } else if (expr instanceof MySQLTableReference) {
            visit((MySQLTableReference) expr);
        } else if (expr instanceof MySQLCollate) {
            visit((MySQLCollate) expr);
        } else if (expr instanceof MySQLText) {
            visit((MySQLText) expr);
        } else if (expr instanceof MySQLAggregate) {
            visit((MySQLAggregate) expr);
        } else if (expr instanceof MySQLCaseOperator) {
            visit((MySQLCaseOperator) expr);
        } else {
            throw new AssertionError(expr);
        }
    }

    static String asString(MySQLExpression expr) {
        MySQLToStringVisitor visitor = new MySQLToStringVisitor();
        visitor.visit(expr);
        return visitor.get();
    }

    static String asExpectedValues(MySQLExpression expr) {
        MySQLExpectedValueVisitor visitor = new MySQLExpectedValueVisitor();
        visitor.visit(expr);
        return visitor.get();
    }

}
