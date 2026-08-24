package idxdiff.postgres;

import java.util.List;

import idxdiff.postgres.PostgresSchema.PostgresColumn;
import idxdiff.postgres.PostgresSchema.PostgresDataType;
import idxdiff.postgres.ast.PostgresAggregate;
import idxdiff.postgres.ast.PostgresBetweenOperation;
import idxdiff.postgres.ast.PostgresBinaryLogicalOperation;
import idxdiff.postgres.ast.PostgresCastOperation;
import idxdiff.postgres.ast.PostgresCollate;
import idxdiff.postgres.ast.PostgresColumnReference;
import idxdiff.postgres.ast.PostgresColumnValue;
import idxdiff.postgres.ast.PostgresConstant;
import idxdiff.postgres.ast.PostgresExpression;
import idxdiff.postgres.ast.PostgresFunction;
import idxdiff.postgres.ast.PostgresInOperation;
import idxdiff.postgres.ast.PostgresLikeOperation;
import idxdiff.postgres.ast.PostgresOrderByTerm;
import idxdiff.postgres.ast.PostgresPOSIXRegularExpression;
import idxdiff.postgres.ast.PostgresPostfixOperation;
import idxdiff.postgres.ast.PostgresPostfixText;
import idxdiff.postgres.ast.PostgresPrefixOperation;
import idxdiff.postgres.ast.PostgresSelect;
import idxdiff.postgres.ast.PostgresSelect.PostgresFromTable;
import idxdiff.postgres.ast.PostgresSelect.PostgresSubquery;
import idxdiff.postgres.ast.PostgresSimilarTo;
import idxdiff.postgres.ast.PostgresTableReference;
import idxdiff.postgres.ast.PostgresWindowFunction;
import idxdiff.postgres.gen.PostgresExpressionGenerator;

public interface PostgresVisitor {

    void visit(PostgresConstant constant);

    void visit(PostgresPostfixOperation op);

    void visit(PostgresColumnValue c);

    void visit(PostgresColumnReference c);

    void visit(PostgresTableReference tb);

    void visit(PostgresPrefixOperation op);

    void visit(PostgresSelect op);

    void visit(PostgresOrderByTerm op);

    void visit(PostgresFunction f);

    void visit(PostgresCastOperation cast);

    void visit(PostgresBetweenOperation op);

    void visit(PostgresInOperation op);

    void visit(PostgresPostfixText op);

    void visit(PostgresAggregate op);

    void visit(PostgresSimilarTo op);

    void visit(PostgresCollate op);

    void visit(PostgresPOSIXRegularExpression op);

    void visit(PostgresFromTable from);

    void visit(PostgresSubquery subquery);

    void visit(PostgresBinaryLogicalOperation op);

    void visit(PostgresLikeOperation op);

    void visit(PostgresWindowFunction windowFunction);

    default void visit(PostgresExpression expression) {
        if (expression instanceof PostgresConstant) {
            visit((PostgresConstant) expression);
        } else if (expression instanceof PostgresPostfixOperation) {
            visit((PostgresPostfixOperation) expression);
        } else if (expression instanceof PostgresColumnValue) {
            visit((PostgresColumnValue) expression);
        } else if (expression instanceof PostgresPrefixOperation) {
            visit((PostgresPrefixOperation) expression);
        } else if (expression instanceof PostgresSelect) {
            visit((PostgresSelect) expression);
        } else if (expression instanceof PostgresOrderByTerm) {
            visit((PostgresOrderByTerm) expression);
        } else if (expression instanceof PostgresFunction) {
            visit((PostgresFunction) expression);
        } else if (expression instanceof PostgresCastOperation) {
            visit((PostgresCastOperation) expression);
        } else if (expression instanceof PostgresBetweenOperation) {
            visit((PostgresBetweenOperation) expression);
        } else if (expression instanceof PostgresInOperation) {
            visit((PostgresInOperation) expression);
        } else if (expression instanceof PostgresAggregate) {
            visit((PostgresAggregate) expression);
        } else if (expression instanceof PostgresPostfixText) {
            visit((PostgresPostfixText) expression);
        } else if (expression instanceof PostgresSimilarTo) {
            visit((PostgresSimilarTo) expression);
        } else if (expression instanceof PostgresPOSIXRegularExpression) {
            visit((PostgresPOSIXRegularExpression) expression);
        } else if (expression instanceof PostgresCollate) {
            visit((PostgresCollate) expression);
        } else if (expression instanceof PostgresFromTable) {
            visit((PostgresFromTable) expression);
        } else if (expression instanceof PostgresSubquery) {
            visit((PostgresSubquery) expression);
        } else if (expression instanceof PostgresLikeOperation) {
            visit((PostgresLikeOperation) expression);
        } else if (expression instanceof PostgresColumnReference) {
            visit((PostgresColumnReference) expression);
        } else if (expression instanceof PostgresTableReference) {
            visit((PostgresTableReference) expression);
        } else if (expression instanceof PostgresWindowFunction) {
            visit((PostgresWindowFunction) expression);
        } else {
            throw new AssertionError(expression);
        }
    }

    static String asString(PostgresExpression expr) {
        PostgresToStringVisitor visitor = new PostgresToStringVisitor();
        visitor.visit(expr);
        return visitor.get();
    }

    static String asExpectedValues(PostgresExpression expr) {
        PostgresExpectedValueVisitor v = new PostgresExpectedValueVisitor();
        v.visit(expr);
        return v.get();
    }

    static String getExpressionAsString(PostgresGlobalState globalState, PostgresDataType type,
            List<PostgresColumn> columns) {
        PostgresExpression expression = PostgresExpressionGenerator.generateExpression(globalState, columns, type);
        PostgresToStringVisitor visitor = new PostgresToStringVisitor();
        visitor.visit(expression);
        return visitor.get();
    }

}
