package idxdiff.postgres.ast;

import idxdiff.common.ast.newast.Expression;
import idxdiff.postgres.PostgresSchema.PostgresColumn;
import idxdiff.postgres.PostgresSchema.PostgresDataType;

public interface PostgresExpression extends Expression<PostgresColumn> {

    default PostgresDataType getExpressionType() {
        return null;
    }

    default PostgresConstant getExpectedValue() {
        return null;
    }
}
