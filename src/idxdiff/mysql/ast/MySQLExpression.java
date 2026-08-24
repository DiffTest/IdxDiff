package idxdiff.mysql.ast;

import idxdiff.common.ast.newast.Expression;
import idxdiff.mysql.MySQLSchema.MySQLColumn;

public interface MySQLExpression extends Expression<MySQLColumn> {

    default MySQLConstant getExpectedValue() {
        throw new AssertionError("PQS not supported for this operator");
    }

}
