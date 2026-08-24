package idxdiff.tidb.gen;

import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.tidb.TiDBErrors;
import idxdiff.tidb.TiDBExpressionGenerator;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema.TiDBColumn;
import idxdiff.tidb.TiDBSchema.TiDBTable;
import idxdiff.tidb.ast.TiDBColumnReference;
import idxdiff.tidb.ast.TiDBExpression;
import idxdiff.tidb.ast.TiDBOrderingTerm;
import idxdiff.tidb.visitor.TiDBVisitor;

public final class TiDBDeleteGenerator {

    private TiDBDeleteGenerator() {
    }

    public static SQLQueryAdapter getQuery(TiDBGlobalState globalState) throws SQLException {
        ExpectedErrors errors = ExpectedErrors.newErrors().with(TiDBErrors.getExpressionErrors()).build();
        TiDBTable table = globalState.getSchema().getRandomTable(t -> !t.isView());
        TiDBExpressionGenerator gen = new TiDBExpressionGenerator(globalState).setColumns(table.getColumns());
        StringBuilder sb = new StringBuilder("DELETE ");
        if (Randomly.getBooleanWithSmallProbability()) {
            sb.append("LOW_PRIORITY ");
        }
        if (Randomly.getBooleanWithSmallProbability()) {
            sb.append("QUICK ");
        }
        if (Randomly.getBooleanWithSmallProbability()) {
            sb.append("IGNORE ");
        }
        sb.append("FROM ");
        sb.append(table.getName());
        if (Randomly.getBoolean()) {
            sb.append(" WHERE ");
            sb.append(TiDBVisitor.asString(gen.generateExpression()));
            errors.add("Truncated incorrect");
            errors.add("Data truncation");
            errors.add("Truncated incorrect FLOAT value");
        }
        if (Randomly.getBoolean()) {
            sb.append(" ORDER BY ");
            // Use column-based ORDER BY instead of arbitrary expressions.
            // In DELETE's ORDER BY, bare integers are interpreted as column position
            // numbers (not constants), causing "Unknown column" false positives.
            List<TiDBExpression> orderByExprs = new ArrayList<>();
            List<TiDBColumn> columns = table.getColumns();
            int nr = Randomly.smallNumber() + 1;
            for (int i = 0; i < nr; i++) {
                TiDBExpression colExpr = new TiDBColumnReference(Randomly.fromList(columns));
                if (Randomly.getBoolean()) {
                    colExpr = new TiDBOrderingTerm(colExpr, Randomly.getBoolean());
                }
                orderByExprs.add(colExpr);
            }
            sb.append(orderByExprs.stream().map(o -> TiDBVisitor.asString(o))
                    .collect(Collectors.joining(", ")));
        }
        if (Randomly.getBoolean()) {
            sb.append(" LIMIT ");
            sb.append(Randomly.getNotCachedInteger(0, Integer.MAX_VALUE));
        }
        errors.add("Bad Number");
        errors.add("Truncated incorrect"); // https://github.com/pingcap/tidb/issues/24292
        errors.add("is not valid for CHARACTER SET");
        errors.add("Division by 0");
        errors.add("error parsing regexp");
        return new SQLQueryAdapter(sb.toString(), errors);

    }

}
