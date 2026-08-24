package idxdiff.tidb.gen;

import java.sql.SQLException;
import java.util.List;

import idxdiff.Randomly;
import idxdiff.common.gen.AbstractUpdateGenerator;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.tidb.TiDBErrors;
import idxdiff.tidb.TiDBExpressionGenerator;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema.TiDBColumn;
import idxdiff.tidb.TiDBSchema.TiDBTable;
import idxdiff.tidb.visitor.TiDBVisitor;

public final class TiDBUpdateGenerator extends AbstractUpdateGenerator<TiDBColumn> {

    private final TiDBGlobalState globalState;
    private TiDBExpressionGenerator gen;

    private TiDBUpdateGenerator(TiDBGlobalState globalState) {
        this.globalState = globalState;
    }

    public static SQLQueryAdapter getQuery(TiDBGlobalState globalState) throws SQLException {
        return new TiDBUpdateGenerator(globalState).generate();
    }

    private SQLQueryAdapter generate() throws SQLException {
        TiDBTable table = globalState.getSchema().getRandomTable(t -> !t.isView());
        List<TiDBColumn> columns = table.getRandomNonEmptyColumnSubset();
        gen = new TiDBExpressionGenerator(globalState).setColumns(table.getColumns());
        sb.append("UPDATE ");
        sb.append(table.getName());
        sb.append(" SET ");
        updateColumns(columns);
        if (Randomly.getBoolean()) {
            sb.append(" WHERE ");
            TiDBErrors.addExpressionErrors(errors);
            sb.append(TiDBVisitor.asString(gen.generateExpression()));
        }
        TiDBErrors.addInsertErrors(errors);

        return new SQLQueryAdapter(sb.toString(), errors);
    }

    @Override
    protected void updateValue(TiDBColumn column) {
        if (Randomly.getBoolean()) {
            sb.append(gen.generateConstant(column.getType().getPrimitiveDataType()));
        } else {
            // Use type-aware expression generation to avoid "cannot convert datum" errors
            // (e.g., assigning a numeric expression to a DATE column)
            sb.append(TiDBVisitor.asString(gen.generateExpression(column.getType().getPrimitiveDataType())));
            TiDBErrors.addExpressionErrors(errors);
        }
    }

}
