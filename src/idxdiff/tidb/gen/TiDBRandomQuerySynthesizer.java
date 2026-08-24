package idxdiff.tidb.gen;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import idxdiff.Randomly;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.tidb.TiDBExpressionGenerator;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema.TiDBTables;
import idxdiff.tidb.ast.TiDBExpression;
import idxdiff.tidb.ast.TiDBSelect;
import idxdiff.tidb.ast.TiDBTableReference;
import idxdiff.tidb.visitor.TiDBVisitor;

public final class TiDBRandomQuerySynthesizer {

    private TiDBRandomQuerySynthesizer() {
    }

    public static SQLQueryAdapter generate(TiDBGlobalState globalState, int nrColumns) {
        TiDBSelect select = generateSelect(globalState, nrColumns);
        return new SQLQueryAdapter(TiDBVisitor.asString(select));
    }

    public static TiDBSelect generateSelect(TiDBGlobalState globalState, int nrColumns) {
        TiDBTables tables = globalState.getSchema().getRandomTableNonEmptyTables();
        TiDBExpressionGenerator gen = new TiDBExpressionGenerator(globalState).setColumns(tables.getColumns());
        TiDBSelect select = new TiDBSelect();
        // select.setDistinct(Randomly.getBoolean());
        List<TiDBExpression> columns = new ArrayList<>();
        // TODO: also generate aggregates
        columns.addAll(gen.generateExpressions(nrColumns));
        select.setFetchColumns(columns);
        List<TiDBExpression> tableList = tables.getTables().stream().map(t -> new TiDBTableReference(t))
                .collect(Collectors.toList());
        // TODO: generate joins
        select.setFromList(tableList);
        if (Randomly.getBoolean()) {
            select.setWhereClause(gen.generateExpression());
        }
        if (Randomly.getBooleanWithRatherLowProbability()) {
            select.setOrderByClauses(gen.generateOrderBys());
        }
        if (Randomly.getBoolean()) {
            select.setGroupByExpressions(gen.generateExpressions(Randomly.smallNumber() + 1));
            if (Randomly.getBoolean()) {
                select.setHavingClause(gen.generateHavingClause());
            }
        }
        if (Randomly.getBoolean()) {
            select.setLimitClause(gen.generateExpression());
        }
        if (Randomly.getBoolean()) {
            select.setOffsetClause(gen.generateExpression());
        }
        return select;
    }

}
