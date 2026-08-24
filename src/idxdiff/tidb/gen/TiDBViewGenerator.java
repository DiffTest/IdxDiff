package idxdiff.tidb.gen;

import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.tidb.TiDBBugs;
import idxdiff.tidb.TiDBErrors;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.ast.TiDBSelect;

public final class TiDBViewGenerator {

    private TiDBViewGenerator() {
    }

    public static SQLQueryAdapter getQuery(TiDBGlobalState globalState) {
        if (globalState.getSchema().getDatabaseTables().size() > globalState.getDbmsSpecificOptions().maxNumTables) {
            throw new IgnoreMeException();
        }
        int nrColumns = Randomly.smallNumber() + 1;
        StringBuilder sb = new StringBuilder("CREATE ");
        if (Randomly.getBoolean()) {
            sb.append("OR REPLACE ");
        }
        if (Randomly.getBoolean()) {
            sb.append("ALGORITHM=");
            sb.append(Randomly.fromOptions("UNDEFINED", "MERGE", "TEMPTABLE"));
            sb.append(" ");
        }
        sb.append("VIEW ");
        sb.append(globalState.getSchema().getFreeViewName());
        sb.append("(");
        for (int i = 0; i < nrColumns; i++) {
            if (i != 0) {
                sb.append(", ");
            }
            sb.append("c");
            sb.append(i);
        }
        sb.append(") AS ");
        TiDBSelect select = TiDBRandomQuerySynthesizer.generateSelect(globalState, nrColumns);
        if (TiDBBugs.bug38319 && !select.getGroupByExpressions().isEmpty()) {
            throw new IgnoreMeException();
        }
        sb.append(select.asString());
        ExpectedErrors errors = new ExpectedErrors();
        TiDBErrors.addExpressionErrors(errors);
        errors.add(
                "references invalid table(s) or column(s) or function(s) or definer/invoker of view lack rights to use them");
        errors.add("Unknown column ");
        if (sb.toString().contains("\\\\")) {
            // TODO: CREATE VIEW v0(c0) AS SELECT '\\' FROM t0; causes an unexpected failure
            throw new IgnoreMeException();
        }
        return new SQLQueryAdapter(sb.toString(), errors, true);
    }

}
