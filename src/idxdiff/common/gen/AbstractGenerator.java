package idxdiff.common.gen;

import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;

public abstract class AbstractGenerator {

    protected final ExpectedErrors errors = new ExpectedErrors();
    protected final StringBuilder sb = new StringBuilder();
    protected boolean canAffectSchema;

    public SQLQueryAdapter getQuery() {
        buildStatement();
        return new SQLQueryAdapter(sb.toString(), errors, canAffectSchema);
    }

    public abstract void buildStatement();

}
