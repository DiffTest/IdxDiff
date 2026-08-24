package idxdiff;

import java.util.List;

import idxdiff.common.log.LoggableFactory;
import idxdiff.common.log.SQLLoggableFactory;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.common.schema.AbstractSchema;
import idxdiff.common.schema.AbstractTable;

public abstract class SQLProviderAdapter<G extends SQLGlobalState<O, ? extends AbstractSchema<G, ?>>, O extends DBMSSpecificOptions<? extends OracleFactory<G>>>
        extends ProviderAdapter<G, O, SQLConnection> {
    protected SQLProviderAdapter(Class<G> globalClass, Class<O> optionClass) {
        super(globalClass, optionClass);
    }

    @Override
    public LoggableFactory getLoggableFactory() {
        return new SQLLoggableFactory();
    }

    @Override
    protected void checkViewsAreValid(G globalState) {
        List<? extends AbstractTable<?, ?, ?>> views = globalState.getSchema().getViews();
        for (AbstractTable<?, ?, ?> view : views) {
            SQLQueryAdapter q = new SQLQueryAdapter("SELECT 1 FROM " + view.getName() + " LIMIT 1");
            try {
                if (!q.execute(globalState)) {
                    dropView(globalState, view.getName());
                }
            } catch (Throwable t) {
                dropView(globalState, view.getName());
            }
        }
    }

    private void dropView(G globalState, String viewName) {
        try {
            globalState.executeStatement(new SQLQueryAdapter("DROP VIEW " + viewName, true));
        } catch (Throwable t2) {
            throw new IgnoreMeException();
        }
    }
}
