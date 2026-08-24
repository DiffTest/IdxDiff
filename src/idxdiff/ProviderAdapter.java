package idxdiff;

import java.sql.SQLException;
import java.util.List;

import idxdiff.StateToReproduce.OracleRunReproductionState;
import idxdiff.common.oracle.TestOracle;
import idxdiff.common.schema.AbstractSchema;

public abstract class ProviderAdapter<G extends GlobalState<O, ? extends AbstractSchema<G, ?>, C>, O extends DBMSSpecificOptions<? extends OracleFactory<G>>, C extends IdxDiffDBConnection>
        implements DatabaseProvider<G, O, C> {

    private final Class<G> globalClass;
    private final Class<O> optionClass;

    protected ProviderAdapter(Class<G> globalClass, Class<O> optionClass) {
        this.globalClass = globalClass;
        this.optionClass = optionClass;
    }

    @Override
    public StateToReproduce getStateToReproduce(String databaseName) {
        return new StateToReproduce(databaseName, this);
    }

    @Override
    public Class<G> getGlobalStateClass() {
        return globalClass;
    }

    @Override
    public Class<O> getOptionClass() {
        return optionClass;
    }

    @Override
    public Reproducer<G> generateAndTestDatabase(G globalState) throws Exception {
        try {
            generateDatabase(globalState);
            checkViewsAreValid(globalState);
            globalState.getManager().incrementCreateDatabase();

            TestOracle<G> oracle = getTestOracle(globalState);
            for (int i = 0; i < globalState.getOptions().getNrQueries(); i++) {
                try (OracleRunReproductionState localState = globalState.getState().createLocalState()) {
                    assert localState != null;
                    try {
                        oracle.check();
                        globalState.getManager().incrementSelectQueryCount();
                    } catch (IgnoreMeException ignored) {
                    } catch (AssertionError e) {
                        Reproducer<G> reproducer = oracle.getLastReproducer();
                        if (reproducer != null) {
                            return reproducer;
                        }
                        throw e;
                    }
                    localState.executedWithoutError();
                }
            }
        } finally {
            globalState.getConnection().close();
        }
        return null;
    }

    protected abstract void checkViewsAreValid(G globalState) throws SQLException;

    protected TestOracle<G> getTestOracle(G globalState) throws Exception {
        List<? extends OracleFactory<G>> testOracleFactory = globalState.getDbmsSpecificOptions()
                .getTestOracleFactory();
        boolean testOracleRequiresMoreThanZeroRows = testOracleFactory.stream()
                .anyMatch(OracleFactory::requiresAllTablesToContainRows);
        boolean userRequiresMoreThanZeroRows = globalState.getOptions().testOnlyWithMoreThanZeroRows();
        boolean checkZeroRows = testOracleRequiresMoreThanZeroRows || userRequiresMoreThanZeroRows;
        if (checkZeroRows && globalState.getSchema().containsTableWithZeroRows(globalState)) {
            throw new IgnoreMeException();
        }
        if (testOracleFactory.isEmpty()) {
            throw new AssertionError("No test oracle was specified");
        }
        return testOracleFactory.get(0).create(globalState);
    }

    public abstract void generateDatabase(G globalState) throws Exception;

}
