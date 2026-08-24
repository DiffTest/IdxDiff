package idxdiff.common.oracle;

import idxdiff.GlobalState;
import idxdiff.Reproducer;

public interface TestOracle<G extends GlobalState<?, ?, ?>> {

    void check() throws Exception;

    default Reproducer<G> getLastReproducer() {
        return null;
    }

    default String getLastQueryString() {
        throw new AssertionError("Not supported!");
    }
}
