package idxdiff.common.query;

@FunctionalInterface
public interface SQLQueryProvider<S> {
    SQLQueryAdapter getQuery(S globalState) throws Exception;
}
