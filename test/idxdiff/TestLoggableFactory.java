package idxdiff;

import org.junit.jupiter.api.Test;
import idxdiff.common.log.SQLLoggableFactory;
import idxdiff.common.query.SQLQueryAdapter;

public class TestLoggableFactory {

    @Test
    public void testLogCreateTable() {
        String query = "CREATE TABLE t1 (c1 INT)";
        SQLLoggableFactory logger = new SQLLoggableFactory();
        SQLQueryAdapter queryAdapter = logger.getQueryForStateToReproduce(query);
        assert (queryAdapter.couldAffectSchema());
    }

}
