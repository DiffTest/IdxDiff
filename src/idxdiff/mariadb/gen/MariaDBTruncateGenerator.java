package idxdiff.mariadb.gen;

import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mariadb.MariaDBErrors;
import idxdiff.mariadb.MariaDBSchema;

public final class MariaDBTruncateGenerator {

    private MariaDBTruncateGenerator() {
    }

    public static SQLQueryAdapter truncate(MariaDBSchema s) {
        StringBuilder sb = new StringBuilder("TRUNCATE ");
        sb.append(s.getRandomTable().getName());
        sb.append(" ");
        MariaDBCommon.addWaitClause(sb);
        ExpectedErrors errors = new ExpectedErrors();
        MariaDBErrors.addCommonErrors(errors);
        return new SQLQueryAdapter(sb.toString(), errors);
    }

}
