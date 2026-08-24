package idxdiff.mysql.gen.admin;

import java.util.stream.Collectors;

import idxdiff.Randomly;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mysql.MySQLGlobalState;

public final class MySQLReset {

    private MySQLReset() {
    }

    public static SQLQueryAdapter create(MySQLGlobalState globalState) {
        StringBuilder sb = new StringBuilder();
        sb.append("RESET ");
        sb.append(Randomly.nonEmptySubset("MASTER", "SLAVE").stream().collect(Collectors.joining(", ")));
        return new SQLQueryAdapter(sb.toString());
    }

}
