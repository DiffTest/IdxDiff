package idxdiff.postgres.gen;

import java.util.stream.Collectors;

import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.postgres.PostgresGlobalState;
import idxdiff.postgres.PostgresSchema.PostgresTable;

public final class PostgresAnalyzeGenerator {

    private PostgresAnalyzeGenerator() {
    }

    public static SQLQueryAdapter create(PostgresGlobalState globalState) {
        PostgresTable table = globalState.getSchema().getRandomTable();
        StringBuilder sb = new StringBuilder("ANALYZE");
        if (Randomly.getBoolean()) {
            sb.append("(");
            if (Randomly.getBoolean()) {
                sb.append(" VERBOSE");
            } else {
                sb.append(" SKIP_LOCKED");
            }
            sb.append(")");
        }
        if (Randomly.getBoolean()) {
            sb.append(" ");
            sb.append(table.getName());
            if (Randomly.getBoolean()) {
                sb.append("(");
                sb.append(table.getRandomNonEmptyColumnSubset().stream().map(c -> c.getName())
                        .collect(Collectors.joining(", ")));
                sb.append(")");
            }
        }
        // FIXME: bug in postgres?
        return new SQLQueryAdapter(sb.toString(), ExpectedErrors.from("deadlock"));
    }

}
