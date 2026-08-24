package idxdiff.mysql.gen;

import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mysql.MySQLGlobalState;
import idxdiff.mysql.MySQLSchema.MySQLTable;

/**
 * @see <a href="https://dev.mysql.com/doc/refman/8.0/en/drop-index.html">DROP INDEX Statement</a>
 */
public final class MySQLDropIndex {

    private MySQLDropIndex() {
    }

    // DROP INDEX index_name ON tbl_name
    // [algorithm_option | lock_option] ...
    //
    // algorithm_option:
    // ALGORITHM [=] {DEFAULT|INPLACE|COPY}
    //
    // lock_option:
    // LOCK [=] {DEFAULT|NONE|SHARED|EXCLUSIVE}

    public static SQLQueryAdapter generate(MySQLGlobalState globalState) {
        MySQLTable table = globalState.getSchema().getRandomTable();
        if (!table.hasIndexes()) {
            throw new IgnoreMeException();
        }
        var idx = table.getRandomIndex();
        // [FIX] Skip PRIMARY indexes — DROP INDEX PRIMARY is invalid in MySQL
        // (requires ALTER TABLE DROP PRIMARY KEY). Without this check, the fuzzer
        // generates invalid DROP INDEX PRIMARY in an infinite loop until OOM.
        if (idx.getIndexName().equals("PRIMARY")) {
            throw new IgnoreMeException();
        }
        StringBuilder sb = new StringBuilder();
        sb.append("DROP INDEX ");
        sb.append(idx.getIndexName());
        sb.append(" ON ");
        sb.append(table.getName());
        if (Randomly.getBoolean()) {
            sb.append(" ALGORITHM=");
            sb.append(Randomly.fromOptions("DEFAULT", "INPLACE", "COPY"));
        }
        if (Randomly.getBoolean()) {
            sb.append(" LOCK=");
            sb.append(Randomly.fromOptions("DEFAULT", "NONE", "SHARED", "EXCLUSIVE"));
        }
        return new SQLQueryAdapter(sb.toString(),
                ExpectedErrors.from("LOCK=NONE is not supported", "ALGORITHM=INPLACE is not supported",
                        "Data truncation", "Data truncated for functional index",
                        "A primary key index cannot be invisible",
                        "there can be only one auto column and it must be defined as a key"));
    }

}
