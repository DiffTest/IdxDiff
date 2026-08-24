package idxdiff.tidb.gen;

import java.sql.SQLException;
import java.util.List;
import java.util.stream.Collectors;

import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.tidb.TiDBExpressionGenerator;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema.TiDBColumn;
import idxdiff.tidb.TiDBSchema.TiDBCompositeDataType;
import idxdiff.tidb.TiDBSchema.TiDBDataType;
import idxdiff.tidb.TiDBSchema.TiDBTable;
import idxdiff.tidb.ast.TiDBCastOperation;
import idxdiff.tidb.ast.TiDBColumnReference;
import idxdiff.tidb.ast.TiDBConstant;
import idxdiff.tidb.ast.TiDBExpression;
import idxdiff.tidb.visitor.TiDBVisitor;

public final class TiDBIndexGenerator {

    private TiDBIndexGenerator() {
    }

    public static SQLQueryAdapter getQuery(TiDBGlobalState globalState) throws SQLException {
        if (globalState.getSchema().getIndexCount() > globalState.getDbmsSpecificOptions().maxNumIndexes) {
            throw new IgnoreMeException();
        }
        ExpectedErrors errors = new ExpectedErrors();

        TiDBTable randomTable = globalState.getSchema().getRandomTable(t -> !t.isView());
        return generateIndexForTable(globalState, randomTable);
    }

    /**
     * Generate a CREATE INDEX statement targeting a specific table.
     * Used by TiDBIndexOracle to ensure indexes are created on the same table
     * that the test query operates on.
     */
    public static SQLQueryAdapter generateIndexForTable(TiDBGlobalState globalState, TiDBTable table) throws SQLException {
        if (globalState.getSchema().getIndexCount() > globalState.getDbmsSpecificOptions().maxNumIndexes) {
            throw new IgnoreMeException();
        }
        ExpectedErrors errors = new ExpectedErrors();

        String indexName = globalState.getSchema().getFreeIndexName();
        StringBuilder sb = new StringBuilder("CREATE ");

        // Determine if UNIQUE index
        boolean isUnique = Randomly.getBooleanWithRatherLowProbability() && !table.isPartitioned();
        if (isUnique) {
            sb.append("UNIQUE ");
            errors.add("Duplicate for key");
            errors.add("Duplicate entry ");
        }
        sb.append("INDEX ");
        sb.append(indexName);
        sb.append(" ON ");
        sb.append(table.getName());
        sb.append("(");

        // For UNIQUE indexes, exclude AUTO_INCREMENT columns
        List<TiDBColumn> candidateCols;
        if (isUnique) {
            candidateCols = table.getColumns().stream()
                    .filter(c -> !c.isAutoIncrement())
                    .collect(Collectors.toList());
            if (candidateCols.isEmpty()) {
                throw new IgnoreMeException();
            }
        } else {
            candidateCols = table.getColumns();
        }

        // Decide: expression index (~10%) or column-based index (~90%)
        boolean useExprIndex = Randomly.getBooleanWithRatherLowProbability();
        if (useExprIndex) {
            // Exclude generated and AUTO_INCREMENT columns from expression index
            List<TiDBColumn> exprCols = candidateCols.stream()
                    .filter(c -> !c.isGenerated() && !c.isAutoIncrement())
                    .collect(Collectors.toList());
            if (exprCols.isEmpty()) {
                useExprIndex = false;
            } else {
                try {
                    StringBuilder exprSB = new StringBuilder();
                    TiDBExpressionGenerator gen = new TiDBExpressionGenerator(globalState)
                            .setColumns(exprCols);
                    int nrExpr = Math.min(Randomly.smallNumber() + 1, 3);
                    for (int i = 0; i < nrExpr; i++) {
                        if (i != 0) {
                            exprSB.append(", ");
                        }
                        exprSB.append("(");
                        TiDBExpression expr = gen.generateExpression();
                        // TiDB rejects bare column/constant as expression index entries
                        // (e.g. "Expression index on a column is not supported");
                        // wrap in CAST to ensure a non-trivial expression
                        if (expr instanceof TiDBColumnReference || expr instanceof TiDBConstant) {
                            expr = new TiDBCastOperation(expr,
                                    Randomly.fromOptions("SIGNED", "CHAR", "DECIMAL"));
                        }
                        exprSB.append(TiDBVisitor.asString(expr));
                        exprSB.append(")");
                    }
                    sb.append(exprSB.toString());
                } catch (Exception e) {
                    useExprIndex = false;
                }
            }
        }

        if (!useExprIndex) {
            // Column-based index with optional prefix length for TEXT columns
            // 50% chance: composite index with 2-3 columns for multi-column index testing
            int nr;
            if (Randomly.getBoolean()) {
                nr = Math.min(candidateCols.size(), Randomly.fromOptions(2, 2, 3));
            } else {
                nr = Math.min(Randomly.smallNumber() + 1, candidateCols.size());
            }
            List<TiDBColumn> subset = Randomly.extractNrRandomColumns(candidateCols, nr);
            for (int i = 0; i < subset.size(); i++) {
                if (i != 0) {
                    sb.append(", ");
                }
                TiDBColumn col = subset.get(i);
                sb.append(col.getName());
                // 15% chance: add prefix length for TEXT type columns
                TiDBCompositeDataType colType = col.getType();
                if (colType != null && colType.getPrimitiveDataType() == TiDBDataType.TEXT
                        && Randomly.getBooleanWithRatherLowProbability()) {
                    sb.append("(").append(Randomly.fromOptions(1, 2, 3, 5, 10)).append(")");
                    errors.add("Incorrect prefix key"); // prefix length exceeds column width
                }
                if (Randomly.getBoolean()) {
                    sb.append(" ");
                    sb.append(Randomly.fromOptions("ASC", "DESC"));
                }
            }
        }

        sb.append(")");
        if (Randomly.getBooleanWithRatherLowProbability()) {
            sb.append(" KEY_BLOCK_SIZE ");
            sb.append(Randomly.getPositiveOrZeroNonCachedInteger());
        }

        // Error handling
        errors.add("Cannot decode index value, because"); // invalid value for generated column
        errors.add("index already exist");
        errors.add("Data truncation");
        errors.add("key was too long");
        errors.add("BLOB/TEXT column"); // BLOB/TEXT columns cannot be indexed without a prefix
        errors.add("used in key specification without a key length");
        // Expression index errors
        errors.add("cannot index the expression");
        errors.add("functional index");
        errors.add("Cannot create a functional index");
        return new SQLQueryAdapter(sb.toString(), errors, true);
    }

}