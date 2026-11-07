package idxdiff.tidb.oracle;

import java.sql.ResultSet;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import idxdiff.ComparatorHelper;
import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.common.oracle.TestOracle;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.common.schema.TableIndex;
import idxdiff.tidb.TiDBErrors;
import idxdiff.tidb.TiDBExpressionGenerator;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema;
import idxdiff.tidb.TiDBSchema.TiDBColumn;
import idxdiff.tidb.TiDBSchema.TiDBTable;
import idxdiff.tidb.ast.TiDBColumnReference;
import idxdiff.tidb.ast.TiDBConstant;
import idxdiff.tidb.ast.TiDBExpression;
import idxdiff.tidb.ast.TiDBSelect;
import idxdiff.tidb.ast.TiDBTableReference;
import idxdiff.tidb.gen.TiDBIndexGenerator;
import idxdiff.tidb.visitor.TiDBVisitor;

/**
 * TiDB Index Oracle — uses TiDB-specific optimizer hints to test index-related
 * plan consistency.
 *
 * Active test modes:
 *   0: CREATE_INDEX_CONSISTENCY — query before/after index creation
 *   1: DROP_INDEX_CONSISTENCY — query before/after index drop
 *   2: USE_INDEX_HINT — USE_INDEX hint vs default
 *   3: IGNORE_INDEX_HINT — IGNORE_INDEX hint vs default
 *   4: HASH_JOIN_VS_MERGE_JOIN [DISABLED]
 *   5: INDEX_MERGE_VS_DEFAULT — USE_INDEX_MERGE vs default
 *   6: AGGREGATE_INDEX_HINT [DISABLED]
 *   7: JOIN_INDEX_SELECTION — join with forced index on each table
 *   8: MULTI_INDEX_CREATE — create multiple indexes, compare plans
 *   9: ORDER_BY_INDEX_SORT [DISABLED]
 *  10: HINT_CONSISTENCY [DISABLED]
 *  11: STREAM_AGG_VS_HASH_AGG [DISABLED]
 *  12: ADMIN_CHECK_TABLE — ADMIN CHECK TABLE after index operations
 *  13: UNIQUE_INDEX_CONSISTENCY — UNIQUE index data consistency
 *  14: PREFIX_INDEX — prefix index on VARCHAR, compare results
 *  15: COVERING_INDEX — index-only scan verification
 *  16: ORDER_BY_LIMIT_INDEX — ORDER BY + LIMIT with index vs filesort
 *  17: RANGE_BOUNDARY — range scan boundary correctness
 *  18: TIFLASH_VS_TIKV — TiFlash vs TiKV storage engine comparison
 *  19: EXPRESSION_INDEX — expression index correctness
 *  20: ICP_CONSISTENCY (variant A) [DISABLED]
 *  21: ICP_CONSISTENCY (variant B) [DISABLED]
 *  22: SQL_SEMANTIC_EQUIVALENCE — equivalent rewrites produce same results
 *  23: DETERMINISTIC_INDEX_QUERY — deterministic queries with index hints
 *  24: NULL_INDEX_HANDLING — NULL values in indexed columns
 *  25: SUBQUERY_INDEX — subquery with index conditions
 *  26: INDEX_MERGE_ENHANCED — enhanced index merge with data-aware values
 *  27: LOOSE_INDEX_SCAN — loose index scan on GROUP BY
 *  28: DML_INDEX_CONSISTENCY — DML operations maintain index consistency
 *  29: GENERATED_COLUMN_INDEX — generated column index
 *  30: AGGREGATE_INDEX — aggregate query with index
 *  31: DESC_INDEX_SORT — DESC index sort order correctness
 *  32: DROP_COLUMN_INDEX — DROP COLUMN with dependent index
 *  33: COLLATION_INDEX — collation-dependent index behavior
 *  34: IMPLICIT_TYPE_CONVERSION_INDEX — implicit type conversion in indexed comparisons
 *  35: COMPLEX_INDEX_QUERY — complex multi-index + deep expression query
 */
public class TiDBIndexOracle implements TestOracle<TiDBGlobalState> {

    private final TiDBGlobalState globalState;
    private final ExpectedErrors errors;
    private String lastQueryString;
    private int aggregateFallbackUsed = 0; // how many times COUNT(*) fallback was used

    // Flag: set to true when assertResultSorted/Strict filters out a result difference
    private boolean lastCompareFiltered = false;

    // Distinguishes between success and expected error, so compareQueries() can detect
    // asymmetric success/failure (one plan crashes while the other succeeds — may indicate a bug).
    private static class ExecResult {
        static final int SUCCESS = 0;
        static final int EXPECTED_ERROR = 1;

        final int status;
        final List<String> rows;

        ExecResult(int status, List<String> rows) {
            this.status = status;
            this.rows = rows;
        }

        boolean isSuccess() {
            return status == SUCCESS;
        }

        List<String> getRows() {
            return rows;
        }
    }

    // Index metadata cache — avoids per-query information_schema lookups
    private Map<String, List<TiDBColumn>> indexedColumnsCache = new HashMap<>();
    private Map<String, List<List<TiDBColumn>>> compositeIndexCache = new HashMap<>();
    private boolean indexCacheValid = false;

    // ANALYZE TABLE batching — only analyze every N checks
    private int checksSinceLastAnalyze = 0;
    private static final int ANALYZE_INTERVAL = 20;
    // Track which tables need ANALYZE after DDL changes
    private Set<String> tablesNeedingAnalyze = new HashSet<>();

    // Column value sampling cache — refreshed each check() call
    private Map<String, List<String>> columnValueCache = new HashMap<>();

    // Statistics tracking — monitors oracle mode effectiveness
    private java.util.Map<String, java.util.concurrent.atomic.AtomicInteger> modeStats = new java.util.HashMap<>();
    private java.util.Map<String, java.util.concurrent.atomic.AtomicInteger> modeBugStats = new java.util.HashMap<>();
    private int checkCount = 0;
    private static final int STATS_REPORT_INTERVAL = 500;
    private static final int DATA_REFRESH_INTERVAL = 3000;
    private int lastDataRefreshCheck = 0;

    public TiDBIndexOracle(TiDBGlobalState globalState) {
        this.globalState = globalState;
        this.errors = buildExpectedErrors();
    }

    private ExpectedErrors buildExpectedErrors() {
        ExpectedErrors expectedErrors = ExpectedErrors.newErrors()
                .with(TiDBErrors.getExpressionErrors())
                .build();

        expectedErrors.add("You have an error in your SQL syntax");
        expectedErrors.add("Unknown column");
        expectedErrors.add("doesn't exist");
        expectedErrors.add("does not exist");
        expectedErrors.add("cannot be null");
        expectedErrors.add("BIGINT value is out of range");
        expectedErrors.add("BIGINT UNSIGNED value is out of range");
        expectedErrors.add("DOUBLE value is out of range");
        expectedErrors.add("Data truncat");
        expectedErrors.add("not in GROUP BY clause");
        expectedErrors.add("nonaggregated column");
        expectedErrors.add("used in key specification");
        expectedErrors.add("Specified key was too long");
        expectedErrors.add("BLOB or TEXT");
        expectedErrors.add("Too many keys specified");
        expectedErrors.add("Duplicate key name");
        expectedErrors.add("index already exist");
        expectedErrors.add("Can't DROP");
        expectedErrors.add("already exists");
        // REMOVED: "Subquery returns more than 1 row" — legitimate SQL error, should be caught
        // REMOVED: "Lost connection" — server crash is exactly what we want to detect
        // REMOVED: "Query execution was interrupted" — may indicate severe TiDB bugs
        expectedErrors.add("Deadlock");
        expectedErrors.add("Lock wait timeout");
        // REMOVED: "Duplicate entry" — SELECT queries should never produce this; kept for DML in checkDMLIndexConsistency()
        expectedErrors.add("doesn't have a default value");
        expectedErrors.add("Unknown charset");
        expectedErrors.add("Unsupported creating expression index");

        // TiDB index creation errors for BLOB/TEXT/JSON columns that cannot be fully indexed
        expectedErrors.add("can't index column");      // e.g., BLOB/TEXT column without prefix length
        expectedErrors.add("Incorrect prefix key");    // e.g., prefix length exceeds column width

        // JOIN queries with unqualified column names — idxdiff generates
        // "SELECT c0 FROM t0 JOIN t1 ON ..." which is ambiguous when both
        // tables have a column named c0. This is a query generation issue,
        // not a database bug.
        expectedErrors.add("is ambiguous");

        // TiDB transient DDL errors — Information schema may change during concurrent DDL
        expectedErrors.add("Information schema is changed");

        // TiDB Cascades Planner known bug: "Some columns of Limit_XX cannot find the reference
        // from its child(ren)" — triggered by ORDER BY + LIMIT under cascades_planner=1.
        // This is a known issue in TiDB v8.5.6 where the Cascades planner fails to resolve
        // column references in Limit operators. Suppress to avoid drowning out other bugs.
        // See: database68-99 logs for repeated occurrences.
        expectedErrors.add("cannot find the reference");

        return expectedErrors;
    }

    private boolean dataPopulated = false;

    @Override
    public void check() throws Exception {
        ensureSufficientData();

        // Batched ANALYZE TABLE — only analyze every N checks
        checksSinceLastAnalyze++;
        if (checksSinceLastAnalyze >= ANALYZE_INTERVAL) {
            analyzeAllTables();
            invalidateIndexCache(); // Refresh cache after ANALYZE
            checksSinceLastAnalyze = 0;
        }

        // Clear column value cache each check
        columnValueCache.clear();

        try {
            // Weight strategy: new/complex features get 2x weight, mature features 1x
            int mode = Randomly.fromOptions(
                // === HIGH WEIGHT (2x): New/complex features, higher bug probability ===
                14, 14,     // Prefix Index (already found bugs!)
                23, 23,     // Deterministic Index Query (lowest IgnoreMe rate)
                19, 19,     // Expression Index (TiDB 7.5+, newer feature)
                15, 15,     // Covering Index (index-only scan)
                17, 17,     // Range Boundary (edge cases)
                16, 16,     // ORDER BY + LIMIT Index
                5, 5,       // Index Merge (complex optimizer path)
                13, 13,     // Unique Index Consistency
                // DEPRECATED: 20, 20, (optimizer switch pairwise — not index-related)
                24, 24,     // NULL Index Handling
                25, 25,     // Subquery + Index
                26, 26,     // Enhanced Index Merge
                27, 27,     // Loose Index Scan
                28, 28,     // DML + Index Consistency
                29, 29,     // Generated Column + Index
                30, 30,     // Aggregate + Index
                31, 31,     // DESC Index Sort
                32, 32,     // DROP COLUMN + Index
                33, 33,     // Collation + Index
                34, 34,     // Implicit Type Conversion + Index
                35, 35,     // Complex AST Query + Index Hints (uses generateComplexQuery)
                // === NORMAL WEIGHT (1x): Mature/stable features ===
                0, 1, 2, 3, 7, 8, 8, 12
                // DEPRECATED: 4 (checkHashJoinVsMergeJoin), 11 (checkStreamAggVsHashAgg)
                // NOT INDEX TESTS: 18 (TiFlash vs TiKV), 22 (SQL Semantic Equivalence)
            );
            switch (mode) {
            case 0: checkCreateIndexConsistency(); break;
            case 1: checkDropIndexConsistency(); break;
            case 2: checkUseIndexHint(); break;
            case 3: checkIgnoreIndexHint(); break;
            // DEPRECATED: case 4 (checkHashJoinVsMergeJoin) — not testing index, tests JOIN algorithm
            // case 4: checkHashJoinVsMergeJoin(); break;
            case 5: checkIndexMergeVsDefault(); break;
            case 7: checkJoinIndexSelection(); break;
            case 8: checkMultiIndexCreate(); break;
            // DEPRECATED: case 11 (checkStreamAggVsHashAgg) — not testing index, tests aggregation strategy
            // case 11: checkStreamAggVsHashAgg(); break;
            case 12: checkAdminCheckTable(); break;
            case 13: checkUniqueIndexConsistency(); break;
            // === Deep Index Bug Modes ===
            case 14: checkPrefixIndex(); break;
            case 15: checkCoveringIndex(); break;
            case 16: checkOrderByLimitIndex(); break;
            case 17: checkRangeBoundary(); break;
            // === P0: TiDB-Specific Index Features ===
            case 18: checkTiFlashVsTiKV(); break;
            case 19: checkExpressionIndex(); break;
            // === P3: New Metamorphic Strategies ===
            // DEPRECATED: case 20/21 checkICPConsistency() — not index-related (tests optimizer switch consistency)
            // case 20: checkICPConsistency(); break;
            // case 21: checkICPConsistency(); break;
            case 22: checkSQLSemanticEquivalence(); break;   // SQL semantic equivalence
            case 23: checkDeterministicIndexQuery(); break;  // Deterministic index query
            case 24: checkNullIndexHandling(); break;       // NULL index handling
            case 25: checkSubqueryIndex(); break;           // Subquery + Index
            case 26: checkIndexMergeEnhanced(); break;      // Enhanced Index Merge
            case 27: checkLooseIndexScan(); break;          // Loose Index Scan
            case 28: checkDMLIndexConsistency(); break;     // DML + Index Consistency
            case 29: checkGeneratedColumnIndex(); break;    // Generated Column + Index
            case 30: checkAggregateIndex(); break;          // Aggregate + Index
            case 31: checkDescIndexSort(); break;           // DESC Index Sort
            case 32: checkDropColumnIndex(); break;         // DROP COLUMN + Index
            case 33: checkCollationIndex(); break;          // Collation + Index
            case 34: checkImplicitTypeConversionIndex(); break; // Implicit Type Conversion + Index
            case 35: checkComplexIndexQuery(); break;           // Complex multi-index + deep expression query
            }

            // Statistics tracking
            trackMode(mode);
        } catch (NullPointerException e) {
            throw new IgnoreMeException();
        }
    }

    // ==================== P0: Data-Aware Value Sampling ====================

    // catch(Throwable) not catch(Exception): TiDB's Cascades planner throws AssertionError
    // (not Exception) from "ORDER BY RAND() LIMIT" on virtual generated columns — see
    // min_tidb_db67_virtual_col_cascades_bug.sql. Revert to catch(Exception) once fixed.
    private List<String> sampleColumnValues(String tableName, String colName, int limit) {
        try {
            String query = "SELECT " + colName + " FROM " + tableName
                    + " WHERE " + colName + " IS NOT NULL ORDER BY RAND() LIMIT " + limit + ";";
            return execInternal(query);
        } catch (Throwable e) {
            return null;
        }
    }

    // Numeric types returned as-is (JDBC provides unquoted numeric strings).
    // String/date types get single-quote wrapping with escaping to handle special chars.
    private String quoteValueForSQL(String rawValue, TiDBColumn col) {
        if (rawValue == null) return "NULL";
        String typeName = col.getType().toString().toUpperCase();
        if (typeName.contains("CHAR") || typeName.contains("TEXT") || typeName.contains("VARCHAR") || typeName.contains("BLOB")) {
            // Escape single quotes by doubling them, then wrap in single quotes
            return "'" + rawValue.replace("'", "''") + "'";
        }
        if (typeName.contains("DATE") || typeName.contains("TIME") || typeName.contains("TIMESTAMP")) {
            // Date/time values need single-quote wrapping for SQL
            return "'" + rawValue.replace("'", "''") + "'";
        }
        // Numeric and other types — return as-is (JDBC returns unquoted numeric strings)
        return rawValue;
    }

    // ==================== P0: Indexable Table/Column Helpers ====================

    // Prioritizes idx_t* tables (index-safe INT/VARCHAR only); falls back to tables
    // with at least 2 indexable (non-TEXT/BLOB/JSON) columns.
    private TiDBTable getRandomIndexableTable() {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return null;

        // First priority: tables whose names start with "idx_t" (index-friendly tables)
        List<TiDBTable> idxFriendlyTables = new ArrayList<>();
        for (TiDBTable t : tables) {
            if (t.getName().startsWith("idx_t") && !t.isView()) {
                idxFriendlyTables.add(t);
            }
        }
        if (!idxFriendlyTables.isEmpty()) {
            return Randomly.fromList(idxFriendlyTables);
        }

        // Second priority: any non-view table with at least 2 indexable columns
        List<TiDBTable> indexableTables = new ArrayList<>();
        for (TiDBTable t : tables) {
            if (!t.isView() && getIndexableColumns(t).size() >= 2) {
                indexableTables.add(t);
            }
        }
        if (!indexableTables.isEmpty()) {
            return Randomly.fromList(indexableTables);
        }

        return null;
    }

    private List<TiDBColumn> getIndexableColumns(TiDBTable table) {
        List<TiDBColumn> result = new ArrayList<>();
        for (TiDBColumn col : table.getColumns()) {
            String typeName = col.getType().toString().toUpperCase();
            if (!typeName.contains("TEXT") && !typeName.contains("BLOB") && !typeName.contains("JSON")) {
                result.add(col);
            }
        }
        return result;
    }

    // ==================== Mode 0: Create Index Consistency ====================
    private void checkCreateIndexConsistency() throws Exception {
        // Fix: select table first, generate query targeting that table,
        // then create index on the SAME table so the index actually affects the query.
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        String queryString = generateIndexAwareQuery(table);
        lastQueryString = "[CREATE_IDX] " + queryString;

        List<String> r1 = exec(queryString);
        if (r1 == null) return;

        try {
            SQLQueryAdapter createIndex = TiDBIndexGenerator.generateIndexForTable(globalState, table);
            globalState.executeStatement(createIndex);
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { return; }
        refreshSchema();

        List<String> r2 = exec(queryString);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_CREATE_INDEX");
    }

    // ==================== Mode 1: Drop Index Consistency ====================
    private void checkDropIndexConsistency() throws Exception {
        // Fix: select a table with indexes first, generate query targeting that table,
        // then drop an index from the SAME table so the drop actually affects the query.
        TiDBTable table = getRandomTableWithIndexes();
        if (table == null) return;

        TableIndex idxToDrop = null;
        for (TableIndex idx : table.getIndexes()) {
            if (!idx.getIndexName().equals("PRIMARY")) {
                idxToDrop = idx;
                break;
            }
        }
        if (idxToDrop == null) return;

        String tableName = table.getName();
        String queryString = generateIndexAwareQuery(table);
        lastQueryString = "[DROP_IDX] " + queryString;

        List<String> r1 = exec(queryString);
        if (r1 == null) return;

        try {
            ExpectedErrors dropErrors = new ExpectedErrors();
            dropErrors.add("Can't DROP");
            dropErrors.add("check that column/key exists");
            globalState.executeStatement(new SQLQueryAdapter(
                    "DROP INDEX " + idxToDrop.getIndexName() + " ON " + tableName + ";", dropErrors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { return; }
        // Schema-drift fix: re-read the live schema after DROP INDEX so that
        refreshSchema();

        List<String> r2 = exec(queryString);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_DROP_INDEX");
    }

    // ==================== Mode 2: USE_INDEX Hint ====================
    private void checkUseIndexHint() throws Exception {
        TiDBTable table = getRandomTableWithIndexes();
        if (table == null) return;
        TableIndex useIdx = Randomly.fromList(table.getIndexes());
        String idxName = useIdx.getIndexName();
        String tblName = table.getName();

        // P1#4 Fix: Generate WHERE condition targeting columns of the hinted index
        // so the hint is more likely to change the execution plan.
        List<TiDBColumn> hintIdxCols = getIndexColumnsFromSchema(table, idxName);
        String queryString;
        if (hintIdxCols != null && !hintIdxCols.isEmpty()) {
            queryString = generateQueryTargetingColumns(table, hintIdxCols);
        } else {
            queryString = generateIndexAwareQuery(table);
        }
        lastQueryString = "[USE_INDEX] " + queryString;

        String hintQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(hintQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        if (!compareQueries(queryString, hintQuery, "USE_INDEX", queryString)) return;
        if (lastCompareFiltered) { countStarFallback(queryString, hintQuery, "TIDB_USE_INDEX"); }
    }

    // ==================== Mode 3: IGNORE_INDEX Hint ====================
    private void checkIgnoreIndexHint() throws Exception {
        TiDBTable table = getRandomTableWithIndexes();
        if (table == null) return;
        List<TableIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) return;

        TableIndex ignoreIdx = Randomly.fromList(tableIndexes);
        String idxName = ignoreIdx.getIndexName();
        String tblName = table.getName();

        // P1#4 Fix: Generate WHERE condition targeting columns of the hinted index
        List<TiDBColumn> hintIdxCols = getIndexColumnsFromSchema(table, idxName);
        String queryString;
        if (hintIdxCols != null && !hintIdxCols.isEmpty()) {
            queryString = generateQueryTargetingColumns(table, hintIdxCols);
        } else {
            queryString = generateIndexAwareQuery(table);
        }
        lastQueryString = "[IGNORE_INDEX] " + queryString;

        String hintQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(hintQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        if (!compareQueries(queryString, hintQuery, "IGNORE_INDEX", queryString)) return;
        if (lastCompareFiltered) { countStarFallback(queryString, hintQuery, "TIDB_IGNORE_INDEX"); }
    }

    // ==================== Mode 4: HASH_JOIN vs MERGE_JOIN ====================
    private void checkHashJoinVsMergeJoin() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().size() < 2) return;

        String queryString = generateJoinQuery();
        if (queryString == null) return;
        lastQueryString = "[JOIN_STRATEGY] " + queryString;

        List<String> tableNames = schema.getDatabaseTables().stream()
                .map(t -> t.getName()).collect(Collectors.toList());
        if (tableNames.size() < 2) return;
        String t1 = tableNames.get(0);
        String t2 = tableNames.get(1);

        String hashQuery = "SELECT /*+ HASH_JOIN(" + t1 + ", " + t2 + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);
        String mergeQuery = "SELECT /*+ MERGE_JOIN(" + t1 + ", " + t2 + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(hashQuery);
        List<String> explainPlan2 = getExplainPlan(mergeQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(hashQuery);
        if (r1 == null) return;
        List<String> r2 = exec(mergeQuery);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_JOIN_STRATEGY");
    }

    // ==================== Mode 5: INDEX_MERGE vs Default ====================
    private void checkIndexMergeVsDefault() throws Exception {
        // Fix: select table first, generate query targeting that table,
        // then apply USE_INDEX_MERGE hint for the SAME table.
        TiDBTable table = getRandomTableWithIndexes();
        if (table == null) return;

        String tblName = table.getName();
        String queryString = generateIndexAwareQuery(table);
        lastQueryString = "[INDEX_MERGE] " + queryString;

        List<TableIndex> indexes = table.getIndexes();
        String idxList = indexes.stream().map(TableIndex::getIndexName).collect(Collectors.joining(", "));
        String mergeQuery = "SELECT /*+ USE_INDEX_MERGE(" + tblName + ", " + idxList + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(mergeQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        if (!compareQueries(queryString, mergeQuery, "INDEX_MERGE", queryString)) return;
    }

    // ==================== Mode 6: Aggregate with Index Hint ====================
    private void checkAggregateIndexHint() throws Exception {
        String queryString = generateSimpleAggregateQuery();
        if (queryString == null) return;
        lastQueryString = "[AGG_IDX] " + queryString;

        String hintQuery = "SELECT /*+ HASH_AGG() */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(hintQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        if (!compareQueries(queryString, hintQuery, "AGG_INDEX", queryString)) return;
    }

    // ==================== Mode 7: JOIN Index Selection (P4#7 enhanced) ====================
    private void checkJoinIndexSelection() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> allTables = schema.getDatabaseTables();
        if (allTables.size() < 2) return;

        // P4#7: Choose between old-style random JOIN and new index-aware JOIN
        int joinVariant = Randomly.fromOptions(0, 1, 2);
        switch (joinVariant) {
        case 0:
            checkJoinIndexSelectionLegacy(allTables);
            break;
        case 1:
            checkJoinIndexSelectionIndexAware(allTables);
            break;
        case 2:
            checkJoinIndexSelectionMergeVsINL(allTables);
            break;
        }
    }

    // Fix: extracts actual table names to ensure INL_JOIN hint references the tables
    // present in the query (not some other table from the schema).
    private void checkJoinIndexSelectionLegacy(List<TiDBTable> allTables) throws Exception {
        if (allTables.size() < 2) return;
        // Fix: pick two tables first, build the query from them, use their names in hint
        List<TiDBTable> shuffled = new ArrayList<>(allTables);
        Collections.shuffle(shuffled);
        TiDBTable t1 = shuffled.get(0);
        TiDBTable t2 = shuffled.get(1);

        String queryString = generateIndexAwareJoinQuery(t1, t2);
        if (queryString == null) return;
        lastQueryString = "[JOIN_IDX] " + queryString;

        String inlQuery = "SELECT /*+ INL_JOIN(" + t1.getName() + ", " + t2.getName() + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(inlQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(queryString);
        if (r1 == null) return;
        List<String> r2 = exec(inlQuery);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_JOIN_INDEX");
    }

    // Tests optimizer index usage for both JOIN ON conditions and WHERE filter conditions.
    private void checkJoinIndexSelectionIndexAware(List<TiDBTable> allTables) throws Exception {
        // Pick two tables with indexes
        List<TiDBTable> tablesWithIndexes = new ArrayList<>();
        for (TiDBTable t : allTables) {
            if (!t.getIndexes().isEmpty()) tablesWithIndexes.add(t);
        }
        if (tablesWithIndexes.size() < 2) {
            // Fall back to any two tables
            tablesWithIndexes = allTables;
        }
        if (tablesWithIndexes.size() < 2) return;

        Collections.shuffle(tablesWithIndexes);
        TiDBTable t1 = tablesWithIndexes.get(0);
        TiDBTable t2 = tablesWithIndexes.get(1);
        List<TiDBColumn> cols1 = t1.getColumns();
        List<TiDBColumn> cols2 = t2.getColumns();
        if (cols1.isEmpty() || cols2.isEmpty()) return;

        // Build index-friendly JOIN query
        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        // Use qualified column names to avoid ambiguity
        int numCols1 = Math.min(cols1.size(), Randomly.smallNumber() + 1);
        List<TiDBColumn> subset1 = Randomly.extractNrRandomColumns(cols1, numCols1);
        for (int i = 0; i < subset1.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(t1.getName()).append(".").append(subset1.get(i).getName());
        }
        sb.append(" FROM ").append(t1.getName());

        // JOIN with index-friendly ON condition
        String joinType = Randomly.fromOptions("JOIN", "INNER JOIN", "LEFT JOIN");
        sb.append(" ").append(joinType).append(" ").append(t2.getName());

        // Build ON condition preferring indexed columns
        List<TiDBColumn> idxCols1 = getIndexedColumnsForTable(t1);
        List<TiDBColumn> idxCols2 = getIndexedColumnsForTable(t2);
        TiDBColumn onCol1 = !idxCols1.isEmpty() && Randomly.getBoolean() ? Randomly.fromList(idxCols1) : Randomly.fromList(cols1);
        TiDBColumn onCol2 = !idxCols2.isEmpty() && Randomly.getBoolean() ? Randomly.fromList(idxCols2) : Randomly.fromList(cols2);
        sb.append(" ON ").append(t1.getName()).append(".").append(onCol1.getName());
        sb.append(" = ").append(t2.getName()).append(".").append(onCol2.getName());

        // WHERE condition using sampled values from t1
        if (Randomly.getBoolean()) {
            TiDBColumn whereCol = Randomly.fromList(cols1);
            List<String> sampled = sampleColumnValues(t1.getName(), whereCol.getName(), 5);
            sb.append(" WHERE ");
            if (sampled != null && !sampled.isEmpty()) {
                String op = Randomly.fromOptions("=", ">=", "<=");
                sb.append(t1.getName()).append(".").append(whereCol.getName()).append(" ").append(op).append(" ");
                sb.append(quoteValueForSQL(sampled.get(0), whereCol));
            } else {
                sb.append(t1.getName()).append(".").append(whereCol.getName()).append(" IS NOT NULL");
            }
            // Optionally add WHERE on t2 as well (tests multi-table index usage)
            if (Randomly.getBoolean() && !cols2.isEmpty()) {
                TiDBColumn whereCol2 = Randomly.fromList(cols2);
                List<String> sampled2 = sampleColumnValues(t2.getName(), whereCol2.getName(), 5);
                sb.append(" AND ");
                if (sampled2 != null && !sampled2.isEmpty()) {
                    sb.append(t2.getName()).append(".").append(whereCol2.getName()).append(" >= ");
                    sb.append(quoteValueForSQL(sampled2.get(0), whereCol2));
                } else {
                    sb.append(t2.getName()).append(".").append(whereCol2.getName()).append(" IS NOT NULL");
                }
            }
        }

        // ORDER BY + LIMIT for deterministic comparison
        TiDBColumn orderCol = Randomly.fromList(cols1);
        sb.append(" ORDER BY ").append(t1.getName()).append(".").append(orderCol.getName());
        sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1);
        sb.append(";");
        String queryString = sb.toString();
        lastQueryString = "[JOIN_IDX_AWARE] " + queryString;

        // Compare INL_JOIN (index nested loop) vs default plan
        String inlQuery = "SELECT /*+ INL_JOIN(" + t1.getName() + ", " + t2.getName() + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(inlQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(queryString);
        if (r1 == null) return;
        List<String> r2 = exec(inlQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_JOIN_IDX_AWARE");
        if (lastCompareFiltered) { countStarFallback(queryString, inlQuery, "TIDB_JOIN_IDX_AWARE"); }
    }

    // SortMergeJoin and IndexNestedLoopJoin handle duplicate keys and NULLs differently —
    // comparing them exposes join-related index bugs.
    private void checkJoinIndexSelectionMergeVsINL(List<TiDBTable> allTables) throws Exception {
        if (allTables.size() < 2) return;
        List<TiDBTable> shuffled = new ArrayList<>(allTables);
        Collections.shuffle(shuffled);
        TiDBTable t1 = shuffled.get(0);
        TiDBTable t2 = shuffled.get(1);
        List<TiDBColumn> cols1 = t1.getColumns();
        List<TiDBColumn> cols2 = t2.getColumns();
        if (cols1.isEmpty() || cols2.isEmpty()) return;

        // Build a simple JOIN query with COUNT(*) for deterministic comparison
        TiDBColumn joinCol1 = Randomly.fromList(cols1);
        TiDBColumn joinCol2 = Randomly.fromList(cols2);

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT COUNT(*) FROM ").append(t1.getName());
        sb.append(" JOIN ").append(t2.getName());
        sb.append(" ON ").append(t1.getName()).append(".").append(joinCol1.getName());
        sb.append(" = ").append(t2.getName()).append(".").append(joinCol2.getName());

        // Add WHERE condition with sampled values
        if (Randomly.getBoolean()) {
            List<String> sampled = sampleColumnValues(t1.getName(), joinCol1.getName(), 3);
            sb.append(" WHERE ");
            if (sampled != null && !sampled.isEmpty()) {
                sb.append(t1.getName()).append(".").append(joinCol1.getName());
                sb.append(" >= ").append(quoteValueForSQL(sampled.get(0), joinCol1));
            } else {
                sb.append(t1.getName()).append(".").append(joinCol1.getName()).append(" IS NOT NULL");
            }
        }
        sb.append(";");
        String queryString = sb.toString();
        lastQueryString = "[JOIN_MERGE_VS_INL] " + queryString;

        // Compare MERGE_JOIN vs INL_JOIN
        String mergeQuery = "SELECT /*+ MERGE_JOIN(" + t1.getName() + ", " + t2.getName() + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);
        String inlQuery = "SELECT /*+ INL_JOIN(" + t1.getName() + ", " + t2.getName() + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> explainPlan1 = getExplainPlan(mergeQuery);
        List<String> explainPlan2 = getExplainPlan(inlQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(mergeQuery);
        if (r1 == null) return;
        List<String> r2 = exec(inlQuery);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_JOIN_MERGE_VS_INL");
    }

    // ==================== Mode 8: Multi-Index Create ====================
    private void checkMultiIndexCreate() throws Exception {
        // Fix: select table first, generate query targeting that table,
        // then create indexes on the SAME table so they affect the query.
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;

        String queryString = generateIndexAwareQuery(table);
        lastQueryString = "[MULTI_IDX] " + queryString;

        List<String> r1 = exec(queryString);
        if (r1 == null) return;

        // Index deduplication: avoid creating too many duplicate indexes
        int numIndexes = Randomly.smallNumber() + 1;
        int created = 0;
        for (int i = 0; i < numIndexes * 3 && created < numIndexes; i++) {
            try {
                Set<String> currentSigs = collectExistingIndexSignatures();
                if (currentSigs.size() >= 10) break; // Don't over-create indexes
                SQLQueryAdapter createIndex = TiDBIndexGenerator.generateIndexForTable(globalState, table);
                globalState.executeStatement(createIndex);
                created++;
            } catch (Exception e) { }
        }
        tablesNeedingAnalyze.add(table.getName());

        List<String> r2 = exec(queryString);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_MULTI_INDEX");
    }

    // ==================== Mode 9: ORDER BY Index Sort ====================
    private void checkOrderByIndexSort() throws Exception {
        String queryString = generateOrderedQuery();
        if (queryString == null) return;
        lastQueryString = "[ORDERBY_IDX] " + queryString;

        String streamQuery = "SELECT /*+ STREAM_AGG() */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(streamQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        if (!compareQueries(queryString, streamQuery, "ORDERBY_IDX", queryString)) return;
    }

    // ==================== Mode 10: Hint Consistency ====================
    private void checkHintConsistency() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        TiDBTable table = Randomly.fromList(tables);
        List<TableIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) return;

        TableIndex hintIdx = Randomly.fromList(tableIndexes);
        String idxName = hintIdx.getIndexName();
        String tblName = table.getName();

        String queryString = generateQuery();
        lastQueryString = "[HINT_CONSISTENCY] " + queryString;

        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_HINT_CONSISTENCY");
    }

    // ==================== Mode 11: STREAM_AGG vs HASH_AGG ====================
    private void checkStreamAggVsHashAgg() throws Exception {
        String queryString = generateSimpleAggregateQuery();
        if (queryString == null) return;
        lastQueryString = "[AGG_STRATEGY] " + queryString;

        String streamQuery = "SELECT /*+ STREAM_AGG() */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);
        String hashQuery = "SELECT /*+ HASH_AGG() */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(streamQuery);
        List<String> explainPlan2 = getExplainPlan(hashQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(streamQuery);
        if (r1 == null) return;
        List<String> r2 = exec(hashQuery);
        if (r2 == null) return;

        assertResultSorted(r1, r2, queryString, "TIDB_AGG_STRATEGY");
    }

    // ==================== Mode 12: ADMIN CHECK TABLE ====================

    // Targets TiDB bugs: #61612 (ADMIN CHECK TABLE false success),
    // #60339 (ADD UNIQUE INDEX data inconsistency).
    private void checkAdminCheckTable() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Filter out views — ADMIN CHECK TABLE and ANALYZE TABLE don't work on views
        List<TiDBTable> nonViewTables = new ArrayList<>();
        for (TiDBTable t : tables) {
            if (!t.isView()) nonViewTables.add(t);
        }
        if (nonViewTables.isEmpty()) return;

        TiDBTable table = Randomly.fromList(nonViewTables);
        String tblName = table.getName();

        // First, create some indexes to stress-test
        try {
            SQLQueryAdapter createIndex = TiDBIndexGenerator.getQuery(globalState);
            globalState.executeStatement(createIndex);
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { }

        // Run ADMIN CHECK TABLE (TiDB-specific, more thorough than CHECK TABLE)
        String checkQuery = "ADMIN CHECK TABLE " + tblName + ";";
        lastQueryString = "[ADMIN_CHECK] " + checkQuery;

        try {
            globalState.executeStatement(new SQLQueryAdapter(checkQuery, errors, true));
        } catch (Exception e) {
            // ADMIN CHECK TABLE failure = data inconsistency = BUG
            String msg = e.getMessage();
            if (msg != null && !msg.contains("doesn't exist") && !msg.contains("does not exist")) {
                throw new AssertionError("TIDB_ADMIN_CHECK: ADMIN CHECK TABLE failed!\n"
                        + "Table: " + tblName + "\nError: " + msg);
            }
            return;
        }

        // NOTE: Removed legacy "compare COUNT(*) before/after ANALYZE" block — it was a false-positive source.
    }

    // ==================== Mode 13: UNIQUE INDEX Consistency ====================

    // Targets TiDB bugs: #60339 (ADD UNIQUE INDEX data inconsistency),
    // #61255 (multi-index data inconsistency).
    private void checkUniqueIndexConsistency() throws Exception {
        // P0: Use indexable table (prioritize idx_t* tables, filter out BLOB/TEXT)
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;

        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        // P0: Only use indexable (non-TEXT/BLOB/JSON) columns as candidates
        // Find a non-PK column for the unique index
        List<TiDBColumn> candidates = new ArrayList<>();
        for (TiDBColumn col : columns) {
            String typeName = col.getType().toString().toUpperCase();
            if (!col.isPrimaryKey() && !typeName.contains("TEXT") && !typeName.contains("BLOB") && !typeName.contains("JSON")) {
                candidates.add(col);
            }
        }
        if (candidates.isEmpty()) return;

        TiDBColumn col = Randomly.fromList(candidates);
        String tblName = table.getName();
        String colName = col.getName();

        // Pre-check: skip if column has duplicate values (thorough fix for false positives)
        // This avoids even attempting CREATE UNIQUE INDEX when we know it will fail.
        try {
            List<String> dupCheck = execInternal(
                    "SELECT " + colName + " FROM " + tblName
                    + " WHERE " + colName + " IS NOT NULL GROUP BY " + colName
                    + " HAVING COUNT(*) > 1 LIMIT 1;");
            if (dupCheck != null && !dupCheck.isEmpty()) {
                return; // Duplicates exist, UNIQUE index will fail — skip
            }
        } catch (Exception e) {
            return; // Safety: if check fails, skip
        }

        // Count rows before
        String countQuery = "SELECT COUNT(*) FROM " + tblName + ";";
        List<String> r1 = exec(countQuery);
        if (r1 == null) return;

        // Create UNIQUE INDEX — use local ExpectedErrors with "Duplicate entry" as safety net
        // (even after pre-check, race conditions or concurrent inserts may introduce duplicates)
        String idxName = "uniq_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            ExpectedErrors uniqueErrors = new ExpectedErrors();
            uniqueErrors.add("Duplicate entry");
            uniqueErrors.add("Duplicate key name");
            uniqueErrors.add("index already exist");
            uniqueErrors.add("Specified key was too long");
            uniqueErrors.add("can't index column");
            uniqueErrors.add("BLOB or TEXT");
            uniqueErrors.add("Too many keys specified");
            uniqueErrors.add("doesn't exist");
            uniqueErrors.add("does not exist");
            uniqueErrors.add("Information schema is changed");
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE UNIQUE INDEX " + idxName + " ON " + tblName + " (" + colName + ");",
                    uniqueErrors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Throwable e) {
            // Use catch(Throwable) because SQLQueryAdapter.checkException() throws AssertionError
            // (which is NOT a subclass of Exception) when the error message is not in ExpectedErrors.
            // UNIQUE constraint violation or other DDL errors are expected — skip.
            return;
        }

        // Count rows after — should be the same
        List<String> r2 = exec(countQuery);
        if (r2 == null) return;
        assertResultSorted(r1, r2, countQuery, "TIDB_UNIQUE_IDX_COUNT");

        // Compare query with/without USE_INDEX hint
        String queryDefault = "SELECT " + colName + " FROM " + tblName
                + " WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " LIMIT 100;";
        String queryForced = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ " + colName
                + " FROM " + tblName + " WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " LIMIT 100;";

        lastQueryString = "[UNIQUE_IDX] " + queryDefault;

        List<String> r3 = exec(queryDefault);
        if (r3 == null) return;
        List<String> r4 = exec(queryForced);
        if (r4 == null) return;

        assertResultStrict(r3, r4, queryDefault, "TIDB_UNIQUE_IDX");
    }

    // ==================== Data Population (Priority 3) ====================

    private void ensureSufficientData() {
        if (dataPopulated) return;
        dataPopulated = true;

        // === P1: Create index-friendly tables for better index testing ===
        createIndexFriendlyTables();

        try {
            for (TiDBTable table : globalState.getSchema().getDatabaseTables()) {
                if (table.isView()) continue;
                List<TiDBColumn> columns = table.getColumns();
                if (columns.isEmpty()) continue;

                // Check current row count
                List<String> countResult = execInternal("SELECT COUNT(*) FROM " + table.getName() + ";");
                int currentRows = 0;
                if (countResult != null && !countResult.isEmpty()) {
                    try { currentRows = Integer.parseInt(countResult.get(0).trim()); } catch (NumberFormatException e) { }
                }

                int targetRows = 500;
                if (currentRows >= targetRows / 2) continue; // Already enough data

                // Build column list for INSERT
                StringBuilder colList = new StringBuilder();
                for (int i = 0; i < columns.size(); i++) {
                    if (i > 0) colList.append(", ");
                    colList.append(columns.get(i).getName());
                }

                // Build expected errors for data population inserts
                ExpectedErrors insertErrors = new ExpectedErrors();
                TiDBErrors.addInsertErrors(insertErrors);

                // Batch insert rows with random values (use INSERT IGNORE to skip constraint violations)
                int batchSize = Math.min(50, targetRows - currentRows);
                for (int batch = 0; batch < batchSize; batch++) {
                    StringBuilder sb = new StringBuilder();
                    sb.append("INSERT IGNORE INTO ").append(table.getName()).append("(").append(colList).append(") VALUES (");
                    for (int i = 0; i < columns.size(); i++) {
                        if (i > 0) sb.append(", ");
                        sb.append(generateRandomValueForColumn(columns.get(i)));
                    }
                    sb.append(");");
                    try {
                        // Log INSERT for reproducibility
                        log(sb.toString());
                        globalState.executeStatement(new SQLQueryAdapter(sb.toString(), insertErrors, true));
                    } catch (Exception e) {
                        // Ignore individual insert failures
                    }
                }

                // Also use INSERT ... SELECT to multiply existing data
                if (currentRows > 0) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(
                                "INSERT IGNORE INTO " + table.getName() + "(" + colList + ") SELECT "
                                + colList + " FROM " + table.getName() + " LIMIT 200;", insertErrors, true));
                    } catch (Exception e) { }
                }
            }
            analyzeAllTables();
        } catch (Exception e) {
            // Data population is best-effort
        }
    }

    private String generateRandomValueForColumn(TiDBColumn col) {
        String typeName = col.getType().toString().toUpperCase();
        if (typeName.contains("BOOL")) {
            // BOOL only accepts 0/1 (or false/true)
            return Randomly.fromOptions("0", "1", "true", "false");
        } else if (typeName.contains("INT")) {
            // Use small non-negative values to work with both SIGNED and UNSIGNED
            return String.valueOf(Math.abs(globalState.getRandomly().getInteger() % 255));
        } else if (typeName.contains("FLOAT") || typeName.contains("DOUBLE") || typeName.contains("DECIMAL") || typeName.contains("NUMERIC") || typeName.contains("REAL")) {
            // Use small non-negative doubles to avoid UNSIGNED out-of-range
            double val = globalState.getRandomly().getDouble();
            // Guard against Infinity/NaN from getDouble()
            if (!Double.isFinite(val)) {
                val = globalState.getRandomly().getInteger() % 1000;
            }
            val = Math.abs(val) * 1000.0;
            // Guard against Infinity from multiplication overflow
            if (!Double.isFinite(val)) {
                val = 0.0;
            }
            return String.valueOf(val);
        } else if (typeName.contains("CHAR")) {
            // CHAR(1) by default — generate only a single safe character
            String safeChars = "abcdefghijklmnopqrstuvwxyz0123456789";
            return "'" + safeChars.charAt((int)(Math.abs(globalState.getRandomly().getInteger()) % safeChars.length())) + "'";
        } else if (typeName.contains("TEXT") || typeName.contains("VARCHAR") || typeName.contains("BLOB")) {
            String s = globalState.getRandomly().getString().replace("'", "''").replace("\\", "\\\\");
            return "'" + s.substring(0, Math.min(20, s.length())) + "'";
        } else if (typeName.contains("DATE")) {
            // DATE type — generate random valid date string
            return "'" + generateRandomDateString() + "'";
        } else if (typeName.contains("TIME") || typeName.contains("TIMESTAMP")) {
            // DATETIME/TIMESTAMP/TIME — use random date with optional time component
            return "'" + generateRandomDateString() + " " + generateRandomTimeString() + "'";
        } else {
            return "NULL";
        }
    }

    private static String generateRandomDateString() {
        int year = 2000 + (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % 50); // 2000-2049
        int month = 1 + (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % 12);
        int maxDay;
        switch (month) {
        case 2: maxDay = java.time.Year.of(year).isLeap() ? 29 : 28; break;
        case 4: case 6: case 9: case 11: maxDay = 30; break;
        default: maxDay = 31; break;
        }
        int day = 1 + (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % maxDay);
        return String.format("%04d-%02d-%02d", year, month, day);
    }

    private static String generateRandomTimeString() {
        int hour = (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % 24);
        int minute = (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % 60);
        int second = (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % 60);
        return String.format("%02d:%02d:%02d", hour, minute, second);
    }

    private void log(String queryString) {
        if (globalState.getOptions().logEachSelect()) {
            globalState.getLogger().writeCurrent(queryString);
        }
    }

    private List<String> execInternal(String query) {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(query, errors, globalState, " ||| ");
        } catch (Exception e) {
            return null;
        }
    }

    // ==================== AST-Based Query Generation (Priority 1) ====================

    // Falls back to simple string-based query if AST generation fails.
    private String generateComplexQuery() {
        TiDBSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return "SELECT 1;";

        try {
            TiDBTable table = Randomly.fromList(schema.getDatabaseTables());
            List<TiDBColumn> columns = table.getColumns();
            if (columns.isEmpty()) return "SELECT 1;";

            TiDBExpressionGenerator gen = new TiDBExpressionGenerator(globalState).setColumns(columns);

            TiDBSelect select = new TiDBSelect();

            // Fetch columns — mix of column references and generated expressions
            List<TiDBExpression> fetchColumns = new ArrayList<>();
            if (Randomly.getBooleanWithRatherLowProbability()) {
                fetchColumns.add(TiDBConstant.createIntConstant(1));
            } else {
                List<TiDBColumn> subset = Randomly.nonEmptySubset(columns);
                for (TiDBColumn col : subset) {
                    if (Randomly.getBoolean()) {
                        fetchColumns.add(new TiDBColumnReference(col));
                    } else {
                        fetchColumns.add(gen.generateExpression());
                    }
                }
            }
            select.setFetchColumns(fetchColumns);

            // FROM
            List<TiDBExpression> fromList = new ArrayList<>();
            fromList.add(new TiDBTableReference(table));
            select.setFromList(fromList);

            // WHERE — 40% chance: use index-aware condition; 60%: use AST expression
            if (Randomly.fromOptions(true, true, false, false, false)) {
                TiDBExpression indexWhere = generateIndexAwareWhere(table, columns);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                } else {
                    select.setWhereClause(gen.generateExpression());
                }
            }

            // GROUP BY
            if (Randomly.getBooleanWithRatherLowProbability()) {
                List<TiDBExpression> groupByExprs = new ArrayList<>();
                for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
                    groupByExprs.add(gen.generateExpression());
                }
                select.setGroupByExpressions(groupByExprs);
                if (Randomly.getBoolean()) {
                    select.setHavingClause(gen.generateExpression());
                }
            }

            // ORDER BY
            if (Randomly.getBoolean()) {
                select.setOrderByClauses(gen.generateOrderBys());
            }

            // LIMIT
            if (Randomly.getBoolean()) {
                select.setLimitClause(TiDBConstant.createIntConstant(
                        Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));
            }

            return TiDBVisitor.asString(select) + ";";
        } catch (Exception e) {
            return null;
        }
    }

    // ==================== Index-Aware WHERE Generation (Priority 2) ====================

    // Queries information_schema.STATISTICS (not the schema model) to get actual
    // non-PRIMARY indexed columns, so hints are more likely to change the plan.
    private List<TiDBColumn> getIndexedColumnsForTable(TiDBTable table) {
        List<TiDBColumn> indexedCols = new ArrayList<>();
        try {
            String query = "SELECT DISTINCT COLUMN_NAME FROM information_schema.STATISTICS WHERE TABLE_SCHEMA = DATABASE()"
                    + " AND TABLE_NAME = '" + table.getName() + "' AND INDEX_NAME != 'PRIMARY' ORDER BY COLUMN_NAME;";
            List<String> result = execInternal(query);
            if (result != null) {
                for (String colName : result) {
                    String trimmed = colName.trim();
                    for (TiDBColumn col : table.getColumns()) {
                        if (col.getName().equals(trimmed)) {
                            if (!indexedCols.contains(col)) {
                                indexedCols.add(col);
                            }
                            break;
                        }
                    }
                }
            }
        } catch (Exception e) { }
        return indexedCols;
    }

    // Groups columns by composite index from information_schema, ordered by SEQ_IN_INDEX.
    private List<List<TiDBColumn>> getCompositeIndexGroups(TiDBTable table) {
        Map<String, List<TiDBColumn>> indexGroups = new java.util.LinkedHashMap<>();
        try {
            String query = "SELECT INDEX_NAME, COLUMN_NAME, SEQ_IN_INDEX FROM information_schema.STATISTICS"
                    + " WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + table.getName() + "'"
                    + " AND INDEX_NAME != 'PRIMARY' ORDER BY INDEX_NAME, SEQ_IN_INDEX;";
            // Use a raw query to get ordered results
            try (java.sql.Statement stmt = globalState.getConnection().createStatement();
                 java.sql.ResultSet rs = stmt.executeQuery(query)) {
                while (rs.next()) {
                    String idxName = rs.getString("INDEX_NAME");
                    String colName = rs.getString("COLUMN_NAME");
                    for (TiDBColumn col : table.getColumns()) {
                        if (col.getName().equals(colName)) {
                            indexGroups.computeIfAbsent(idxName, k -> new ArrayList<>()).add(col);
                            break;
                        }
                    }
                }
            }
        } catch (Exception e) { }
        List<List<TiDBColumn>> compositeGroups = new ArrayList<>();
        for (List<TiDBColumn> group : indexGroups.values()) {
            if (group.size() >= 2) {
                compositeGroups.add(group);
            }
        }
        return compositeGroups;
    }

    // Strategies: equality, range, IN list, multi-column, composite prefix (≤4 cols), index merge.
    // Reads actual indexed columns via information_schema so conditions hit real index paths.
    private TiDBExpression generateIndexAwareWhere(TiDBTable table, List<TiDBColumn> columns) {
        if (columns.isEmpty()) return null;

        // P0: Collect index information for smart column selection
        List<TiDBColumn> indexedCols = getIndexedColumnsForTable(table);
        List<List<TiDBColumn>> compositeIdxGroups = getCompositeIndexGroups(table);

        // Choose column — prefer indexed columns 70% of the time when available
        TiDBColumn col;
        if (!indexedCols.isEmpty() && Randomly.getBoolean()) {
            col = Randomly.fromList(indexedCols);
        } else {
            col = Randomly.fromList(columns);
        }
        TiDBExpression colRef = new TiDBColumnReference(col);

        // Choose strategy — more strategies when composite indexes exist
        int maxStrategy = !compositeIdxGroups.isEmpty() ? 7 : 5;
        int strategy = globalState.getRandomly().getInteger(0, maxStrategy);
        switch (strategy) {
            case 0: {
                // Equality: col = value (triggers Index Seek) — use sampled data
                return new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef,
                        generateDataAwareConstant(table, col), idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.EQUALS);
            }
            case 1: {
                // Range: col >= x AND col <= y (triggers Index Range Scan) — use sampled data
                TiDBConstant low = generateDataAwareConstant(table, col);
                TiDBConstant high = generateDataAwareConstant(table, col);
                TiDBExpression gte = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef, low,
                        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER_EQUALS);
                TiDBExpression lte = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef, high,
                        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER_EQUALS);
                return new idxdiff.tidb.ast.TiDBBinaryLogicalOperation(gte, lte,
                        idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator.AND);
            }
            case 2: {
                // Greater/Less: col > value or col < value — use sampled data
                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator op =
                        Randomly.fromOptions(
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER,
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER,
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER_EQUALS,
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER_EQUALS);
                return new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef, generateDataAwareConstant(table, col), op);
            }
            case 3: {
                // IS NOT NULL + another condition (covers more rows while still using index)
                TiDBExpression notNull = new idxdiff.tidb.ast.TiDBUnaryPostfixOperation(colRef,
                        idxdiff.tidb.ast.TiDBUnaryPostfixOperation.TiDBUnaryPostfixOperator.IS_NOT_NULL);
                TiDBExpression extra = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef,
                        generateDataAwareConstant(table, col),
                        Randomly.fromOptions(
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER,
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER));
                return new idxdiff.tidb.ast.TiDBBinaryLogicalOperation(notNull, extra,
                        idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator.AND);
            }
            case 4: {
                // Multi-column condition: col1 = v1 AND col2 > v2 (tests composite index)
                if (columns.size() < 2) return null;
                TiDBColumn col2;
                if (!indexedCols.isEmpty() && Randomly.getBoolean()) {
                    col2 = Randomly.fromList(indexedCols);
                } else {
                    col2 = Randomly.fromList(columns);
                }
                TiDBExpression eq = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef,
                        generateTypeAwareConstant(col),
                        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.EQUALS);
                TiDBExpression range = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(
                        new TiDBColumnReference(col2), generateTypeAwareConstant(col2),
                        Randomly.fromOptions(
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER,
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER));
                return new idxdiff.tidb.ast.TiDBBinaryLogicalOperation(eq, range,
                        idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator.AND);
            }
            case 5: {
                // P0: Composite index prefix condition: idx_col0 = v0 AND idx_col1 > v1
                if (compositeIdxGroups.isEmpty()) return null;
                List<TiDBColumn> idxCols = Randomly.fromList(compositeIdxGroups);
                int prefixLen = Math.min(idxCols.size(), globalState.getRandomly().getInteger(1, 4));
                TiDBExpression combined = null;
                for (int i = 0; i < prefixLen; i++) {
                    TiDBColumn ic = idxCols.get(i);
                    TiDBExpression ref = new TiDBColumnReference(ic);
                    TiDBExpression cond;
                    if (i == 0) {
                        // First column: equality for best selectivity
                        cond = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(ref,
                                generateTypeAwareConstant(ic),
                                idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.EQUALS);
                    } else {
                        // Subsequent columns: range
                        cond = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(ref,
                                generateTypeAwareConstant(ic),
                                Randomly.fromOptions(
                                        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER,
                                        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER_EQUALS,
                                        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.EQUALS));
                    }
                    combined = (combined == null) ? cond
                            : new idxdiff.tidb.ast.TiDBBinaryLogicalOperation(combined, cond,
                                    idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator.AND);
                }
                return combined;
            }
            case 6: {
                // P0: Index merge — OR across different indexed columns
                if (indexedCols.size() < 2) return null;
                List<TiDBColumn> mergeCols = Randomly.nonEmptySubset(indexedCols);
                if (mergeCols.size() < 2) mergeCols = indexedCols.subList(0, Math.min(2, indexedCols.size()));
                TiDBExpression combined = null;
                for (TiDBColumn mc : mergeCols) {
                    TiDBExpression ref = new TiDBColumnReference(mc);
                    TiDBExpression cond = new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(ref,
                            generateTypeAwareConstant(mc),
                            Randomly.fromOptions(
                                    idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.EQUALS,
                                    idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER));
                    combined = (combined == null) ? cond
                            : new idxdiff.tidb.ast.TiDBBinaryLogicalOperation(combined, cond,
                                    idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator.OR);
                }
                return combined;
            }
            default: return null;
        }
    }

    private TiDBConstant generateTypeAwareConstant(TiDBColumn col) {
        String typeName = col.getType().toString().toUpperCase();
        Randomly r = globalState.getRandomly();
        if (typeName.contains("INT")) {
            return TiDBConstant.createIntConstant(r.getInteger() % 100);
        } else if (typeName.contains("CHAR") || typeName.contains("TEXT") || typeName.contains("VARCHAR")) {
            return TiDBConstant.createStringConstant(r.getString());
        } else if (typeName.contains("FLOAT") || typeName.contains("DOUBLE") || typeName.contains("DECIMAL") || typeName.contains("REAL")) {
            return TiDBConstant.createIntConstant(r.getInteger()); // use int as approximate decimal
        } else {
            return generateRandomConstant(); // fallback
        }
    }

    // Tries to sample real values from the table (60% chance); falls back to random.
    // Sampling real values significantly improves query hit rate for index testing.
    private TiDBConstant generateDataAwareConstant(TiDBTable table, TiDBColumn col) {
        // 60% chance: try to use a sampled value from actual table data
        if (!Randomly.getBooleanWithRatherLowProbability()) {
            try {
                List<String> sampled = sampleColumnValues(table.getName(), col.getName(), 5);
                if (sampled != null && !sampled.isEmpty()) {
                    String rawVal = Randomly.fromList(sampled).trim();
                    return parseSampledValueToConstant(rawVal, col);
                }
            } catch (Exception e) { }
        }
        return generateTypeAwareConstant(col);
    }

    private TiDBConstant parseSampledValueToConstant(String rawVal, TiDBColumn col) {
        String typeName = col.getType().toString().toUpperCase();
        if (typeName.contains("INT")) {
            try {
                // Strip any quotes just in case
                String cleaned = rawVal.replace("'", "").trim();
                return TiDBConstant.createIntConstant(Integer.parseInt(cleaned));
            } catch (NumberFormatException e) {
                return generateTypeAwareConstant(col);
            }
        } else if (typeName.contains("CHAR") || typeName.contains("TEXT") || typeName.contains("VARCHAR")) {
            // Strip surrounding quotes from executeQuery output
            String cleaned = rawVal;
            if (cleaned.startsWith("'") && cleaned.endsWith("'")) {
                cleaned = cleaned.substring(1, cleaned.length() - 1);
            }
            return TiDBConstant.createStringConstant(cleaned);
        } else if (typeName.contains("FLOAT") || typeName.contains("DOUBLE") || typeName.contains("DECIMAL") || typeName.contains("REAL")) {
            try {
                String cleaned = rawVal.replace("'", "").trim();
                return TiDBConstant.createIntConstant((int) Double.parseDouble(cleaned));
            } catch (NumberFormatException e) {
                return generateTypeAwareConstant(col);
            }
        }
        return generateTypeAwareConstant(col);
    }

    private TiDBConstant generateRandomConstant() {
        switch (Randomly.fromOptions(0, 1, 2)) {
            case 0: return TiDBConstant.createIntConstant(globalState.getRandomly().getInteger() % 100);
            case 1: return TiDBConstant.createStringConstant(globalState.getRandomly().getString());
            default: return TiDBConstant.createIntConstant(globalState.getRandomly().getInteger());
        }
    }

    // ==================== P1#4: Query Generation Targeting Specific Index Columns ====================

    // Mode 2/3 fix: WHERE targets the hinted index's columns so USE_INDEX/IGNORE_INDEX
    // is more likely to change the execution plan.
    private String generateQueryTargetingColumns(TiDBTable table, List<TiDBColumn> targetCols) {
        String tblName = table.getName();
        List<TiDBColumn> allCols = table.getColumns();

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        int numCols = Math.min(allCols.size(), Randomly.smallNumber() + 1);
        List<TiDBColumn> selectSubset = Randomly.extractNrRandomColumns(allCols, numCols);
        for (int i = 0; i < selectSubset.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(selectSubset.get(i).getName());
        }
        sb.append(" FROM ").append(tblName);

        // WHERE: target the first column of the index (most selective for optimizer)
        sb.append(" WHERE ");
        TiDBColumn whereCol = targetCols.get(0);
        List<String> sampled = sampleColumnValues(tblName, whereCol.getName(), 5);
        if (sampled != null && !sampled.isEmpty()) {
            String op = Randomly.fromOptions("=", ">=", "<=", ">");
            sb.append(whereCol.getName()).append(" ").append(op).append(" ");
            sb.append(quoteValueForSQL(sampled.get(0), whereCol));
        } else {
            sb.append(whereCol.getName()).append(" IS NOT NULL");
        }

        // If composite index, add condition on second column too
        if (targetCols.size() >= 2 && Randomly.getBoolean()) {
            TiDBColumn col2 = targetCols.get(1);
            List<String> sampled2 = sampleColumnValues(tblName, col2.getName(), 3);
            sb.append(" AND ").append(col2.getName());
            if (sampled2 != null && !sampled2.isEmpty()) {
                sb.append(" >= ").append(quoteValueForSQL(sampled2.get(0), col2));
            } else {
                sb.append(" IS NOT NULL");
            }
        }

        // ORDER BY + LIMIT
        if (Randomly.getBoolean()) {
            sb.append(" ORDER BY ").append(whereCol.getName());
            if (Randomly.getBoolean()) sb.append(" DESC");
        }
        sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1);
        sb.append(";");
        return sb.toString();
    }

    // ==================== Index-Aware Query Generation ====================

    private String generateIndexAwareQuery(TiDBTable targetTable) {
        // 60% chance: use AST-based complex query with index-aware WHERE
        if (Randomly.fromOptions(true, true, true, false, false)) {
            try {
                List<TiDBColumn> columns = targetTable.getColumns();
                if (columns.isEmpty()) return generateQuery();

                TiDBExpressionGenerator gen = new TiDBExpressionGenerator(globalState).setColumns(columns);
                TiDBSelect select = new TiDBSelect();

                // SELECT: pick some columns from the target table
                List<TiDBExpression> fetchColumns = new ArrayList<>();
                List<TiDBColumn> subset = Randomly.nonEmptySubset(columns);
                for (TiDBColumn col : subset) {
                    fetchColumns.add(new TiDBColumnReference(col));
                }
                select.setFetchColumns(fetchColumns);

                // FROM
                List<TiDBExpression> fromList = new ArrayList<>();
                fromList.add(new TiDBTableReference(targetTable));
                select.setFromList(fromList);

                // WHERE: always use index-aware conditions
                TiDBExpression indexWhere = generateIndexAwareWhere(targetTable, columns);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                }

                // ORDER BY: 50% chance, using table columns
                if (Randomly.getBoolean()) {
                    select.setOrderByClauses(gen.generateOrderBys());
                }

                // LIMIT
                if (Randomly.getBoolean()) {
                    select.setLimitClause(TiDBConstant.createIntConstant(
                            Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));
                }

                return TiDBVisitor.asString(select) + ";";
            } catch (Exception e) {
                // Fall through to string-based generation
            }
        }

        // 40% chance: string-based query with WHERE on target table columns
        List<TiDBColumn> columns = targetTable.getColumns();
        if (columns.isEmpty()) return generateQuery();

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        int numCols = Math.min(columns.size(), Randomly.smallNumber() + 1);
        List<TiDBColumn> subset = Randomly.extractNrRandomColumns(columns, numCols);
        for (int i = 0; i < subset.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(subset.get(i).getName());
        }
        sb.append(" FROM ").append(targetTable.getName());

        // WHERE: P0 — use data-aware values when possible to avoid empty result sets
        sb.append(" WHERE ");
        TiDBColumn whereCol = Randomly.fromList(columns);

        // P0: Try sampling actual column values for data-aware conditions
        List<String> sampledValues = sampleColumnValues(targetTable.getName(), whereCol.getName(), 10);
        boolean hasSampledValues = sampledValues != null && !sampledValues.isEmpty();

        int whereStrategy = Randomly.fromOptions(0, 1, 2, 3, 4);
        switch (whereStrategy) {
            case 0: // Equality — use sampled value if available
                if (hasSampledValues) {
                    sb.append(whereCol.getName()).append(" = ").append(quoteValueForSQL(sampledValues.get(0), whereCol));
                } else {
                    sb.append(whereCol.getName()).append(" = ").append(generateRandomValueForColumn(whereCol));
                }
                break;
            case 1: // Range — use sampled values as boundaries
                if (hasSampledValues && sampledValues.size() >= 2) {
                    sb.append(whereCol.getName()).append(" >= ").append(quoteValueForSQL(sampledValues.get(0), whereCol));
                    sb.append(" AND ").append(whereCol.getName()).append(" <= ").append(quoteValueForSQL(sampledValues.get(1), whereCol));
                } else {
                    sb.append(whereCol.getName()).append(" IS NOT NULL");
                }
                break;
            case 2: // IS NOT NULL + comparison with sampled value
                sb.append(whereCol.getName()).append(" IS NOT NULL");
                if (hasSampledValues && Randomly.getBoolean()) {
                    sb.append(" AND ").append(whereCol.getName());
                    sb.append(Randomly.fromOptions(" >= ", " <= "));
                    sb.append(quoteValueForSQL(sampledValues.get(0), whereCol));
                }
                break;
            case 3: // IN list — use sampled values
                if (hasSampledValues) {
                    sb.append(whereCol.getName()).append(" IN (");
                    int inSize = Math.min(sampledValues.size(), Randomly.smallNumber() + 1);
                    for (int i = 0; i < inSize; i++) {
                        if (i > 0) sb.append(", ");
                        sb.append(quoteValueForSQL(sampledValues.get(i), whereCol));
                    }
                    sb.append(")");
                } else {
                    sb.append(whereCol.getName()).append(" IS NOT NULL");
                }
                break;
            case 4: // Multi-column with sampled values
                if (hasSampledValues) {
                    sb.append(whereCol.getName()).append(" = ").append(quoteValueForSQL(sampledValues.get(0), whereCol));
                } else {
                    sb.append(whereCol.getName()).append(" IS NOT NULL");
                }
                if (columns.size() > 1) {
                    TiDBColumn col2 = Randomly.fromList(columns);
                    sb.append(" AND ").append(col2.getName());
                    List<String> sampled2 = sampleColumnValues(targetTable.getName(), col2.getName(), 5);
                    if (sampled2 != null && !sampled2.isEmpty() && Randomly.getBoolean()) {
                        sb.append(" >= ").append(quoteValueForSQL(sampled2.get(0), col2));
                    } else {
                        sb.append(" IS NOT NULL");
                    }
                }
                break;
        }

        // ORDER BY: 50% chance
        if (Randomly.getBoolean()) {
            TiDBColumn orderCol = Randomly.fromList(columns);
            sb.append(" ORDER BY ").append(orderCol.getName());
            if (Randomly.getBoolean()) sb.append(" DESC");
        }

        sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1);
        sb.append(";");
        return sb.toString();
    }

    // ==================== Query Generation ====================

    private String generateQuery() {
        // 90% chance: use AST-based complex query with deep expression trees
        if (!Randomly.getBooleanWithRatherLowProbability()) {
            String complexQuery = generateComplexQuery();
            if (complexQuery != null) return complexQuery;
        }

        // 30% chance: use simple string-based query (original logic)
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return "SELECT 1;";
        TiDBTable table = Randomly.fromList(tables);
        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return "SELECT 1;";

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        int numCols = Math.min(columns.size(), Randomly.smallNumber() + 1);
        List<TiDBColumn> subset = Randomly.extractNrRandomColumns(columns, numCols);
        for (int i = 0; i < subset.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(subset.get(i).getName());
        }
        sb.append(" FROM ").append(table.getName());

        // Multi-table JOIN: 40% chance when multiple tables exist
        if (tables.size() > 1 && Randomly.getBoolean()) {
            // Try index-friendly JOIN first (30% chance)
            if (Randomly.getBooleanWithRatherLowProbability()) {
                String idxJoin = generateIndexFriendlyJoinClauses(tables, table);
                if (idxJoin != null && !idxJoin.isEmpty()) {
                    sb.append(idxJoin);
                } else {
                    // Fallback to simple random JOIN
                    List<TiDBTable> otherTables = new ArrayList<>(tables);
                    otherTables.remove(table);
                    TiDBTable joinTable = Randomly.fromList(otherTables);
                    List<TiDBColumn> joinCols = joinTable.getColumns();
                    if (!joinCols.isEmpty()) {
                        String joinType = Randomly.fromOptions("JOIN", "LEFT JOIN", "INNER JOIN");
                        sb.append(" ").append(joinType).append(" ").append(joinTable.getName());
                        TiDBColumn c1 = Randomly.fromList(columns);
                        TiDBColumn c2 = Randomly.fromList(joinCols);
                        sb.append(" ON ").append(table.getName()).append(".").append(c1.getName());
                        sb.append(" = ").append(joinTable.getName()).append(".").append(c2.getName());
                    }
                }
            } else {
                List<TiDBTable> otherTables = new ArrayList<>(tables);
                otherTables.remove(table);
                TiDBTable joinTable = Randomly.fromList(otherTables);
                List<TiDBColumn> joinCols = joinTable.getColumns();
                if (!joinCols.isEmpty()) {
                    String joinType = Randomly.fromOptions("JOIN", "LEFT JOIN", "INNER JOIN");
                    sb.append(" ").append(joinType).append(" ").append(joinTable.getName());
                    TiDBColumn c1 = Randomly.fromList(columns);
                    TiDBColumn c2 = Randomly.fromList(joinCols);
                    sb.append(" ON ").append(table.getName()).append(".").append(c1.getName());
                    sb.append(" = ").append(joinTable.getName()).append(".").append(c2.getName());
                }
            }
        }

        // WHERE: try index-friendly WHERE first (30% chance), then fallback to data-aware
        if (Randomly.getBooleanWithRatherLowProbability()) {
            String idxWhere = tryGenerateIndexFriendlyWhere(table, columns);
            if (idxWhere != null) {
                sb.append(" WHERE ").append(idxWhere);
            } else if (Randomly.getBoolean()) {
            TiDBColumn whereCol = Randomly.fromList(columns);
            List<String> sampled = sampleColumnValues(table.getName(), whereCol.getName(), 5);
            boolean hasSampled = sampled != null && !sampled.isEmpty();
            int whereVariant = Randomly.fromOptions(0, 1, 2, 3);
            switch (whereVariant) {
            case 0: // Equality with sampled value
                if (hasSampled) {
                    sb.append(" WHERE ").append(whereCol.getName()).append(" = ").append(quoteValueForSQL(sampled.get(0), whereCol));
                } else {
                    sb.append(" WHERE ").append(whereCol.getName()).append(" IS NOT NULL");
                }
                break;
            case 1: // Range with sampled boundaries
                if (hasSampled && sampled.size() >= 2) {
                    sb.append(" WHERE ").append(whereCol.getName()).append(" >= ").append(quoteValueForSQL(sampled.get(0), whereCol));
                    sb.append(" AND ").append(whereCol.getName()).append(" <= ").append(quoteValueForSQL(sampled.get(1), whereCol));
                } else {
                    sb.append(" WHERE ").append(whereCol.getName()).append(" IS NOT NULL");
                }
                break;
            case 2: // IS NOT NULL + optional sampled comparison
                sb.append(" WHERE ").append(whereCol.getName()).append(" IS NOT NULL");
                if (hasSampled && Randomly.getBoolean()) {
                    sb.append(" AND ").append(whereCol.getName());
                    sb.append(Randomly.fromOptions(" >= ", " <= ", " != "));
                    sb.append(quoteValueForSQL(sampled.get(0), whereCol));
                }
                break;
            default: // IN list with sampled values
                if (hasSampled) {
                    sb.append(" WHERE ").append(whereCol.getName()).append(" IN (");
                    int inSize = Math.min(sampled.size(), Randomly.smallNumber() + 1);
                    for (int i = 0; i < inSize; i++) {
                        if (i > 0) sb.append(", ");
                        sb.append(quoteValueForSQL(sampled.get(i), whereCol));
                    }
                    sb.append(")");
                } else {
                    sb.append(" WHERE ").append(whereCol.getName()).append(" IS NOT NULL");
                }
                break;
            }
            }
        }
        if (Randomly.getBoolean()) {
            TiDBColumn orderCol = Randomly.fromList(columns);
            sb.append(" ORDER BY ").append(orderCol.getName());
            if (Randomly.getBoolean()) sb.append(" DESC");
        }
        sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1);
        sb.append(";");
        return sb.toString();
    }

    private String generateJoinQuery() {
        TiDBSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().size() < 2) return null;

        List<TiDBTable> tableList = Randomly.nonEmptySubset(schema.getDatabaseTables());
        if (tableList.size() < 2) return null;

        TiDBTable t1 = tableList.get(0);
        TiDBTable t2 = tableList.get(1);
        List<TiDBColumn> cols1 = t1.getColumns();
        List<TiDBColumn> cols2 = t2.getColumns();
        if (cols1.isEmpty() || cols2.isEmpty()) return null;

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        if (Randomly.getBoolean()) {
            sb.append(t1.getName()).append(".").append(cols1.get(0).getName());
        } else {
            sb.append("*");
        }
        sb.append(" FROM ").append(t1.getName());

        String joinType = Randomly.fromOptions("JOIN", "LEFT JOIN", "RIGHT JOIN", "INNER JOIN");
        sb.append(" ").append(joinType).append(" ").append(t2.getName());

        if (Randomly.getBoolean() && !cols1.isEmpty() && !cols2.isEmpty()) {
            sb.append(" ON ").append(t1.getName()).append(".").append(cols1.get(0).getName());
            sb.append(" = ").append(t2.getName()).append(".").append(cols2.get(0).getName());
        }

        if (Randomly.getBoolean()) {
            sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1);
        }
        sb.append(";");
        return sb.toString();
    }

    // Mode 7 legacy: ensures INL_JOIN hint references tables actually present in the query.
    private String generateIndexAwareJoinQuery(TiDBTable t1, TiDBTable t2) {
        List<TiDBColumn> cols1 = t1.getColumns();
        List<TiDBColumn> cols2 = t2.getColumns();
        if (cols1.isEmpty() || cols2.isEmpty()) return null;

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        if (Randomly.getBoolean()) {
            sb.append(t1.getName()).append(".").append(cols1.get(0).getName());
        } else {
            sb.append("*");
        }
        sb.append(" FROM ").append(t1.getName());

        String joinType = Randomly.fromOptions("JOIN", "LEFT JOIN", "INNER JOIN");
        sb.append(" ").append(joinType).append(" ").append(t2.getName());

        if (Randomly.getBoolean() && !cols1.isEmpty() && !cols2.isEmpty()) {
            sb.append(" ON ").append(t1.getName()).append(".").append(cols1.get(0).getName());
            sb.append(" = ").append(t2.getName()).append(".").append(cols2.get(0).getName());
        }

        // Add index-friendly WHERE condition using sampled column values
        if (Randomly.getBoolean()) {
            List<TiDBColumn> indexableCols1 = getIndexableColumns(t1);
            if (!indexableCols1.isEmpty()) {
                TiDBColumn whereCol = Randomly.fromList(indexableCols1);
                List<String> sampled = getCachedSampledValues(t1.getName(), whereCol.getName(), 5);
                if (sampled != null && !sampled.isEmpty()) {
                    String val = quoteValueForSQL(sampled.get(0), whereCol);
                    sb.append(" WHERE ").append(t1.getName()).append(".").append(whereCol.getName())
                            .append(" = ").append(val);
                } else {
                    sb.append(" WHERE ").append(t1.getName()).append(".").append(whereCol.getName())
                            .append(" IS NOT NULL");
                }
            }
        }

        if (Randomly.getBoolean()) {
            sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1);
        }
        sb.append(";");
        return sb.toString();
    }

    private String generateSimpleAggregateQuery() {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return null;
        TiDBTable table = Randomly.fromList(tables);
        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return null;

        TiDBColumn col = Randomly.fromList(columns);
        String aggFunc = Randomly.fromOptions("COUNT", "SUM", "AVG", "MIN", "MAX");

        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ").append(aggFunc).append("(").append(col.getName()).append(")");
        sb.append(" FROM ").append(table.getName());

        if (Randomly.getBoolean()) {
            sb.append(" WHERE ").append(col.getName()).append(" IS NOT NULL");
        }
        sb.append(";");
        return sb.toString();
    }

    private String generateOrderedQuery() {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return null;
        TiDBTable table = Randomly.fromList(tables);
        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return null;

        TiDBColumn orderCol = Randomly.fromList(columns);
        StringBuilder sb = new StringBuilder();
        sb.append("SELECT ");
        int numCols = Math.min(columns.size(), Randomly.smallNumber() + 1);
        List<TiDBColumn> subset = Randomly.extractNrRandomColumns(columns, numCols);
        for (int i = 0; i < subset.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(subset.get(i).getName());
        }
        sb.append(" FROM ").append(table.getName());
        if (Randomly.getBoolean()) {
            sb.append(" WHERE ").append(orderCol.getName()).append(" IS NOT NULL");
        }
        sb.append(" ORDER BY ").append(orderCol.getName());
        if (Randomly.getBoolean()) sb.append(" DESC");
        sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1);
        sb.append(";");
        return sb.toString();
    }

    // ==================== Helpers ====================

    // Unexpected errors (not in the errors list) propagate as AssertionError, same as before.
    private ExecResult execV2(String query) {
        try {
            List<String> rows = ComparatorHelper.getResultSetAllColumnsAsString(query, errors, globalState, " ||| ");
            return new ExecResult(ExecResult.SUCCESS, rows);
        } catch (IgnoreMeException e) {
            return new ExecResult(ExecResult.EXPECTED_ERROR, null);
        } catch (Exception e) {
            // Should not happen — ComparatorHelper wraps non-IgnoreMeException as AssertionError
            // but be safe
            return new ExecResult(ExecResult.EXPECTED_ERROR, null);
        }
    }

    // Legacy method retained for non-comparison uses (sampling, ADMIN CHECK, etc.).
    private List<String> exec(String query) {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(query, errors, globalState, " ||| ");
        } catch (Exception e) {
            return null;
        }
    }

    // Detects asymmetric success/failure (one plan crashes, the other succeeds) as
    // potential optimizer bugs. Returns false if both plans hit expected errors.
    private boolean compareQueries(String q1, String q2, String label, String queryContext) throws Exception {
        ExecResult r1 = execV2(q1);
        ExecResult r2 = execV2(q2);

        // Key: detect asymmetric success/failure
        if (r1.isSuccess() != r2.isSuccess()) {
            throw new AssertionError(
                "TIDB_ASYMMETRIC_" + label + ": queries produced different success outcomes!\n"
                + "Q1 [" + (r1.isSuccess() ? "OK, " + r1.getRows().size() + " rows" : "EXPECTED_ERROR") + "]: " + q1 + "\n"
                + "Q2 [" + (r2.isSuccess() ? "OK, " + r2.getRows().size() + " rows" : "EXPECTED_ERROR") + "]: " + q2);
        }

        // Both hit expected errors → skip
        if (!r1.isSuccess()) return false;

        // Both succeeded → compare results
        lastCompareFiltered = false;
        assertResultSorted(r1.getRows(), r2.getRows(), queryContext, "TIDB_" + label);
        return true;
    }

    private void analyzeAllTables() {
        // Build expected errors for ANALYZE TABLE — TiDB DDL operations are asynchronous,
        // so information schema may be temporarily inconsistent during heavy DDL workloads.
        // This can cause transient "Table doesn't exist" or "Information schema is changed"
        // errors that are NOT real bugs.
        ExpectedErrors analyzeErrors = new ExpectedErrors();
        analyzeErrors.add("doesn't exist");
        analyzeErrors.add("does not exist");
        analyzeErrors.add("Information schema is changed");

        for (TiDBTable table : globalState.getSchema().getDatabaseTables()) {
            if (table.isView()) continue; // TiDB does not support ANALYZE on views
            try {
                String analyzeStmt = "ANALYZE TABLE " + table.getName() + ";";
                log(analyzeStmt);
                globalState.executeStatement(new SQLQueryAdapter(analyzeStmt, analyzeErrors, true));
            } catch (Throwable e) {
                // Use catch(Throwable) to also catch AssertionError from SQLQueryAdapter
                // when an unexpected error occurs. ANALYZE TABLE is a best-effort
                // operation — failures should not abort the oracle check.
            }
        }
        // Also analyze any tables that were marked by individual modes
        for (String tableName : tablesNeedingAnalyze) {
            try {
                String analyzeStmt = "ANALYZE TABLE " + tableName + ";";
                log(analyzeStmt);
                globalState.executeStatement(new SQLQueryAdapter(analyzeStmt, analyzeErrors, true));
            } catch (Throwable e) { }
        }
        tablesNeedingAnalyze.clear();
    }

    // Faster than analyzeAllTables() when only one table was modified by DDL.
    private void analyzeTable(String tableName) {
        ExpectedErrors analyzeErrors = new ExpectedErrors();
        analyzeErrors.add("doesn't exist");
        analyzeErrors.add("does not exist");
        analyzeErrors.add("Information schema is changed");
        try {
            String analyzeStmt = "ANALYZE TABLE " + tableName + ";";
            log(analyzeStmt);
            globalState.executeStatement(new SQLQueryAdapter(analyzeStmt, analyzeErrors, true));
        } catch (Throwable e) {
            // ANALYZE TABLE is best-effort
        }
    }

    private void refreshSchema() {
        try {
            globalState.updateSchema();
        } catch (Throwable e) {
            // best-effort: a stale model for one iteration is preferable
            // to aborting the entire oracle run.
        }
    }

    private TiDBTable getRandomTableWithIndexes() {
        List<TiDBTable> candidates = new ArrayList<>();
        for (TiDBTable t : globalState.getSchema().getDatabaseTables()) {
            if (!t.getIndexes().isEmpty()) candidates.add(t);
        }
        if (candidates.isEmpty()) return null;
        return Randomly.fromList(candidates);
    }

    private TableIndex getRandomNonPrimaryIndex() {
        List<TableIndex> candidates = new ArrayList<>();
        for (TiDBTable table : globalState.getSchema().getDatabaseTables()) {
            for (TableIndex idx : table.getIndexes()) {
                if (!idx.getIndexName().equals("PRIMARY")) {
                    candidates.add(idx);
                }
            }
        }
        return candidates.isEmpty() ? null : Randomly.fromList(candidates);
    }

    private String findTableForIndex(TableIndex targetIdx) {
        for (TiDBTable table : globalState.getSchema().getDatabaseTables()) {
            for (TableIndex idx : table.getIndexes()) {
                if (idx.getIndexName().equals(targetIdx.getIndexName())) {
                    return table.getName();
                }
            }
        }
        return null;
    }

    // LIMIT without ORDER BY is non-deterministic across plans — expected SQL behavior.
    // Real index bugs (wrong values, missing rows) still get caught when ORDER BY is present.
    private boolean hasLimitWithoutOrderBy(String query) {
        String upperQuery = query.toUpperCase();
        boolean hasLimit = upperQuery.contains("LIMIT");
        boolean hasOrderBy = upperQuery.contains("ORDER BY");
        return hasLimit && !hasOrderBy;
    }

    // GROUP BY with only constants (GROUP BY NULL, 1+2, etc.) collapses all rows into
    // one group; TiDB picks arbitrary non-aggregated column values → non-deterministic.
    private boolean hasNonDeterministicGroupBy(String query) {
        String upperQuery = query.toUpperCase();
        if (!upperQuery.contains("GROUP BY")) return false;

        int groupByStart = upperQuery.indexOf("GROUP BY");
        if (groupByStart == -1) return false;
        String afterGroupBy = query.substring(groupByStart + "GROUP BY".length()).trim();

        int endIdx = afterGroupBy.length();
        for (String keyword : new String[]{" HAVING ", " ORDER BY ", " LIMIT ", " INTO "}) {
            int idx = afterGroupBy.toUpperCase().indexOf(keyword);
            if (idx != -1 && idx < endIdx) {
                endIdx = idx;
            }
        }
        String groupByExpr = afterGroupBy.substring(0, endIdx).trim();

        String[] groupByParts = groupByExpr.split(",");
        for (String part : groupByParts) {
            String trimmed = part.trim();
            if (trimmed.matches(".*[a-zA-Z].*")) {
                return false;
            }
        }

        return true;
    }

    // In TiDB's non-strict mode, SELECT columns not in GROUP BY return an arbitrary
    // row's value per group — non-deterministic across execution plans.
    private boolean hasNonGroupingSelectColumns(String query) {
        String upperQuery = query.toUpperCase();
        if (!upperQuery.contains("GROUP BY")) return false;

        try {
            // Extract GROUP BY columns
            int groupByStart = upperQuery.indexOf("GROUP BY");
            String afterGroupBy = query.substring(groupByStart + "GROUP BY".length()).trim();
            int gbEnd = afterGroupBy.length();
            for (String kw : new String[]{" HAVING ", " ORDER BY ", " LIMIT ", " INTO "}) {
                int idx = afterGroupBy.toUpperCase().indexOf(kw);
                if (idx != -1 && idx < gbEnd) gbEnd = idx;
            }
            String groupByExpr = afterGroupBy.substring(0, gbEnd).trim().toUpperCase();
            Set<String> groupByCols = new HashSet<>();
            for (String part : groupByExpr.split(",")) {
                // Extract column name: table.col or just col
                String trimmed = part.trim().replaceAll("(?i)\\s+(ASC|DESC)\\s*$", "").trim();
                // Strip table prefix if present
                if (trimmed.contains(".")) {
                    trimmed = trimmed.substring(trimmed.lastIndexOf(".") + 1);
                }
                groupByCols.add(trimmed.toUpperCase());
            }

            // Extract SELECT columns (between SELECT and FROM/GROUP BY/etc.)
            int selectStart = upperQuery.indexOf("SELECT") + "SELECT".length();
            int selectEnd = upperQuery.length();
            for (String kw : new String[]{" FROM ", " WHERE ", " GROUP BY ", " HAVING ", " ORDER BY ", " LIMIT "}) {
                int idx = upperQuery.indexOf(kw, selectStart);
                if (idx != -1 && idx < selectEnd) selectEnd = idx;
            }
            String selectClause = query.substring(selectStart, selectEnd).trim();

            // Check each SELECT expression for column references not in GROUP BY
            // Skip expressions that are aggregate functions: COUNT(...), SUM(...), etc.
            for (String expr : selectClause.split(",")) {
                String trimmedExpr = expr.trim();
                // Skip aggregate function calls
                String upperExpr = trimmedExpr.toUpperCase();
                if (upperExpr.startsWith("COUNT(") || upperExpr.startsWith("SUM(")
                        || upperExpr.startsWith("AVG(") || upperExpr.startsWith("MIN(")
                        || upperExpr.startsWith("MAX(") || upperExpr.startsWith("GROUP_CONCAT(")
                        || upperExpr.startsWith("BIT_AND(") || upperExpr.startsWith("BIT_OR(")
                        || upperExpr.startsWith("BIT_XOR(") || upperExpr.startsWith("STD(")
                        || upperExpr.startsWith("STDDEV(") || upperExpr.startsWith("VARIANCE(")
                        || upperExpr.startsWith("JSON_ARRAYAGG(") || upperExpr.startsWith("JSON_OBJECTAGG(")) {
                    continue;
                }
                // Check if this expression contains column references (e.g., "t0.c0" or "c0")
                // that are NOT in the GROUP BY list
                java.util.regex.Pattern colPattern = java.util.regex.Pattern.compile(
                        "(\\w+)\\.(\\w+)|(?:^|\\(|\\s|,)(\\w+)(?:\\)|\\s|,|$)");
                java.util.regex.Matcher m = colPattern.matcher(trimmedExpr);
                while (m.find()) {
                    String colName;
                    if (m.group(2) != null) {
                        colName = m.group(2).toUpperCase();
                    } else if (m.group(3) != null) {
                        String word = m.group(3).toUpperCase();
                        // Skip SQL keywords and function names
                        if (word.matches("CASE|WHEN|THEN|ELSE|END|AND|OR|NOT|NULL|TRUE|FALSE|IS|AS|CAST|LIKE|IN|BETWEEN|EXISTS|SELECT|BINARY|REGEXP")) {
                            continue;
                        }
                        colName = word;
                    } else {
                        continue;
                    }
                    if (!groupByCols.contains(colName)) {
                        return true;
                    }
                }
            }
        } catch (Exception e) {
            // On error, conservatively return false (don't skip the check)
        }
        return false;
    }

    // Rows are delimited as "col1 ||| col2 ||| ..."; extract only the first column.
    private List<String> extractFirstColumn(List<String> rows) {
        List<String> result = new ArrayList<>();
        for (String row : rows) {
            int idx = row.indexOf(" ||| ");
            if (idx >= 0) {
                result.add(row.substring(0, idx));
            } else {
                result.add(row); // single column
            }
        }
        return result;
    }

    private void assertResultSorted(List<String> r1, List<String> r2, String query, String label) {
        if (r1.equals(r2)) return;

        // LIMIT without ORDER BY → non-deterministic row selection, skip comparison
        if (hasLimitWithoutOrderBy(query)) { lastCompareFiltered = true; return; }

        // GROUP BY with constant expressions (no column refs) → non-deterministic
        if (hasNonDeterministicGroupBy(query)) { lastCompareFiltered = true; return; }

        // GROUP BY with SELECT columns not in GROUP BY → non-deterministic
        if (hasNonGroupingSelectColumns(query)) { lastCompareFiltered = true; return; }

        List<String> sorted1 = new ArrayList<>(r1);
        List<String> sorted2 = new ArrayList<>(r2);
        Collections.sort(sorted1);
        Collections.sort(sorted2);
        if (sorted1.equals(sorted2)) return;

        // Floating-point tolerance
        if (resultsAlmostEqualDouble(sorted1, sorted2)) { lastCompareFiltered = true; return; }

        // GROUP BY with different result set sizes → non-deterministic
        if (sorted1.size() != sorted2.size() && query.toUpperCase().contains("GROUP BY")) { lastCompareFiltered = true; return; }

        // LIMIT with different result sizes → check if ORDER BY is unique
        // (Fix: previously skipped unconditionally, missing bugs when ORDER BY has a unique tie-breaker)
        if (sorted1.size() != sorted2.size() && query.toUpperCase().contains("LIMIT")) {
            if (!hasUniqueOrderByTieBreaker(query)) {
                lastCompareFiltered = true; return;
            }
            // has unique ORDER BY tie-breaker → size difference is likely a real bug, fall through
        }

        // LIMIT + ORDER BY: Check for unique tie-breaker (only when sizes match but content differs).
        String upperQuery = query.toUpperCase();
        if (upperQuery.contains("LIMIT") && upperQuery.contains("ORDER BY")) {
            if (hasUniqueOrderByTieBreaker(query)) {
                // deterministic → fall through to report
            } else {
                lastCompareFiltered = true; return;
            }
        }

        throw new AssertionError(label + " mismatch!\nQuery: " + query
                + "\nResult1 (" + sorted1.size() + "): " + sorted1
                + "\nResult2 (" + sorted2.size() + "): " + sorted2);
    }

    private void assertResultStrict(List<String> r1, List<String> r2, String query, String label) {
        if (r1.equals(r2)) return;

        // Floating-point tolerance (same rationale as assertResultSorted)
        if (resultsAlmostEqualDouble(r1, r2)) { lastCompareFiltered = true; return; }

        // LIMIT without ORDER BY → non-deterministic
        if (hasLimitWithoutOrderBy(query)) { lastCompareFiltered = true; return; }

        // GROUP BY with constant expressions → non-deterministic
        if (hasNonDeterministicGroupBy(query)) { lastCompareFiltered = true; return; }

        // GROUP BY with SELECT columns not in GROUP BY → non-deterministic
        if (hasNonGroupingSelectColumns(query)) { lastCompareFiltered = true; return; }

        // GROUP BY with different result set sizes → non-deterministic
        if (r1.size() != r2.size() && query.toUpperCase().contains("GROUP BY")) { lastCompareFiltered = true; return; }

        // LIMIT with different result sizes → check if ORDER BY is unique
        if (r1.size() != r2.size() && query.toUpperCase().contains("LIMIT")) {
            if (!hasUniqueOrderByTieBreaker(query)) {
                lastCompareFiltered = true; return;
            }
        }

        // LIMIT + ORDER BY
        String upperQuery = query.toUpperCase();
        if (upperQuery.contains("LIMIT") && upperQuery.contains("ORDER BY")) {
            if (hasUniqueOrderByTieBreaker(query)) {
                // deterministic → fall through
            } else {
                lastCompareFiltered = true; return;
            }
        }

        throw new AssertionError(label + " strict mismatch!\nQuery: " + query
                + "\nResult1 (" + r1.size() + "): " + r1
                + "\nResult2 (" + r2.size() + "): " + r2);
    }

    // ==================== P0: COUNT(*) Aggregate Fallback ====================

    // When row comparison is filtered (LIMIT without ORDER BY, non-det GROUP BY, etc.),
    // COUNT(*) is a deterministic fallback that still catches missing/extra-row bugs.
    private void countStarFallback(String queryA, String queryB, String mode) {
        aggregateFallbackUsed++;
        try {
            String countA = wrapInCountStar(queryA);
            String countB = wrapInCountStar(queryB);
            if (countA == null || countB == null) return;
            List<String> r1 = exec(countA);
            List<String> r2 = exec(countB);
            if (r1 == null || r2 == null) return;
            if (!r1.equals(r2)) {
                throw new AssertionError(mode + " COUNT(*) fallback mismatch!\nCountA: " + countA
                        + "\nCountB: " + countB
                        + "\nResult1: " + r1 + "\nResult2: " + r2);
            }
        } catch (AssertionError e) {
            throw e;
        } catch (Exception e) {
            // COUNT(*) fallback failed — ignore gracefully
        }
    }

    // Strips top-level ORDER BY/LIMIT using backward search to avoid stripping ORDER BY
    // inside subqueries.
    private String wrapInCountStar(String query) {
        try {
            String q = query.trim();
            if (q.endsWith(";")) q = q.substring(0, q.length() - 1).trim();
            // Strip LIMIT first (always at the very end if present)
            q = q.replaceAll("(?i)\\s+LIMIT\\s+\\d+\\s*$", "").trim();
            // Strip ORDER BY — only if it's at the top level (not inside parentheses).
            // Find the last "ORDER BY" that is NOT inside parentheses.
            int lastOrderBy = findLastTopLevelOrderBy(q);
            if (lastOrderBy >= 0) {
                q = q.substring(0, lastOrderBy).trim();
            }
            return "SELECT COUNT(*) FROM (" + q + ") AS _count_subq;";
        } catch (Exception e) {
            return null;
        }
    }

    // "Top-level" means not inside parentheses (i.e., not inside a subquery); returns -1 if absent.
    private int findLastTopLevelOrderBy(String sql) {
        String upper = sql.toUpperCase();
        int depth = 0;
        int lastPos = -1;
        for (int i = 0; i < sql.length(); i++) {
            char c = sql.charAt(i);
            if (c == '(') depth++;
            else if (c == ')') depth--;
            else if (depth == 0 && i + 8 <= sql.length() && upper.substring(i, i + 8).equals("ORDER BY")) {
                lastPos = i;
            }
        }
        return lastPos;
    }

    // ==================== Floating-Point Tolerance ====================

    // Relative tolerance 1e-10 avoids false positives from SUM accumulation order (StreamAgg
    // vs HashAgg) while still catching COUNT(*) differences (relDiff ~0.17) and wrong values.
    // Non-numeric strings fall through to exact comparison.
    private boolean resultsAlmostEqualDouble(List<String> r1, List<String> r2) {
        if (r1.size() != r2.size()) return false;
        for (int i = 0; i < r1.size(); i++) {
            String s1 = r1.get(i);
            String s2 = r2.get(i);
            if (s1.equals(s2)) continue;
            try {
                double v1 = Double.parseDouble(s1);
                double v2 = Double.parseDouble(s2);
                // Handle special IEEE 754 values
                if (Double.isNaN(v1) && Double.isNaN(v2)) continue;
                if (Double.isInfinite(v1) || Double.isInfinite(v2)) {
                    if (v1 == v2) continue;
                    return false; // Different infinities
                }
                // Both finite: compare with relative tolerance
                double maxAbs = Math.max(Math.abs(v1), Math.abs(v2));
                if (maxAbs == 0.0) continue; // Both are 0.0 (or -0.0)
                double relDiff = Math.abs(v1 - v2) / maxAbs;
                if (relDiff > 1e-10) return false;
            } catch (NumberFormatException e) {
                return false; // Not numeric → cannot use tolerance, must be exact
            }
        }
        return true;
    }

    // ==================== P1: Tie-Breaker Detection ====================

    // Only considers tN-pattern tables; returns null on failure (conservative: assumes no tie-breaker).
    private Set<String> extractFromTables(String queryString) {
        try {
            String upper = queryString.toUpperCase();
            int fromIdx = upper.indexOf("FROM ");
            if (fromIdx == -1) return null;

            // Find the end of the FROM clause
            int start = fromIdx + 5;
            int whereIdx = upper.indexOf(" WHERE ", start);
            int orderByIdx = upper.indexOf("ORDER BY", start);
            int limitIdx = upper.indexOf("LIMIT", start);
            int groupByIdx = upper.indexOf("GROUP BY", start);
            int havingIdx = upper.indexOf("HAVING", start);
            int endIdx = queryString.length();
            for (int idx : new int[]{whereIdx, orderByIdx, limitIdx, groupByIdx, havingIdx}) {
                if (idx != -1 && idx < endIdx) endIdx = idx;
            }

            String fromClause = queryString.substring(start, endIdx).trim();
            Set<String> tables = new HashSet<>();

            // Split by comma for multi-table FROM clauses (e.g., JOINs)
            String[] parts = fromClause.split(",");
            for (String part : parts) {
                String trimmed = part.trim();
                // Remove alias: t0 AS x or t0 x → t0
                trimmed = trimmed.replaceAll("(?i)\\s+AS\\s+\\S+", "");
                trimmed = trimmed.replaceAll("(?i)^(t\\d+)(\\s+\\S+)?$", "$1");
                trimmed = trimmed.trim();
                // Only add if it looks like a idxdiff table name (tN)
                if (trimmed.matches("t\\d+")) {
                    tables.add(trimmed);
                }
            }

            // Also handle JOIN syntax: "t0 JOIN t1 ON ..." (no comma between tables)
            java.util.regex.Pattern joinPattern = java.util.regex.Pattern.compile(
                    "(?i)\\b(t\\d+)\\s+(?:INNER\\s+|LEFT\\s+|RIGHT\\s+|CROSS\\s+)?JOIN\\s+(t\\d+)");
            java.util.regex.Matcher m = joinPattern.matcher(fromClause);
            while (m.find()) {
                tables.add(m.group(1));
                tables.add(m.group(2));
            }

            return tables.isEmpty() ? null : tables;
        } catch (Exception e) {
            return null;
        }
    }

    // TiDB's TableIndex doesn't expose column info, so tie-breaker check is PK-only.
    private boolean hasUniqueOrderByTieBreaker(String queryString) {
        try {
            String upperQuery = queryString.toUpperCase();
            int orderByIdx = upperQuery.indexOf("ORDER BY");
            if (orderByIdx == -1) return false;

            String afterOrderBy = queryString.substring(orderByIdx + "ORDER BY".length());
            int endIdx = afterOrderBy.length();
            for (String kw : new String[]{" LIMIT ", " OFFSET "}) {
                int idx = afterOrderBy.toUpperCase().indexOf(kw);
                if (idx != -1 && idx < endIdx) endIdx = idx;
            }
            String orderByClause = afterOrderBy.substring(0, endIdx).trim();

            // Collect all ORDER BY column names (stripped of ASC/DESC and table prefix)
            Set<String> orderByCols = new HashSet<>();
            for (String part : orderByClause.split(",")) {
                String expr = part.trim().replaceAll("(?i)\\s+(ASC|DESC)\\s*$", "").trim();
                orderByCols.add(expr);
            }

            // Only check tables that actually appear in the FROM clause.
            // This prevents false matches where table t0 has PK column c0,
            // but the query is on table t1 (which has no such unique constraint on c0).
            Set<String> fromTables = extractFromTables(queryString);
            if (fromTables == null) {
                return false;
            }

            TiDBSchema schema = globalState.getSchema();
            for (TiDBTable table : schema.getDatabaseTables()) {
                String tblName = table.getName();
                // Only consider tables that appear in the FROM clause
                if (!fromTables.contains(tblName)) continue;

                // Collect PK columns for this table
                List<TiDBColumn> pkCols = new ArrayList<>();
                for (TiDBColumn col : table.getColumns()) {
                    if (col.isPrimaryKey()) pkCols.add(col);
                }
                if (pkCols.isEmpty()) continue;

                // Check if ALL PK columns are present in ORDER BY
                // (a single column from a composite PK is NOT a unique tie-breaker)
                boolean allPkCovered = true;
                boolean anyPkNullable = false;
                for (TiDBColumn pkCol : pkCols) {
                    String colName = pkCol.getName();
                    boolean found = false;
                    for (String obExpr : orderByCols) {
                        if (obExpr.equals(colName) || obExpr.equals(tblName + "." + colName)) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        allPkCovered = false;
                        break;
                    }
                    if (pkCol.isNullable() && columnHasNullValues(table, pkCol.getName())) {
                        anyPkNullable = true;
                    }
                }

                // Only return true if the complete PK is covered and no PK column has NULLs
                if (allPkCovered && !anyPkNullable) {
                    return true;
                }
            }
            return false;
        } catch (Exception e) {
            return false;
        }
    }

    // Conservatively returns true on query error (assumes nulls exist).
    private boolean columnHasNullValues(TiDBTable table, String columnName) {
        try {
            String checkQuery = "SELECT EXISTS(SELECT 1 FROM " + table.getName()
                    + " WHERE " + columnName + " IS NULL LIMIT 1) AS has_null;";
            List<String> result = ComparatorHelper.getResultSetAllColumnsAsString(
                    checkQuery, new ExpectedErrors(), globalState, " ||| ");
            return result == null || result.isEmpty() || !result.get(0).equals("0");
        } catch (Exception e) {
            return true;
        }
    }

    private boolean areSetsEqual(List<String> list1, List<String> list2) {
        Map<String, Integer> freq1 = new HashMap<>();
        Map<String, Integer> freq2 = new HashMap<>();
        for (String s : list1) freq1.merge(s, 1, Integer::sum);
        for (String s : list2) freq2.merge(s, 1, Integer::sum);
        return freq1.equals(freq2);
    }

    // ==================== EXPLAIN Plan Verification ====================

    // TiDB EXPLAIN columns: id | access_object | operator_info (estRows and task discarded).
    private List<String> getExplainPlan(String queryString) {
        List<String> plan = new ArrayList<>();
        try {
            String explainQuery = "EXPLAIN " + queryString;
            try (Statement stmt = globalState.getConnection().createStatement();
                 ResultSet rs = stmt.executeQuery(explainQuery)) {
                while (rs.next()) {
                    String id = rs.getString("id");
                    String accessObject = rs.getString("access_object");
                    String operatorInfo = rs.getString("operator_info");
                    plan.add(id + "|" + (accessObject != null ? accessObject : "") + "|" + (operatorInfo != null ? operatorInfo : ""));
                }
            }
        } catch (Exception e) {
            // EXPLAIN may fail for various reasons
        }
        return plan;
    }

    private boolean plansAreDifferent(List<String> plan1, List<String> plan2) {
        if (plan1.isEmpty() || plan2.isEmpty()) return true; // Can't verify, assume different
        if (plan1.size() != plan2.size()) return true;

        for (int i = 0; i < plan1.size(); i++) {
            String[] parts1 = plan1.get(i).split("\\|");
            String[] parts2 = plan2.get(i).split("\\|");
            String id1 = parts1.length > 0 ? parts1[0] : "";
            String id2 = parts2.length > 0 ? parts2[0] : "";
            String access1 = parts1.length > 1 ? parts1[1] : "";
            String access2 = parts2.length > 1 ? parts2[1] : "";

            if (!id1.equals(id2) || !access1.equals(access2)) {
                return true; // Plans differ
            }
        }
        return false; // Plans are identical
    }

    // TiDB's TableIndex may not expose column names; uses table:indexName as proxy.
    private Set<String> collectExistingIndexSignatures() {
        Set<String> sigs = new HashSet<>();
        try {
            for (TiDBTable table : globalState.getSchema().getDatabaseTables()) {
                for (TableIndex idx : table.getIndexes()) {
                    sigs.add(table.getName() + ":" + idx.getIndexName());
                }
            }
        } catch (Exception e) { }
        return sigs;
    }

    // ==================== Mode 14: Prefix Index (Enhanced) ====================

    // Mode 14: 0=LIKE prefix, 1=LEFT(), 2=SUBSTRING(), 3=range scan, 4=equality, 5=IS NOT NULL baseline.
    private void checkPrefixIndex() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Filter out views — cannot create indexes on views
        List<TiDBTable> nonViewTables = new ArrayList<>();
        for (TiDBTable t : tables) {
            if (!t.isView()) nonViewTables.add(t);
        }
        if (nonViewTables.isEmpty()) return;

        TiDBTable table = Randomly.fromList(nonViewTables);
        List<TiDBColumn> varCharCols = new ArrayList<>();
        for (TiDBColumn col : table.getColumns()) {
            String typeName = col.getType().toString().toUpperCase();
            if (typeName.contains("VARCHAR") || typeName.contains("TEXT")) {
                varCharCols.add(col);
            }
        }
        if (varCharCols.isEmpty()) return;

        TiDBColumn col = Randomly.fromList(varCharCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create a prefix index
        String idxName = "prefix_idx_" + Math.abs(colName.hashCode() % 10000);
        int prefixLen = Randomly.fromOptions(1, 2, 3, 5, 10);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " (" + colName + "(" + prefixLen + "));", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) {
            return;
        }

        // Get a PK column for ORDER BY determinism
        TiDBColumn pkCol = getPrimaryKeyColumn(table);
        String orderByClause = pkCol != null ? " ORDER BY " + pkCol.getName() : "";
        String limitClause = " LIMIT 100";

        // Sample a real value for prefix extraction
        List<String> sampled = sampleColumnValues(tblName, colName, 3);
        String prefix = null;
        if (sampled != null && !sampled.isEmpty()) {
            String rawVal = sampled.get(0).trim();
            // Strip surrounding quotes if present
            if (rawVal.startsWith("'") && rawVal.endsWith("'") && rawVal.length() >= 2) {
                rawVal = rawVal.substring(1, rawVal.length() - 1);
            }
            if (rawVal.length() > prefixLen) {
                prefix = rawVal.substring(0, prefixLen);
            } else {
                prefix = rawVal;
            }
            // Escape single quotes in prefix
            prefix = prefix.replace("'", "''");
        }

        // Empty prefix is useless for prefix index queries — fall back to IS NOT NULL strategy
        if (prefix != null && prefix.isEmpty()) {
            prefix = null;
        }

        int strategy = prefix != null ? Randomly.fromOptions(0, 1, 2, 3, 4, 5) : 5;
        String whereExpr;
        switch (strategy) {
        case 0:
            // LIKE prefix match — col LIKE 'abc%'
            whereExpr = colName + " LIKE '" + prefix + "%'";
            break;
        case 1:
            // LEFT function — LEFT(col, N) = 'val'
            whereExpr = "LEFT(" + colName + ", " + prefixLen + ") = '" + prefix + "'";
            break;
        case 2:
            // SUBSTRING function — SUBSTRING(col, 1, N) = 'val'
            whereExpr = "SUBSTRING(" + colName + ", 1, " + prefixLen + ") = '" + prefix + "'";
            break;
        case 3: {
            // Range scan — col >= 'prefix' AND col < 'prefixx' (next char after prefix)
            char nextChar = (char) (prefix.charAt(prefix.length() - 1) + 1);
            String prefixUpper = prefix.substring(0, prefix.length() - 1) + nextChar;
            whereExpr = colName + " >= '" + prefix + "' AND " + colName + " < '" + prefixUpper + "'";
            break;
        }
        case 4:
            // Equality on sampled value
            whereExpr = colName + " = '" + prefix + "'";
            break;
        default:
            // Original: IS NOT NULL
            whereExpr = colName + " IS NOT NULL";
            break;
        }

        // Build USE_INDEX vs IGNORE_INDEX queries
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + whereExpr + orderByClause + limitClause + ";";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + whereExpr + orderByClause + limitClause + ";";

        lastQueryString = "[PREFIX_IDX] strategy=" + strategy + " " + useQuery;

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, useQuery, "TIDB_PREFIX_IDX");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_PREFIX_IDX"); }
    }

    // ==================== Mode 15: Covering Index ====================

    private void checkCoveringIndex() throws Exception {
        // P0: Use indexable table (prioritize idx_t* tables, filter out BLOB/TEXT)
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;

        // P0: Only use indexable (non-TEXT/BLOB/JSON) columns
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.size() < 2) return;
        List<TiDBColumn> cols = new ArrayList<>(indexableCols);
        Collections.shuffle(cols);

        int numIdxCols = Math.min(cols.size(), Randomly.fromOptions(2, 3));
        List<TiDBColumn> idxCols = cols.subList(0, numIdxCols);
        String idxColList = idxCols.stream().map(TiDBColumn::getName).collect(Collectors.joining(", "));
        String tblName = table.getName();
        String idxName = "cover_idx_" + Math.abs(idxCols.get(0).getName().hashCode() % 10000);

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + idxColList + ");", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { return; }

        // SELECT only indexed columns
        String selectCols = idxCols.stream().map(TiDBColumn::getName).collect(Collectors.joining(", "));
        TiDBColumn whereCol = idxCols.get(0);
        // P1: Use sampled values instead of random values for better query hit rate
        String val;
        List<String> sampled = sampleColumnValues(tblName, whereCol.getName(), 3);
        if (sampled != null && !sampled.isEmpty()) {
            val = quoteValueForSQL(sampled.get(0), whereCol);
        } else {
            val = generateRandomValueForColumn(whereCol);
        }
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String queryString = "SELECT " + selectCols + " FROM " + tblName
                + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";
        lastQueryString = "[COVER_IDX] " + queryString;

        // Plan A: USE INDEX (IndexReader / covering)
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ " + selectCols
                + " FROM " + tblName + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";
        // Plan B: IGNORE INDEX (TableReader)
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ " + selectCols
                + " FROM " + tblName + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";

        // EXPLAIN filter
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_COVERING_INDEX");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_COVERING_INDEX"); }
    }

    // ==================== Mode 16: ORDER BY + LIMIT Index ====================

    private void checkOrderByLimitIndex() throws Exception {
        // P0: Use indexable table (prioritize idx_t* tables, filter out BLOB/TEXT)
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;

        // P0: Only use indexable (non-TEXT/BLOB/JSON) columns
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.isEmpty()) return;

        TiDBColumn col = Randomly.fromList(indexableCols);
        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "ordlim_idx_" + Math.abs(colName.hashCode() % 10000);

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { return; }

        int limit = Randomly.fromOptions(1, 5, 10, 20, 50);
        String direction = Randomly.fromOptions("ASC", "DESC");
        String whereClause = "";
        if (Randomly.getBoolean()) {
            // P1: Use sampled values instead of random values for better query hit rate
            String val;
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                val = quoteValueForSQL(sampled.get(0), col);
            } else {
                val = generateRandomValueForColumn(col);
            }
            String op = Randomly.fromOptions(">", "<", ">=", "<=", "!=");
            whereClause = " WHERE " + colName + " " + op + " " + val;
        }
        String queryString = "SELECT * FROM " + tblName + whereClause
                + " ORDER BY " + colName + " " + direction + " LIMIT " + limit + ";";
        lastQueryString = "[ORDLIM_IDX] " + queryString;

        // Plan A: USE INDEX (ordered index scan)
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM " + tblName
                + whereClause + " ORDER BY " + colName + " " + direction + " LIMIT " + limit + ";";
        // Plan B: IGNORE INDEX (table scan + sort)
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ * FROM " + tblName
                + whereClause + " ORDER BY " + colName + " " + direction + " LIMIT " + limit + ";";

        // EXPLAIN filter
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        // checkOrderByLimitIndex constructs ORDER BY on a single column with a non-unique
        // index (CREATE INDEX, not CREATE UNIQUE INDEX).  The column may have duplicate
        // values, so different execution plans (index scan vs table scan) can legitimately
        // break ORDER BY ties differently, producing different row orderings within tied
        // groups.  Use sorted (multiset) comparison so that:
        //   - Missing or extra rows (real bug) → sorted results differ → caught
        //   - Different tie-breaking order (not a bug) → sorted results match → passes
        // Always use assertResultSorted for LIMIT queries in this mode since the ORDER BY
        // column is non-unique by construction.
        lastCompareFiltered = false;
        if (queryString.toUpperCase().contains("LIMIT")) {
            assertResultSorted(r1, r2, queryString, "TIDB_ORDLIM_IDX");
        } else {
            assertResultStrict(r1, r2, queryString, "TIDB_ORDLIM_IDX");
        }
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_ORDLIM_IDX"); }
    }

    // ==================== Mode 17: Range Boundary ====================

    // Off-by-one errors in index range scans often miss boundary rows; tests MIN/MAX/BETWEEN edges.
    private void checkRangeBoundary() throws Exception {
        // P0: Use indexable table (prioritize idx_t* tables, filter out BLOB/TEXT)
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;

        // P0: Only use indexable (non-TEXT/BLOB/JSON) columns
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.isEmpty()) return;

        TiDBColumn col = Randomly.fromList(indexableCols);
        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "range_idx_" + Math.abs(colName.hashCode() % 10000);

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { return; }

        // Get MIN and MAX values for boundary testing
        String minVal = null, maxVal = null;
        try {
            List<String> minResult = execInternal("SELECT MIN(" + colName + ") FROM " + tblName + ";");
            if (minResult != null && !minResult.isEmpty()) minVal = minResult.get(0).trim();
            List<String> maxResult = execInternal("SELECT MAX(" + colName + ") FROM " + tblName + ";");
            if (maxResult != null && !maxResult.isEmpty()) maxVal = maxResult.get(0).trim();
        } catch (Exception e) { return; }
        if (minVal == null || maxVal == null || minVal.equals("NULL") || maxVal.equals("NULL")) return;

        // Fix: Quote minVal/maxVal for non-numeric types (VARCHAR, DATE, etc.)
        // to avoid SQL errors (e.g., unquoted DATE becomes arithmetic, unquoted VARCHAR is unknown column)
        String qMin = quoteValueForSQL(minVal, col);
        String qMax = quoteValueForSQL(maxVal, col);

        // Build boundary queries
        String queryString;
        int boundaryType = Randomly.fromOptions(0, 1, 2, 3);
        switch (boundaryType) {
        case 0:
            // col >= MIN(col) — should return all non-NULL rows
            queryString = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " >= " + qMin + ";";
            break;
        case 1:
            // col <= MAX(col) — should return all non-NULL rows
            queryString = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " <= " + qMax + ";";
            break;
        case 2:
            // col BETWEEN MIN AND MAX — should match all non-NULL rows
            queryString = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " BETWEEN " + qMin + " AND " + qMax + ";";
            break;
        default:
            // col = MIN OR col = MAX — boundary values
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " = " + qMin
                    + " OR " + colName + " = " + qMax + ";";
            break;
        }
        lastQueryString = "[RANGE_BOUNDARY] " + queryString;

        // Plan A: USE INDEX
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);
        // Plan B: IGNORE INDEX
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_RANGE_BOUNDARY");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_RANGE_BOUNDARY"); }
    }

    // ==================== Mode 18: READ_FROM_STORAGE(TIFLASH vs TIKV) ====================

    // TiDB: column store (TiFlash) vs row store (TiKV) must produce identical results; uses READ_FROM_STORAGE hint.
    private void checkTiFlashVsTiKV() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        TiDBTable table = Randomly.fromList(tables);
        String tblName = table.getName();
        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        // Generate a query — use simple column references for reliable comparison
        TiDBColumn col = Randomly.fromList(columns);
        StringBuilder sb = new StringBuilder();
        int queryType = Randomly.fromOptions(0, 1, 2, 3);
        switch (queryType) {
        case 0:
            sb.append("SELECT COUNT(*) FROM ").append(tblName);
            if (Randomly.getBoolean()) {
                sb.append(" WHERE ").append(col.getName()).append(" IS NOT NULL");
            }
            sb.append(";");
            break;
        case 1:
            sb.append("SELECT * FROM ").append(tblName);
            if (Randomly.getBoolean()) {
                List<String> sampled = sampleColumnValues(tblName, col.getName(), 3);
                if (sampled != null && !sampled.isEmpty()) {
                    sb.append(" WHERE ").append(col.getName()).append(" = ").append(quoteValueForSQL(sampled.get(0), col));
                } else {
                    sb.append(" WHERE ").append(col.getName()).append(" IS NOT NULL");
                }
            }
            sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1);
            sb.append(";");
            break;
        case 2:
            sb.append("SELECT ");
            String aggFunc = Randomly.fromOptions("COUNT", "SUM", "AVG", "MIN", "MAX");
            sb.append(aggFunc).append("(").append(col.getName()).append(") FROM ").append(tblName);
            sb.append(" WHERE ").append(col.getName()).append(" IS NOT NULL;");
            break;
        default:
            sb.append("SELECT ");
            int numCols = Math.min(columns.size(), 3);
            List<TiDBColumn> subset = Randomly.extractNrRandomColumns(columns, numCols);
            for (int i = 0; i < subset.size(); i++) {
                if (i > 0) sb.append(", ");
                sb.append(subset.get(i).getName());
            }
            sb.append(" FROM ").append(tblName);
            if (Randomly.getBoolean()) {
                sb.append(" WHERE ").append(col.getName()).append(" IS NOT NULL");
            }
            sb.append(" ORDER BY ").append(col.getName());
            sb.append(" LIMIT ").append(Randomly.getPositiveOrZeroNonCachedInteger() % 50 + 1);
            sb.append(";");
            break;
        }

        String queryString = sb.toString();
        lastQueryString = "[TIFLASH_VS_TIKV] " + queryString;

        // Plan A: Force TiFlash read (columnar storage)
        String tiFlashQuery = "SELECT /*+ READ_FROM_STORAGE(TIFLASH[" + tblName + "]) */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        // Plan B: Force TiKV read (row storage)
        String tiKVQuery = "SELECT /*+ READ_FROM_STORAGE(TIKV[" + tblName + "]) */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> r1 = null;
        try {
            r1 = exec(tiFlashQuery);
        } catch (Exception e) {
            // TiFlash may not be available — skip gracefully
            return;
        }
        if (r1 == null) return;

        List<String> r2 = exec(tiKVQuery);
        if (r2 == null) return;

        // Use sorted comparison since ORDER BY may not be unique
        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_TIFLASH_VS_TIKV");
        if (lastCompareFiltered) { countStarFallback(tiFlashQuery, tiKVQuery, "TIDB_TIFLASH_VS_TIKV"); }
    }

    // ==================== Mode 19: Expression Index ====================

    // TiDB expression index: CREATE INDEX ON t((expr)); double parens required (MySQL 8.0 compat, since ~v5.7).
    private void checkExpressionIndex() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Filter out views
        List<TiDBTable> nonViewTables = new ArrayList<>();
        for (TiDBTable t : tables) {
            if (!t.isView()) nonViewTables.add(t);
        }
        if (nonViewTables.isEmpty()) return;

        TiDBTable table = Randomly.fromList(nonViewTables);
        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        // Find VARCHAR/TEXT columns for expression index (LOWER, UPPER work on strings)
        List<TiDBColumn> stringCols = new ArrayList<>();
        for (TiDBColumn col : columns) {
            String typeName = col.getType().toString().toUpperCase();
            if (typeName.contains("CHAR") || typeName.contains("TEXT")) {
                stringCols.add(col);
            }
        }
        // Also consider INT columns (ABS(col), col+1, etc.)
        List<TiDBColumn> intCols = new ArrayList<>();
        for (TiDBColumn col : columns) {
            String typeName = col.getType().toString().toUpperCase();
            if (typeName.contains("INT")) {
                intCols.add(col);
            }
        }

        String tblName = table.getName();
        String idxName = "expr_idx_" + Math.abs(globalState.getRandomly().getInteger() % 10000);
        String expression;
        String whereExpr;

        if (!stringCols.isEmpty() && Randomly.getBoolean()) {
            // String expression: LOWER(col) or UPPER(col)
            TiDBColumn col = Randomly.fromList(stringCols);
            String func = Randomly.fromOptions("LOWER", "UPPER");
            expression = func + "(" + col.getName() + ")";
            whereExpr = func + "(" + col.getName() + ")";
        } else if (!intCols.isEmpty()) {
            // Integer expression: ABS(col) or col + 0
            TiDBColumn col = Randomly.fromList(intCols);
            String func = Randomly.fromOptions("ABS", "");
            if (func.isEmpty()) {
                expression = col.getName() + " + 0";
                whereExpr = col.getName() + " + 0";
            } else {
                expression = func + "(" + col.getName() + ")";
                whereExpr = func + "(" + col.getName() + ")";
            }
        } else {
            return;
        }

        // Create expression index
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " ((" + expression + "));", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) {
            return;
        }

        // Query using the expression in WHERE
        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereExpr + " IS NOT NULL LIMIT 50;";
        lastQueryString = "[EXPR_IDX] " + queryString;

        // Plan A: USE INDEX (force expression index scan)
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + whereExpr + " IS NOT NULL LIMIT 50;";
        // Plan B: IGNORE INDEX (table scan)
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + whereExpr + " IS NOT NULL LIMIT 50;";

        // EXPLAIN filter
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_EXPRESSION_INDEX");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_EXPRESSION_INDEX"); }
    }

    // ==================== Mode 20: ICP Consistency ====================

    private void checkICPConsistency() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        TiDBTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        List<TableIndex> indexes = table.getIndexes();
        if (indexes.isEmpty()) return;

        String tblName = table.getName();
        TiDBColumn col = Randomly.fromList(table.getColumns());
        TiDBConstant val = generateDataAwareConstant(table, col);
        String op = Randomly.fromOptions(">", ">=", "<", "<=", "=");

        String baseQuery = "SELECT COUNT(*) FROM " + tblName
                + " WHERE " + col.getName() + " " + op + " " + val + ";";
        lastQueryString = "[ICP_TEST] " + baseQuery;
        log(baseQuery);

        List<String> r1 = exec(baseQuery);
        if (r1 == null) return;

        // Expanded optimizer switches — 21 switches covering join, index, subquery,
        // agg, scan, and additional TiDB-specific optimizer paths.
        String setOff = Randomly.fromOptions(
                // Join related
                "SET SESSION tidb_enable_inl_join_inner=0;",
                "SET SESSION tidb_enable_index_merge_join=0;",
                "SET SESSION tidb_enable_inl_join=0;",
                // Index related
                "SET SESSION tidb_enable_index_merge=0;",
                "SET SESSION tidb_enable_index_fast_plan=0;",
                // Subquery related
                "SET SESSION tidb_opt_insubq_to_join_and_agg=0;",
                "SET SESSION tidb_opt_enable_correlation_adjustment=0;",
                // Aggregation related
                "SET SESSION tidb_opt_agg_push_down=1;",
                // Optimizer related
                "SET SESSION tidb_enable_cascades_planner=1;",
                "SET SESSION tidb_opt_prefer_range_scan=1;",
                "SET SESSION tidb_opt_enable_hash_join=0;",
                // Scan related
                "SET SESSION tidb_enable_late_materialization=0;",
                "SET SESSION tidb_enable_ordered_index_mode=0;",
                // Additional optimizer switches for broader bug coverage
                "SET SESSION tidb_opt_prefix_index_single_scan=0;",   // Prefix index scan strategy
                "SET SESSION tidb_enable_parallel_apply=1;",           // Parallel Apply execution
                "SET SESSION tidb_opt_enable_hash_agg=0;",             // Disable Hash Agg (fallback to Stream Agg)
                "SET SESSION tidb_enable_ordered_index_mode=1;",       // Force ordered index mode ON
                "SET SESSION tidb_opt_derive_topn=0;",                 // Disable TOPN derivation
                "SET SESSION tidb_enable_index_adaptive_news=0;",      // Disable adaptive index selection
                // Combination switches (test interaction effects)
                "SET SESSION tidb_enable_inl_join=0; SET SESSION tidb_enable_index_merge=0;",
                "SET SESSION tidb_opt_prefer_range_scan=1; SET SESSION tidb_enable_index_merge=0;");
        // Fix: use semicolon-anchored replacement to avoid no-op chain
        // (".replace("=0","=1").replace("=1","=0")" is a no-op since the
        // first replace creates "=1" which the second replace flips back)
        String setOn;
        if (setOff.contains("=0;")) {
            setOn = setOff.replace("=0;", "=1;");
        } else {
            setOn = setOff.replace("=1;", "=0;");
        }
        // Fix: save original session variable values and restore to them (not just flip)
        String savedState = saveSessionVariables(setOff);
        try {
            globalState.executeStatement(new SQLQueryAdapter(setOff, errors, true));
        } catch (Throwable t) { return; }
        List<String> r2 = null;
        try { r2 = exec(baseQuery); } finally {
            try { restoreSessionVariables(savedState); } catch (Throwable t) {}
        }
        if (r2 == null) return;
        assertResultSorted(r1, r2, baseQuery, "TIDB_ICP");
    }

    // ==================== Mode 21: DELETED (merged into Mode 20 checkICPConsistency) ====================

    // ==================== Mode 22: SQL Semantic Equivalence ====================

    private void checkSQLSemanticEquivalence() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        TiDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        TiDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        String idxName = "seq_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) { }

        TiDBConstant val1 = generateDataAwareConstant(table, col);
        TiDBConstant val2 = generateDataAwareConstant(table, col);
        TiDBConstant val3 = generateDataAwareConstant(table, col);

        int variant = Randomly.fromOptions(0, 1, 2, 3, 4);
        String queryA, queryB, modeTag;
        switch (variant) {
        case 0:
            queryA = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " IN (" + val1 + ", " + val2 + ", " + val3 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " = " + val1 + " OR " + colName + " = " + val2
                    + " OR " + colName + " = " + val3 + ";";
            modeTag = "TIDB_SEMANTIC_IN_VS_OR";
            break;
        case 1:
            queryA = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " BETWEEN " + val1 + " AND " + val2 + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " >= " + val1 + " AND " + colName + " <= " + val2 + ";";
            modeTag = "TIDB_SEMANTIC_BETWEEN";
            break;
        case 2:
            // Fix: add IS NOT NULL to avoid NULL semantics mismatch between NOT IN and <> 
            // (NOT IN returns UNKNOWN for NULL, <> returns TRUE for NULL compared to non-NULL values)
            queryA = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " IS NOT NULL AND " + colName + " NOT IN (" + val1 + ", " + val2 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " IS NOT NULL AND " + colName + " <> " + val1 + " AND " + colName + " <> " + val2 + ";";
            modeTag = "TIDB_SEMANTIC_NOT_IN";
            break;
        case 3:
            // IN vs UNION ALL (UNION ALL preserves all rows; sum of individual counts
            // equals IN count when val1 != val2, and even when val1 == val2 both sides
            // count the same rows so the semantics remain correct)
            queryA = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " IN (" + val1 + ", " + val2 + ");";
            queryB = "SELECT COUNT(*) FROM ("
                    + "SELECT " + colName + " FROM " + tblName + " USE INDEX(" + idxName + ") WHERE " + colName + " = " + val1
                    + " UNION ALL "
                    + "SELECT " + colName + " FROM " + tblName + " USE INDEX(" + idxName + ") WHERE " + colName + " = " + val2
                    + ") t;";
            modeTag = "TIDB_SEMANTIC_IN_VS_UNION";
            break;
        default:
            // EXISTS vs JOIN — fallback to BETWEEN if only 1 table
            if (schema.getDatabaseTables().size() >= 2) {
                TiDBTable table2 = Randomly.fromList(schema.getDatabaseTables());
                if (!table2.getColumns().isEmpty() && !table2.getName().equals(tblName)) {
                    TiDBColumn col2 = Randomly.fromList(table2.getColumns());
                    queryA = "SELECT COUNT(*) FROM " + tblName + " t1"
                            + " WHERE EXISTS (SELECT 1 FROM " + table2.getName() + " t2 WHERE t1." + colName + " = t2." + col2.getName() + ");";
                    queryB = "SELECT COUNT(*) FROM " + tblName + " t1"
                            + " WHERE " + colName + " IN (SELECT " + col2.getName() + " FROM " + table2.getName() + ");";
                    modeTag = "TIDB_SEMANTIC_EXISTS_VS_JOIN";
                    break;
                }
            }
            queryA = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " BETWEEN " + val1 + " AND " + val2 + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " >= " + val1 + " AND " + colName + " <= " + val2 + ";";
            modeTag = "TIDB_SEMANTIC_BETWEEN";
            break;
        }

        lastQueryString = "[SEMANTIC_EQ] A=" + queryA + " B=" + queryB;
        log(queryA); log(queryB);

        List<String> r1 = exec(queryA);
        if (r1 == null) return;
        List<String> r2 = exec(queryB);
        if (r2 == null) return;
        assertResultSorted(r1, r2, queryA, modeTag);
    }

    // ==================== Mode 23: Deterministic Index Query (P4) ====================

    private TiDBColumn getPrimaryKeyColumn(TiDBTable table) {
        for (TiDBColumn col : table.getColumns()) {
            if (col.isPrimaryKey()) return col;
        }
        return null;
    }

    // FIX: WHERE on indexed col (not PK) makes USE_INDEX hint effective; PK-in-WHERE caused optimizer to always prefer PK index.
    private String buildDeterministicASTQuery(TiDBTable table, TiDBColumn pkCol,
            TableIndex targetIdx, TiDBColumn idxCol, String idxVal) {
        try {
            List<TiDBColumn> columns = table.getColumns();
            if (columns.isEmpty()) return null;

            TiDBExpressionGenerator gen = new TiDBExpressionGenerator(globalState).setColumns(columns);
            TiDBSelect select = new TiDBSelect();

            // SELECT: pick some columns, always include PK
            List<TiDBExpression> fetchColumns = new ArrayList<>();
            fetchColumns.add(new TiDBColumnReference(pkCol));
            List<TiDBColumn> subset = Randomly.nonEmptySubset(columns);
            for (TiDBColumn col : subset) {
                if (!col.getName().equals(pkCol.getName())) {
                    fetchColumns.add(new TiDBColumnReference(col));
                }
            }
            select.setFetchColumns(fetchColumns);

            // FROM with USE INDEX hint
            List<TiDBExpression> fromList = new ArrayList<>();
            fromList.add(new TiDBTableReference(table));
            select.setFromList(fromList);

            // WHERE: anchor on indexed column + add complex AST conditions
            TiDBExpression idxCondition = buildIndexAnchorCondition(idxCol, idxVal);
            TiDBExpression extraCondition = gen.generateExpression();
            TiDBExpression combinedWhere = new idxdiff.tidb.ast.TiDBBinaryLogicalOperation(idxCondition, extraCondition,
                    idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator.AND);
            select.setWhereClause(combinedWhere);

            // ORDER BY PK — always, for deterministic ordering
            List<TiDBExpression> orderBy = new ArrayList<>();
            orderBy.add(new TiDBColumnReference(pkCol));
            select.setOrderByClauses(orderBy);

            // LIMIT
            select.setLimitClause(TiDBConstant.createIntConstant(
                    Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));

            String baseQuery = TiDBVisitor.asString(select) + ";";

            // Inject USE INDEX hint after FROM clause
            String tblName = table.getName();
            String idxName = targetIdx.getIndexName();
            String fromClause = "FROM " + tblName;
            baseQuery = baseQuery.replace(fromClause, fromClause + " USE INDEX(" + idxName + ")");

            return baseQuery;
        } catch (Exception e) {
            return null;
        }
    }

    private TiDBExpression buildIndexAnchorCondition(TiDBColumn idxCol, String idxVal) {
        TiDBExpression colRef = new TiDBColumnReference(idxCol);
        TiDBExpression valConst = TiDBConstant.createStringConstant(idxVal);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator cmpOp;
        switch (op) {
        case ">": cmpOp = idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER; break;
        case "<": cmpOp = idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER; break;
        case ">=": cmpOp = idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.GREATER_EQUALS; break;
        case "<=": cmpOp = idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.SMALLER_EQUALS; break;
        default: cmpOp = idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator.EQUALS; break;
        }
        return new idxdiff.tidb.ast.TiDBBinaryComparisonOperation(colRef, valConst, cmpOp);
    }

    private String buildDeterministicQuery(TiDBTable table, TiDBColumn pkCol,
            TableIndex targetIdx, TiDBColumn idxCol, String idxVal) {
        String tblName = table.getName();
        String pkColName = pkCol.getName();
        String idxColName = idxCol.getName();
        String idxName = targetIdx.getIndexName();

        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String query;
        int variant = Randomly.fromOptions(0, 1, 2);
        switch (variant) {
        case 0:
            // SELECT * with WHERE on indexed col, ORDER BY PK for deterministic order
            query = "SELECT * FROM " + tblName + " USE INDEX(" + idxName
                    + ") WHERE " + idxColName + " " + op + " " + idxVal
                    + " ORDER BY " + pkColName + " LIMIT 100;";
            break;
        case 1:
            // COUNT(*) — deterministic regardless of ordering
            query = "SELECT COUNT(*) FROM " + tblName + " USE INDEX(" + idxName
                    + ") WHERE " + idxColName + " " + op + " " + idxVal + ";";
            break;
        default:
            // SELECT * with range + LIMIT, ORDER BY PK
            query = "SELECT * FROM " + tblName + " USE INDEX(" + idxName
                    + ") WHERE " + idxColName + " " + op + " " + idxVal
                    + " ORDER BY " + pkColName + " LIMIT 50;";
            break;
        }
        return query;
    }

    // FIX: WHERE on indexed col (not PK); PK-in-WHERE made USE_INDEX(non-PK) ineffective (optimizer always picks PK index).
    private void checkDeterministicIndexQuery() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        TiDBTable table = Randomly.fromList(tables);
        TiDBColumn pkCol = getPrimaryKeyColumn(table);
        if (pkCol == null) return;

        String tblName = table.getName();

        // Ensure at least one non-PK index exists
        List<TableIndex> indexes = table.getIndexes();
        boolean hasNonPK = false;
        for (TableIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY")) { hasNonPK = true; break; }
        }
        if (!hasNonPK) {
            try {
                SQLQueryAdapter createIndex = TiDBIndexGenerator.getQuery(globalState);
                globalState.executeStatement(createIndex);
                tablesNeedingAnalyze.add(table.getName());
                indexes = table.getIndexes();
                for (TableIndex idx : indexes) {
                    if (!idx.getIndexName().equals("PRIMARY")) { hasNonPK = true; break; }
                }
            } catch (Exception e) { return; }
        }
        if (!hasNonPK) return;

        // FIX: Find a non-PK index and its indexed columns
        List<TableIndex> nonPKIndexes = new ArrayList<>();
        for (TableIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY")) {
                nonPKIndexes.add(idx);
            }
        }
        TableIndex targetIdx = Randomly.fromList(nonPKIndexes);

        // Get the columns covered by this index from information_schema
        List<TiDBColumn> idxCols = getIndexColumnsFromSchema(table, targetIdx.getIndexName());
        if (idxCols == null || idxCols.isEmpty()) {
            // Fallback: use any non-PK indexable column
            List<TiDBColumn> indexableCols = getIndexableColumns(table);
            idxCols = new ArrayList<>();
            for (TiDBColumn c : indexableCols) {
                if (!c.isPrimaryKey()) idxCols.add(c);
            }
        }
        if (idxCols.isEmpty()) return;

        // FIX: Use an indexed column in WHERE (not PK)
        TiDBColumn idxCol = Randomly.fromList(idxCols);
        List<String> sampledVals = sampleColumnValues(tblName, idxCol.getName(), 5);
        if (sampledVals == null || sampledVals.isEmpty()) return;
        String rawVal = Randomly.fromList(sampledVals);
        String idxVal = quoteValueForSQL(rawVal, idxCol);

        // AST混合策略: randomly choose between string-based and AST-based query generation
        // String path (buildDeterministicQuery): simple templates — high reliability, covers basic index operations
        // AST path (buildDeterministicASTQuery): complex WHERE via TiDBExpressionGenerator — tests optimizer
        // expression evaluation, function pushdown, and nested boolean conditions under different index plans
        boolean useAST = Randomly.getBooleanWithRatherLowProbability(); // ~20% AST
        String queryA;
        if (useAST) {
            queryA = buildDeterministicASTQuery(table, pkCol, targetIdx, idxCol, rawVal);
        } else {
            queryA = buildDeterministicQuery(table, pkCol, targetIdx, idxCol, idxVal);
        }
        if (queryA == null) return;

        // Build query B (no index hint, default plan)
        String queryB = queryA.replaceAll(" USE INDEX\\([^)]+\\)", "");

        // EXPLAIN filter
        List<String> planA = getExplainPlan(queryA);
        List<String> planB = getExplainPlan(queryB);
        if (!plansAreDifferent(planA, planB)) return;

        lastQueryString = "[DET_IDX] A=" + queryA + " B=" + queryB;
        log(queryA);
        log(queryB);

        List<String> r1 = exec(queryA);
        if (r1 == null) return;
        List<String> r2 = exec(queryB);
        if (r2 == null) return;

        // Strict comparison: PK in ORDER BY guarantees deterministic order
        assertResultSorted(r1, r2, queryA, "TIDB_DET_IDX");
    }

    private List<TiDBColumn> getIndexColumnsFromSchema(TiDBTable table, String indexName) {
        List<TiDBColumn> cols = new ArrayList<>();
        try {
            String query = "SELECT COLUMN_NAME FROM information_schema.STATISTICS WHERE TABLE_SCHEMA = DATABASE()"
                    + " AND TABLE_NAME = '" + table.getName() + "'"
                    + " AND INDEX_NAME = '" + indexName + "' ORDER BY SEQ_IN_INDEX;";
            List<String> result = execInternal(query);
            if (result != null) {
                for (String colName : result) {
                    String trimmed = colName.trim();
                    for (TiDBColumn col : table.getColumns()) {
                        if (col.getName().equals(trimmed)) {
                            if (!cols.contains(col)) {
                                cols.add(col);
                            }
                            break;
                        }
                    }
                }
            }
        } catch (Exception e) { }
        return cols;
    }

    // ==================== Index-Friendly Infrastructure ====================

    // TiDB vs Postgres: no INCLUDE/partial index/expression index in CREATE INDEX; INSERT IGNORE not ON CONFLICT; ANALYZE TABLE.
    private void createIndexFriendlyTables() {
        ExpectedErrors tableErrors = new ExpectedErrors();
        tableErrors.add("already exists");
        tableErrors.add("Duplicate key name");
        tableErrors.add("index already exist");
        tableErrors.add("Specified key was too long");
        tableErrors.add("BLOB or TEXT");
        tableErrors.add("used in key specification");
        tableErrors.add("Too many keys specified");

        // Check if index-friendly tables already exist
        try {
            TiDBSchema schema = globalState.getSchema();
            boolean hasIdxTable = false;
            for (TiDBTable t : schema.getDatabaseTables()) {
                if (t.getName().startsWith("idx_")) {
                    hasIdxTable = true;
                    break;
                }
            }
            if (hasIdxTable) return; // Already created in a previous iteration
        } catch (Exception e) { return; }

        // P3#6: Create 2-3 index-friendly tables with diverse column types
        // Table 0: INT + VARCHAR (original, proven effective)
        // Table 1: INT + DECIMAL + DATE (tests DECIMAL precision and DATE range indexes)
        // Table 2 (optional): INT + VARCHAR + FLOAT (tests FLOAT index approximation)
        int numTables = Randomly.fromOptions(2, 2, 3);
        for (int t = 0; t < numTables; t++) {
            String tableName = "idx_t" + t;
            try {
                StringBuilder createSQL = new StringBuilder();
                createSQL.append("CREATE TABLE IF NOT EXISTS ").append(tableName).append(" (");

                // Data generation helpers for batch inserts (built per table type)
                final String[] insertColExprs; // SQL expressions for each column in INSERT

                if (t == 0) {
                    // Table 0: INT + VARCHAR — proven effective for general index testing
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 INT NOT NULL, ");
                    createSQL.append("c2 INT, "); // nullable for NULL boundary testing
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 INT NOT NULL, ");
                    createSQL.append("c5 VARCHAR(64) NOT NULL, ");
                    createSQL.append("c6 VARCHAR(64), "); // nullable
                    createSQL.append("c7 VARCHAR(64) NOT NULL");
                    createSQL.append(");");
                    insertColExprs = null; // will use legacy inline generation below
                } else if (t == 1) {
                    // Table 1 (P3#6): INT + DECIMAL + DATE — tests DECIMAL precision and DATE range indexes
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 DECIMAL(10,2) NOT NULL, "); // DECIMAL for precision index testing
                    createSQL.append("c2 DATE NOT NULL, ");           // DATE for range scan testing
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 DECIMAL(10,4), ");           // nullable DECIMAL
                    createSQL.append("c5 VARCHAR(64) NOT NULL, ");
                    createSQL.append("c6 DATE, ");                    // nullable DATE
                    createSQL.append("c7 INT NOT NULL");
                    createSQL.append(");");
                    insertColExprs = null; // will use legacy inline generation below
                } else {
                    // Table 2 (P3#6): INT + VARCHAR + FLOAT — tests FLOAT index approximation
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 FLOAT NOT NULL, ");          // FLOAT for approximate index testing
                    createSQL.append("c2 VARCHAR(64), ");             // nullable VARCHAR
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 FLOAT, ");                   // nullable FLOAT
                    createSQL.append("c5 VARCHAR(64) NOT NULL, ");
                    createSQL.append("c6 INT, ");                     // nullable INT
                    createSQL.append("c7 FLOAT NOT NULL");
                    createSQL.append(");");
                    insertColExprs = null; // will use legacy inline generation below
                }
                globalState.executeStatement(new SQLQueryAdapter(createSQL.toString(), tableErrors, true));

                // Pre-build diverse indexes on this table — adapt per table type
                List<String> indexStmtsList = new ArrayList<>();
                if (t == 0) {
                    // Table 0: original indexes (INT + VARCHAR focused)
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c1c3 ON " + tableName + " (c0, c1, c3);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c5 ON " + tableName + " (c5);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0desc ON " + tableName + " (c0 DESC);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c2 ON " + tableName + " (c2);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0asc1desc ON " + tableName + " (c0 ASC, c1 DESC);");
                } else if (t == 1) {
                    // Table 1 (P3#6): DECIMAL + DATE indexes
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c1 ON " + tableName + " (c1);");           // DECIMAL index
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c2 ON " + tableName + " (c2);");           // DATE index
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");    // INT + DECIMAL composite
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c2 ON " + tableName + " (c0, c2);");    // INT + DATE composite
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c2desc ON " + tableName + " (c2 DESC);"); // DATE DESC
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c4 ON " + tableName + " (c4);");           // nullable DECIMAL
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c6 ON " + tableName + " (c6);");           // nullable DATE
                } else {
                    // Table 2 (P3#6): FLOAT indexes
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c1 ON " + tableName + " (c1);");           // FLOAT index
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");    // INT + FLOAT composite
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c5 ON " + tableName + " (c5);");           // VARCHAR index
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c1desc ON " + tableName + " (c1 DESC);"); // FLOAT DESC
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c4 ON " + tableName + " (c4);");           // nullable FLOAT
                    indexStmtsList.add("CREATE INDEX IF NOT EXISTS idx_" + t + "_c7 ON " + tableName + " (c7);");           // FLOAT index
                }

                for (String idxSQL : indexStmtsList) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(idxSQL, tableErrors, true));
                    } catch (Exception e) { }
                }

                // Insert initial data (200 rows) using type-aware generation
                ExpectedErrors insertErrors = new ExpectedErrors();
                TiDBErrors.addInsertErrors(insertErrors);
                Randomly r = globalState.getRandomly();

                for (int batch = 0; batch < 4; batch++) {
                    StringBuilder insertSQL = new StringBuilder();
                    insertSQL.append("INSERT IGNORE INTO ").append(tableName).append(" VALUES ");
                    for (int row = 0; row < 50; row++) {
                        if (row > 0) insertSQL.append(", ");
                        insertSQL.append("(");
                        if (t == 0) {
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c0 INT
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c1 INT
                            insertSQL.append(Randomly.getBoolean() ? String.valueOf(r.getInteger() % 255) : "NULL").append(", ");  // c2 INT nullable
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c3 INT
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c4 INT
                            insertSQL.append("'").append(r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length()))).append("', ");  // c5 VARCHAR
                            insertSQL.append(Randomly.getBoolean() ? "'" + r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length())) + "'" : "NULL").append(", ");  // c6 VARCHAR nullable
                            insertSQL.append("'").append(r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length()))).append("'");  // c7 VARCHAR
                        } else if (t == 1) {
                            // P3#6: INT + DECIMAL + DATE data generation
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c0 INT
                            insertSQL.append(Math.abs(r.getInteger() % 100000) / 100.0).append(", ");  // c1 DECIMAL(10,2)
                            String[] dates = {"2020-01-01", "2021-06-15", "2022-12-31", "2023-03-15", "2024-07-20", "2019-09-10"};
                            insertSQL.append("'").append(dates[(int)(Math.abs(r.getInteger()) % dates.length)]).append("', ");  // c2 DATE
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c3 INT
                            insertSQL.append(Randomly.getBoolean() ? String.valueOf(Math.abs(r.getInteger() % 100000) / 10000.0) : "NULL").append(", ");  // c4 DECIMAL nullable
                            insertSQL.append("'").append(r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length()))).append("', ");  // c5 VARCHAR
                            insertSQL.append(Randomly.getBoolean() ? "'" + dates[(int)(Math.abs(r.getInteger()) % dates.length)] + "'" : "NULL").append(", ");  // c6 DATE nullable
                            insertSQL.append(r.getInteger() % 255);  // c7 INT
                        } else {
                            // P3#6: INT + VARCHAR + FLOAT data generation
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c0 INT
                            double f1 = Math.abs(r.getInteger() % 10000) / 10.0;
                            insertSQL.append(f1).append(", ");  // c1 FLOAT
                            insertSQL.append(Randomly.getBoolean() ? "'" + r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length())) + "'" : "NULL").append(", ");  // c2 VARCHAR nullable
                            insertSQL.append(r.getInteger() % 255).append(", ");  // c3 INT
                            insertSQL.append(Randomly.getBoolean() ? String.valueOf(Math.abs(r.getInteger() % 10000) / 10.0) : "NULL").append(", ");  // c4 FLOAT nullable
                            insertSQL.append("'").append(r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length()))).append("', ");  // c5 VARCHAR
                            insertSQL.append(Randomly.getBoolean() ? String.valueOf(r.getInteger() % 255) : "NULL").append(", ");  // c6 INT nullable
                            double f7 = Math.abs(r.getInteger() % 10000) / 10.0;
                            insertSQL.append(f7);  // c7 FLOAT
                        }
                        insertSQL.append(")");
                    }
                    insertSQL.append(";");
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(insertSQL.toString(), insertErrors, true));
                    } catch (Exception e) { }
                }

                // Analyze — defer to batched analyzeAllTables()
                tablesNeedingAnalyze.add(tableName);
            } catch (Exception e) {
                // Table/index creation may fail, ignore
            }
        }
    }

    // Returns null if no indexed cols; string-based generation (not AST) since TiDB generateQuery() is string-based.
    private String tryGenerateIndexFriendlyWhere(TiDBTable table, List<TiDBColumn> columns) {
        if (columns.isEmpty()) return null;

        try {
            // Step 1: Collect index information from information_schema
            List<TiDBColumn> indexedCols = getIndexedColumnsForTable(table);
            List<List<TiDBColumn>> compositeIdxCols = getCompositeIndexGroups(table);
            List<TiDBColumn> singleIdxCols = new ArrayList<>();
            for (TiDBColumn ic : indexedCols) {
                boolean inComposite = false;
                for (List<TiDBColumn> group : compositeIdxCols) {
                    if (group.contains(ic)) { inComposite = true; break; }
                }
                if (!inComposite) singleIdxCols.add(ic);
            }

            Randomly r = globalState.getRandomly();

            // Step 2: Choose strategy
            int strategy;
            if (!compositeIdxCols.isEmpty() && singleIdxCols.size() >= 2 && Randomly.getBoolean()) {
                strategy = r.getInteger(0, 5);
            } else if (!compositeIdxCols.isEmpty()) {
                strategy = r.getInteger(0, 3);
            } else if (indexedCols.size() >= 2) {
                strategy = Randomly.fromOptions(0, 2);
            } else if (!indexedCols.isEmpty()) {
                strategy = 0;
            } else {
                return null;
            }

            switch (strategy) {
            case 0: return generateIndexFriendlyEquality(table, indexedCols, columns);
            case 1: return generateIndexFriendlyCompositePrefix(table, compositeIdxCols);
            case 2: return generateIndexFriendlyMultiColumn(table, indexedCols, columns);
            case 3: return generateIndexFriendlyRange(table, indexedCols, columns);
            case 4: return generateIndexFriendlyMerge(table, indexedCols);
            default: return generateIndexFriendlyCompositePrefix(table, compositeIdxCols);
            }
        } catch (Exception e) {
            return null;
        }
    }

    // Triggers index ref lookup (equality on indexed column).
    private String generateIndexFriendlyEquality(TiDBTable table, List<TiDBColumn> indexedCols, List<TiDBColumn> fallbackCols) {
        TiDBColumn col = !indexedCols.isEmpty() ? Randomly.fromList(indexedCols) : Randomly.fromList(fallbackCols);
        List<String> sampled = sampleColumnValues(table.getName(), col.getName(), 5);
        if (sampled != null && !sampled.isEmpty()) {
            return col.getName() + " = " + quoteValueForSQL(sampled.get(0), col);
        }
        return col.getName() + " = " + generateRandomValueForColumn(col);
    }

    // Triggers composite index range scan (prefix condition).
    private String generateIndexFriendlyCompositePrefix(TiDBTable table, List<List<TiDBColumn>> compositeIdxCols) {
        if (compositeIdxCols.isEmpty()) return null;
        List<TiDBColumn> idxCols = Randomly.fromList(compositeIdxCols);
        int prefixLen = Math.min(idxCols.size(), globalState.getRandomly().getInteger(1, 4));
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < prefixLen; i++) {
            TiDBColumn col = idxCols.get(i);
            if (i > 0) sb.append(" AND ");
            List<String> sampled = sampleColumnValues(table.getName(), col.getName(), 3);
            if (i == 0) {
                // First column: equality for best selectivity
                if (sampled != null && !sampled.isEmpty()) {
                    sb.append(col.getName()).append(" = ").append(quoteValueForSQL(sampled.get(0), col));
                } else {
                    sb.append(col.getName()).append(" = ").append(generateRandomValueForColumn(col));
                }
            } else if (i == prefixLen - 1 && Randomly.getBoolean()) {
                // Last column: range
                String op = Randomly.fromOptions(" >= ", " <= ");
                if (sampled != null && !sampled.isEmpty()) {
                    sb.append(col.getName()).append(op).append(quoteValueForSQL(sampled.get(0), col));
                } else {
                    sb.append(col.getName()).append(" IS NOT NULL");
                }
            } else {
                // Middle columns: equality or comparison
                String op = Randomly.fromOptions(" = ", " >= ", " <= ");
                if (sampled != null && !sampled.isEmpty()) {
                    sb.append(col.getName()).append(op).append(quoteValueForSQL(sampled.get(0), col));
                } else {
                    sb.append(col.getName()).append(" IS NOT NULL");
                }
            }
        }
        return sb.toString();
    }

    private String generateIndexFriendlyMultiColumn(TiDBTable table, List<TiDBColumn> indexedCols, List<TiDBColumn> fallbackCols) {
        List<TiDBColumn> cols = !indexedCols.isEmpty() ? indexedCols : fallbackCols;
        if (cols.size() < 2) return null;
        Collections.shuffle(cols);
        TiDBColumn col1 = cols.get(0);
        TiDBColumn col2 = cols.get(1);

        List<String> sampled1 = sampleColumnValues(table.getName(), col1.getName(), 3);
        StringBuilder sb = new StringBuilder();
        if (sampled1 != null && !sampled1.isEmpty()) {
            sb.append(col1.getName()).append(" = ").append(quoteValueForSQL(sampled1.get(0), col1));
        } else {
            sb.append(col1.getName()).append(" IS NOT NULL");
        }

        sb.append(" AND ");
        List<String> sampled2 = sampleColumnValues(table.getName(), col2.getName(), 3);
        String op = Randomly.fromOptions(" >= ", " <= ", " > ", " < ");
        if (sampled2 != null && !sampled2.isEmpty()) {
            sb.append(col2.getName()).append(op).append(quoteValueForSQL(sampled2.get(0), col2));
        } else {
            sb.append(col2.getName()).append(" IS NOT NULL");
        }
        return sb.toString();
    }

    // Triggers index range scan (range condition on indexed column).
    private String generateIndexFriendlyRange(TiDBTable table, List<TiDBColumn> indexedCols, List<TiDBColumn> fallbackCols) {
        TiDBColumn col = !indexedCols.isEmpty() ? Randomly.fromList(indexedCols) : Randomly.fromList(fallbackCols);
        List<String> sampled = sampleColumnValues(table.getName(), col.getName(), 5);
        if (sampled != null && sampled.size() >= 2) {
            return col.getName() + " >= " + quoteValueForSQL(sampled.get(0), col)
                    + " AND " + col.getName() + " <= " + quoteValueForSQL(sampled.get(1), col);
        }
        return col.getName() + " IS NOT NULL";
    }

    // OR across different indexed cols triggers TiDB IndexMerge.
    private String generateIndexFriendlyMerge(TiDBTable table, List<TiDBColumn> indexedCols) {
        if (indexedCols.size() < 2) return null;
        Collections.shuffle(indexedCols);
        TiDBColumn col1 = indexedCols.get(0);
        TiDBColumn col2 = indexedCols.get(1);

        List<String> sampled1 = sampleColumnValues(table.getName(), col1.getName(), 3);
        List<String> sampled2 = sampleColumnValues(table.getName(), col2.getName(), 3);

        StringBuilder sb = new StringBuilder();
        sb.append("(");
        if (sampled1 != null && !sampled1.isEmpty()) {
            sb.append(col1.getName()).append(" = ").append(quoteValueForSQL(sampled1.get(0), col1));
        } else {
            sb.append(col1.getName()).append(" IS NOT NULL");
        }
        sb.append(" OR ");
        if (sampled2 != null && !sampled2.isEmpty()) {
            sb.append(col2.getName()).append(" = ").append(quoteValueForSQL(sampled2.get(0), col2));
        } else {
            sb.append(col2.getName()).append(" IS NOT NULL");
        }
        sb.append(")");
        return sb.toString();
    }

    private String generateIndexFriendlyJoinClauses(List<TiDBTable> tables, TiDBTable fromTable) {
        if (tables.size() < 2) return "";

        StringBuilder joinClause = new StringBuilder();
        try {
            // Build list of tables eligible for JOIN (exclude the FROM table to avoid
            // "Not unique table/alias" errors when the same table appears twice)
            List<TiDBTable> joinableTables = new ArrayList<>(tables);
            joinableTables.remove(fromTable);
            if (joinableTables.isEmpty()) return "";

            int nrJoinClauses = (int) (Math.abs(Randomly.getPositiveOrZeroNonCachedInteger()) % Math.min(joinableTables.size(), 3) + 1);

            List<TiDBTable> remaining = new ArrayList<>(joinableTables);
            TiDBTable firstTable = fromTable;

            for (int i = 0; i < nrJoinClauses && !remaining.isEmpty(); i++) {
                TiDBTable joinTable = Randomly.fromList(remaining);
                remaining.remove(joinTable);

                String joinType = Randomly.fromOptions("JOIN", "LEFT JOIN", "RIGHT JOIN", "INNER JOIN");
                joinClause.append(" ").append(joinType).append(" ").append(joinTable.getName());

                // Build ON condition using indexed columns when possible
                List<TiDBColumn> cols1 = firstTable.getColumns();
                List<TiDBColumn> cols2 = joinTable.getColumns();
                if (!cols1.isEmpty() && !cols2.isEmpty()) {
                    // Prefer indexed columns for join condition
                    List<TiDBColumn> idxCols1 = getIndexedColumnsForTable(firstTable);
                    List<TiDBColumn> idxCols2 = getIndexedColumnsForTable(joinTable);

                    TiDBColumn c1 = !idxCols1.isEmpty() && Randomly.getBoolean()
                            ? Randomly.fromList(idxCols1) : Randomly.fromList(cols1);
                    TiDBColumn c2 = !idxCols2.isEmpty() && Randomly.getBoolean()
                            ? Randomly.fromList(idxCols2) : Randomly.fromList(cols2);

                    joinClause.append(" ON ").append(firstTable.getName()).append(".").append(c1.getName());
                    String op = Randomly.fromOptions(" = ", " = ", " = ", " >= ", " <= "); // bias toward equality
                    joinClause.append(op).append(joinTable.getName()).append(".").append(c2.getName());

                    // Optionally add a second condition
                    if (Randomly.getBoolean() && cols1.size() > 1 && cols2.size() > 1) {
                        TiDBColumn extra1 = Randomly.fromList(cols1);
                        TiDBColumn extra2 = Randomly.fromList(cols2);
                        joinClause.append(" AND ").append(firstTable.getName()).append(".").append(extra1.getName());
                        joinClause.append(" >= ").append(joinTable.getName()).append(".").append(extra2.getName());
                    }
                }
            }
        } catch (Exception e) {
            // fallback: return empty
        }
        return joinClause.toString();
    }

    // ==================== Mode 24: NULL Index Handling ====================

    // NULL values are stored separately in B-tree indexes; index scans can miss/miscount them.
    private void checkNullIndexHandling() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        TiDBTable table = Randomly.fromList(tables);
        List<TiDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        // Find nullable columns
        List<TiDBColumn> nullableCols = new ArrayList<>();
        for (TiDBColumn col : columns) {
            if (col.isNullable()) nullableCols.add(col);
        }
        // If no nullable column found, use any column (IS NOT NULL still tests index)
        if (nullableCols.isEmpty()) {
            nullableCols = columns;
        }

        TiDBColumn col = Randomly.fromList(nullableCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create an index on this column
        String idxName = "null_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            tablesNeedingAnalyze.add(table.getName());
        } catch (Exception e) {
            return;
        }

        // Check if the column actually has NULL values
        boolean hasNulls = false;
        try {
            List<String> nullCheck = execInternal(
                    "SELECT EXISTS(SELECT 1 FROM " + tblName + " WHERE " + colName + " IS NULL LIMIT 1);");
            hasNulls = nullCheck != null && !nullCheck.isEmpty() && !nullCheck.get(0).equals("0");
        } catch (Exception e) { }

        // Generate NULL-focused WHERE conditions
        String whereCond;
        int nullVariant;
        if (hasNulls) {
            nullVariant = Randomly.fromOptions(0, 1, 2, 3, 4);
        } else {
            nullVariant = Randomly.fromOptions(1, 3); // IS NOT NULL variants only
        }

        switch (nullVariant) {
        case 0:
            // IS NULL — tests that index scan finds all NULL rows
            whereCond = colName + " IS NULL";
            break;
        case 1:
            // IS NOT NULL — tests that index scan finds all non-NULL rows
            whereCond = colName + " IS NOT NULL";
            break;
        case 2:
            // IS NULL OR = value — tests NULL handling in OR conditions with index
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                whereCond = colName + " IS NULL OR " + colName + " = " + quoteValueForSQL(sampled.get(0), col);
            } else {
                whereCond = colName + " IS NULL";
            }
            break;
        case 3:
            // IS NOT NULL + range — tests NULL filtering combined with index range scan
            sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                whereCond = colName + " IS NOT NULL AND " + colName + " >= " + quoteValueForSQL(sampled.get(0), col);
            } else {
                whereCond = colName + " IS NOT NULL";
            }
            break;
        default:
            // COUNT(*) WHERE IS NULL vs COUNT(*) WHERE IS NOT NULL — compare sum to total
            String countNull = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NULL;";
            String countNotNull = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
            String countTotal = "SELECT COUNT(*) FROM " + tblName + ";";

            // Force index for NULL count
            String countNullIdx = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ COUNT(*) FROM "
                    + tblName + " WHERE " + colName + " IS NULL;";
            String countNotNullIdx = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ COUNT(*) FROM "
                    + tblName + " WHERE " + colName + " IS NOT NULL;";

            lastQueryString = "[NULL_IDX] NULL count check";

            List<String> rNullIdx = exec(countNullIdx);
            if (rNullIdx == null) return;
            List<String> rNullNoIdx = exec(countNull);
            if (rNullNoIdx == null) return;

            // Compare IS NULL count: index scan vs table scan
            assertResultSorted(rNullIdx, rNullNoIdx, countNull, "TIDB_NULL_IDX_ISNULL");

            List<String> rNotNullIdx = exec(countNotNullIdx);
            if (rNotNullIdx == null) return;
            List<String> rNotNullNoIdx = exec(countNotNull);
            if (rNotNullNoIdx == null) return;

            // Compare IS NOT NULL count: index scan vs table scan
            assertResultSorted(rNotNullIdx, rNotNullNoIdx, countNotNull, "TIDB_NULL_IDX_ISNOTNULL");
            return;
        }

        // Build queries for comparison
        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";

        lastQueryString = "[NULL_IDX] " + queryString;

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_NULL_IDX");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_NULL_IDX"); }
    }

    // ==================== Index Metadata Cache ====================

    private void invalidateIndexCache() {
        indexCacheValid = false;
        indexedColumnsCache.clear();
        compositeIndexCache.clear();
    }

    private void rebuildIndexCache() {
        indexedColumnsCache.clear();
        compositeIndexCache.clear();
        try {
            TiDBSchema schema = globalState.getSchema();
            for (TiDBTable table : schema.getDatabaseTables()) {
                String tblName = table.getName();
                indexedColumnsCache.put(tblName, getIndexedColumnsForTable(table));
                compositeIndexCache.put(tblName, getCompositeIndexGroups(table));
            }
        } catch (Exception e) { }
        indexCacheValid = true;
    }

    // ==================== Cached Column Value Sampling ====================

    private List<String> getCachedSampledValues(String tableName, String colName, int limit) {
        String key = tableName + "." + colName;
        if (columnValueCache.containsKey(key)) {
            return columnValueCache.get(key);
        }
        List<String> values = sampleColumnValues(tableName, colName, limit);
        columnValueCache.put(key, values);
        return values;
    }

    // ==================== Mode 25: Subquery + Index ====================

    private void checkSubqueryIndex() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        if (tables.size() < 2) return;

        List<TiDBTable> nonViewTables = new ArrayList<>();
        for (TiDBTable t : tables) { if (!t.isView()) nonViewTables.add(t); }
        if (nonViewTables.size() < 2) return;

        Collections.shuffle(nonViewTables);
        TiDBTable outerTable = nonViewTables.get(0);
        TiDBTable innerTable = nonViewTables.get(1);
        if (outerTable.getColumns().isEmpty() || innerTable.getColumns().isEmpty()) return;

        String outerTbl = outerTable.getName();
        String innerTbl = innerTable.getName();
        TiDBColumn outerCol = Randomly.fromList(outerTable.getColumns());
        TiDBColumn innerCol = Randomly.fromList(innerTable.getColumns());

        String outerIdx = "sq_out_" + Math.abs(outerCol.getName().hashCode() % 10000);
        String innerIdx = "sq_in_" + Math.abs(innerCol.getName().hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + outerIdx + " ON " + outerTbl + " (" + outerCol.getName() + ");", errors, true));
        } catch (Exception e) { }
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + innerIdx + " ON " + innerTbl + " (" + innerCol.getName() + ");", errors, true));
        } catch (Exception e) { }

        String queryString;
        if (Randomly.getBoolean()) {
            queryString = "SELECT * FROM " + outerTbl + " WHERE " + outerCol.getName()
                + " IN (SELECT " + innerCol.getName() + " FROM " + innerTbl + ");";
        } else {
            queryString = "SELECT * FROM " + outerTbl
                + " WHERE EXISTS (SELECT 1 FROM " + innerTbl
                + " WHERE " + innerTbl + "." + innerCol.getName()
                + " = " + outerTbl + "." + outerCol.getName() + ");";
        }
        lastQueryString = "[SUBQ_IDX] " + queryString;

        String hintQuery = "SELECT /*+ USE_INDEX(" + innerTbl + ", " + innerIdx + ") */ "
            + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(hintQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(queryString);
        if (r1 == null) return;
        List<String> r2 = exec(hintQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, queryString, "TIDB_SUBQ_IDX");
        if (lastCompareFiltered) countStarFallback(queryString, hintQuery, "TIDB_SUBQ_IDX");
    }

    // ==================== Mode 26: Enhanced Index Merge ====================

    private void checkIndexMergeEnhanced() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.size() < 2) return;

        List<TiDBColumn> cols = new ArrayList<>(indexableCols);
        Collections.shuffle(cols);
        TiDBColumn col1 = cols.get(0);
        TiDBColumn col2 = cols.get(1);
        String tblName = table.getName();

        String idx1 = "imerge_a_" + Math.abs(col1.getName().hashCode() % 10000);
        String idx2 = "imerge_b_" + Math.abs(col2.getName().hashCode() % 10000);
        boolean created1 = false, created2 = false;
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idx1 + " ON " + tblName + " (" + col1.getName() + ");", errors, true));
            created1 = true;
        } catch (Exception e) { }
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idx2 + " ON " + tblName + " (" + col2.getName() + ");", errors, true));
            created2 = true;
        } catch (Exception e) { }
        if (!created1 || !created2) return;

        invalidateIndexCache();

        // Fix: check both null and empty to avoid IndexOutOfBoundsException
        List<String> sampled1 = getCachedSampledValues(tblName, col1.getName(), 5);
        String val1 = (sampled1 != null && !sampled1.isEmpty())
            ? quoteValueForSQL(sampled1.get(0), col1) : "0";
        List<String> sampled2 = getCachedSampledValues(tblName, col2.getName(), 5);
        String val2 = (sampled2 != null && !sampled2.isEmpty())
            ? quoteValueForSQL(sampled2.get(0), col2) : "0";
        String whereClause = col1.getName() + " = " + val1 + " OR " + col2.getName() + " = " + val2;

        String mergeQuery = "SELECT /*+ USE_INDEX_MERGE(" + tblName + ", " + idx1 + ", " + idx2 + ") */ * FROM "
            + tblName + " WHERE " + whereClause + ";";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idx1 + ") IGNORE_INDEX("
            + tblName + ", " + idx2 + ") */ * FROM " + tblName + " WHERE " + whereClause + ";";

        lastQueryString = "[INDEX_MERGE_ENHANCED] " + mergeQuery;

        List<String> explainPlan1 = getExplainPlan(mergeQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(mergeQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, mergeQuery, "TIDB_INDEX_MERGE_ENHANCED");
        if (lastCompareFiltered) countStarFallback(mergeQuery, ignoreQuery, "TIDB_INDEX_MERGE_ENHANCED");
    }

    // ==================== Mode 27: Loose Index Scan ====================

    private void checkLooseIndexScan() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.size() < 2) return;

        List<TiDBColumn> cols = new ArrayList<>(indexableCols);
        Collections.shuffle(cols);
        TiDBColumn col1 = cols.get(0);
        TiDBColumn col2 = cols.get(1);
        String tblName = table.getName();

        // Create composite index for GROUP BY + MIN/MAX optimization
        String idxName = "loose_idx_" + Math.abs(col1.getName().hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName
                + " (" + col1.getName() + ", " + col2.getName() + ");", errors, true));
        } catch (Exception e) { return; }

        String aggFunc = Randomly.fromOptions("MIN", "MAX", "COUNT", "SUM");
        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ "
            + col1.getName() + ", " + aggFunc + "(" + col2.getName()
            + ") FROM " + tblName + " GROUP BY " + col1.getName() + ";";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ "
            + col1.getName() + ", " + aggFunc + "(" + col2.getName()
            + ") FROM " + tblName + " GROUP BY " + col1.getName() + ";";

        lastQueryString = "[LOOSE_SCAN] " + useQuery;

        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, useQuery, "TIDB_LOOSE_SCAN");
        if (lastCompareFiltered) countStarFallback(useQuery, ignoreQuery, "TIDB_LOOSE_SCAN");
    }

    // ==================== Mode 28: DML + Index Consistency ====================

    // Targets: MVCC visibility bugs, index corruption after DML, stale index reads.
    private void checkDMLIndexConsistency() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.isEmpty()) return;

        String tblName = table.getName();

        // Ensure at least one non-PK index exists
        List<TableIndex> indexes = table.getIndexes();
        boolean hasNonPK = false;
        for (TableIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY")) { hasNonPK = true; break; }
        }
        if (!hasNonPK) {
            TiDBColumn col = Randomly.fromList(indexableCols);
            String idxName = "dml_idx_" + Math.abs(col.getName().hashCode() % 10000);
            try {
                globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + col.getName() + ");", errors, true));
                tablesNeedingAnalyze.add(tblName);
            } catch (Exception e) { return; }
        }

        // Re-fetch indexes after potential creation
        indexes = table.getIndexes();
        List<TableIndex> nonPKIndexes = new ArrayList<>();
        for (TableIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY")) nonPKIndexes.add(idx);
        }
        if (nonPKIndexes.isEmpty()) return;

        // Record pre-DML query result using default plan
        TiDBColumn whereCol = Randomly.fromList(indexableCols);
        List<String> sampled = sampleColumnValues(tblName, whereCol.getName(), 3);
        String op = Randomly.fromOptions("=", ">=", "<=");
        String val;
        if (sampled != null && !sampled.isEmpty()) {
            val = quoteValueForSQL(sampled.get(0), whereCol);
        } else {
            val = generateRandomValueForColumn(whereCol);
        }
        String countQuery = "SELECT COUNT(*) FROM " + tblName
                + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";
        lastQueryString = "[DML_IDX] " + countQuery;

        // Execute random DML (1-3 operations)
        ExpectedErrors dmlErrors = new ExpectedErrors();
        dmlErrors.add("Deadlock");
        dmlErrors.add("Lock wait timeout");
        dmlErrors.add("Duplicate entry");
        dmlErrors.add("Write conflict");
        dmlErrors.add("cannot be null");
        dmlErrors.add("doesn't have a default value");
        dmlErrors.add("Data truncat");
        dmlErrors.add("out of range");
        TiDBErrors.addInsertErrors(dmlErrors);

        int numOps = Randomly.fromOptions(1, 2, 3);
        for (int i = 0; i < numOps; i++) {
            int dmlType = Randomly.fromOptions(0, 1, 2);
            try {
                switch (dmlType) {
                case 0: {
                    // INSERT
                    List<TiDBColumn> cols = table.getColumns();
                    StringBuilder insertSB = new StringBuilder();
                    insertSB.append("INSERT IGNORE INTO ").append(tblName).append(" VALUES (");
                    for (int j = 0; j < cols.size(); j++) {
                        if (j > 0) insertSB.append(", ");
                        insertSB.append(generateRandomValueForColumn(cols.get(j)));
                    }
                    insertSB.append(");");
                    log(insertSB.toString());
                    globalState.executeStatement(new SQLQueryAdapter(insertSB.toString(), dmlErrors, true));
                    break;
                }
                case 1: {
                    // UPDATE with WHERE on indexed column
                    List<String> updSampled = sampleColumnValues(tblName, whereCol.getName(), 3);
                    String updVal = (updSampled != null && !updSampled.isEmpty())
                            ? quoteValueForSQL(updSampled.get(0), whereCol) : generateRandomValueForColumn(whereCol);
                    String updateSQL = "UPDATE " + tblName + " SET "
                            + whereCol.getName() + " = " + updVal
                            + " WHERE " + whereCol.getName() + " IS NOT NULL LIMIT 1;";
                    log(updateSQL);
                    globalState.executeStatement(new SQLQueryAdapter(updateSQL, dmlErrors, true));
                    break;
                }
                case 2: {
                    // DELETE with WHERE on indexed column
                    List<String> delSampled = sampleColumnValues(tblName, whereCol.getName(), 3);
                    String delCond;
                    if (delSampled != null && !delSampled.isEmpty()) {
                        delCond = whereCol.getName() + " = " + quoteValueForSQL(delSampled.get(0), whereCol);
                    } else {
                        delCond = whereCol.getName() + " IS NOT NULL";
                    }
                    String deleteSQL = "DELETE FROM " + tblName + " WHERE " + delCond + " LIMIT 1;";
                    log(deleteSQL);
                    globalState.executeStatement(new SQLQueryAdapter(deleteSQL, dmlErrors, true));
                    break;
                }
                }
            } catch (Exception e) {
                // DML may fail due to constraints — that's expected
            }
        }

        // After DML: compare results using different index hints
        TableIndex hintIdx = Randomly.fromList(nonPKIndexes);
        String idxName = hintIdx.getIndexName();

        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ COUNT(*) FROM "
                + tblName + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ COUNT(*) FROM "
                + tblName + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";

        // EXPLAIN filter
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        assertResultSorted(r1, r2, useQuery, "TIDB_DML_INDEX");
    }

    // ==================== Mode 29: Generated Column + Index ====================

    // TiDB supports VIRTUAL (since 7.5) and STORED generated column indexes. Has caught real bugs.
    private void checkGeneratedColumnIndex() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();

        // Look for idx_t3 (generated column table created by createIndexFriendlyTables)
        TiDBTable genTable = null;
        for (TiDBTable t : tables) {
            if (t.getName().equals("idx_t3")) {
                genTable = t;
                break;
            }
        }

        if (genTable == null) {
            // Create the generated column table on-the-fly
            ExpectedErrors createErrors = new ExpectedErrors();
            createErrors.add("already exists");
            createErrors.add("Unsupported");
            try {
                // Try creating a table with generated columns
                // TiDB supports: col INT AS (expr) [VIRTUAL|STORED]
                String createSQL = "CREATE TABLE IF NOT EXISTS idx_t3 ("
                        + "c0 INT NOT NULL, "
                        + "c1 INT NOT NULL, "
                        + "c2 VARCHAR(64) NOT NULL, "
                        + "gen_col_0 INT AS (c0 + c1) STORED, "
                        + "gen_col_1 VARCHAR(128) AS (CONCAT(c2, c0)) STORED, "
                        + "PRIMARY KEY (c0)"
                        + ");";
                globalState.executeStatement(new SQLQueryAdapter(createSQL, createErrors, true));

                // Create indexes on generated columns
                String[] indexSQLs = {
                    "CREATE INDEX IF NOT EXISTS idx_t3_gen0 ON idx_t3 (gen_col_0);",
                    "CREATE INDEX IF NOT EXISTS idx_t3_gen1 ON idx_t3 (gen_col_1);",
                    "CREATE INDEX IF NOT EXISTS idx_t3_c0gen0 ON idx_t3 (c0, gen_col_0);",
                };
                for (String idxSQL : indexSQLs) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(idxSQL, createErrors, true));
                    } catch (Exception e) { }
                }

                // Insert data into idx_t3
                ExpectedErrors insertErrors = new ExpectedErrors();
                TiDBErrors.addInsertErrors(insertErrors);
                insertErrors.add("Duplicate entry");
                Randomly r = globalState.getRandomly();
                for (int batch = 0; batch < 4; batch++) {
                    StringBuilder insertSQL = new StringBuilder();
                    insertSQL.append("INSERT IGNORE INTO idx_t3 (c0, c1, c2) VALUES ");
                    for (int row = 0; row < 50; row++) {
                        if (row > 0) insertSQL.append(", ");
                        insertSQL.append("(");
                        insertSQL.append(r.getInteger() % 255).append(", ");
                        insertSQL.append(r.getInteger() % 255).append(", ");
                        insertSQL.append("'").append(r.getString().replace("'", "''").substring(0, Math.min(20, r.getString().length()))).append("'");
                        insertSQL.append(")");
                    }
                    insertSQL.append(";");
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(insertSQL.toString(), insertErrors, true));
                    } catch (Exception e) { }
                }
                tablesNeedingAnalyze.add("idx_t3");
            } catch (Exception e) {
                return; // Generated column not supported — skip
            }

            // Refresh schema
            genTable = null;
            for (TiDBTable t : globalState.getSchema().getDatabaseTables()) {
                if (t.getName().equals("idx_t3")) {
                    genTable = t;
                    break;
                }
            }
            if (genTable == null) return;
        }

        String tblName = genTable.getName();
        List<TableIndex> indexes = genTable.getIndexes();
        List<TableIndex> nonPKIndexes = new ArrayList<>();
        for (TableIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY")) nonPKIndexes.add(idx);
        }
        if (nonPKIndexes.isEmpty()) return;

        // Get indexed columns from schema — check for generated columns
        for (TableIndex idx : nonPKIndexes) {
            List<TiDBColumn> idxCols = getIndexColumnsFromSchema(genTable, idx.getIndexName());
            if (idxCols.isEmpty()) continue;

            // Build query targeting the generated column index
            TiDBColumn idxCol = idxCols.get(0);
            String idxColName = idxCol.getName();
            String idxName = idx.getIndexName();

            // Sample values from the generated column
            List<String> sampled = sampleColumnValues(tblName, idxColName, 5);
            String whereCond;
            if (sampled != null && !sampled.isEmpty()) {
                String op = Randomly.fromOptions("=", ">=", "<=");
                whereCond = idxColName + " " + op + " " + quoteValueForSQL(sampled.get(0), idxCol);
            } else {
                whereCond = idxColName + " IS NOT NULL";
            }

            // Get PK column for ORDER BY
            TiDBColumn pkCol = getPrimaryKeyColumn(genTable);
            String orderBy = pkCol != null ? " ORDER BY " + pkCol.getName() : "";

            String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                    + tblName + " WHERE " + whereCond + orderBy + " LIMIT 100;";
            String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                    + tblName + " WHERE " + whereCond + orderBy + " LIMIT 100;";

            lastQueryString = "[GEN_COL_IDX] " + useQuery;

            // EXPLAIN filter
            List<String> explainPlan1 = getExplainPlan(useQuery);
            List<String> explainPlan2 = getExplainPlan(ignoreQuery);
            if (!plansAreDifferent(explainPlan1, explainPlan2)) continue;

            List<String> r1 = exec(useQuery);
            if (r1 == null) continue;
            List<String> r2 = exec(ignoreQuery);
            if (r2 == null) continue;

            lastCompareFiltered = false;
            assertResultSorted(r1, r2, useQuery, "TIDB_GEN_COL_INDEX");
            if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_GEN_COL_INDEX"); }

            // Only test one index per invocation to avoid excessive index creation
            break;
        }
    }

    // ==================== [P1] Mode 30: Aggregate + Index ====================

    private void checkAggregateIndex() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.isEmpty()) return;

        TiDBColumn groupCol = Randomly.fromList(indexableCols);
        String tblName = table.getName();
        String groupColName = groupCol.getName();

        String typeName = groupCol.getType().toString().toUpperCase();
        String aggFunc;
        if (typeName.contains("FLOAT") || typeName.contains("DOUBLE") || typeName.contains("REAL")) {
            aggFunc = Randomly.fromOptions("COUNT", "MIN", "MAX");
        } else {
            aggFunc = Randomly.fromOptions("COUNT", "SUM", "MIN", "MAX");
        }

        String idxName = "agg_idx_" + Math.abs(groupColName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + groupColName + ");", errors, true));
            tablesNeedingAnalyze.add(tblName);
        } catch (Exception e) { }

        List<String> sampled = sampleColumnValues(tblName, groupColName, 5);
        String whereClause = "";
        if (sampled != null && !sampled.isEmpty() && Randomly.getBoolean()) {
            String op = Randomly.fromOptions(">", ">=", "<=");
            whereClause = " WHERE " + groupColName + " " + op + " " + quoteValueForSQL(sampled.get(0), groupCol);
        }

        String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ "
            + groupColName + ", " + aggFunc + "(" + groupColName + ") FROM " + tblName
            + whereClause + " GROUP BY " + groupColName + ";";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ "
            + groupColName + ", " + aggFunc + "(" + groupColName + ") FROM " + tblName
            + whereClause + " GROUP BY " + groupColName + ";";

        lastQueryString = "[AGG_IDX] " + useQuery;

        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, useQuery, "TIDB_AGG_INDEX");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_AGG_INDEX"); }
    }

    // ==================== [P1] Mode 31: DESC Index Sort ====================

    private void checkDescIndexSort() throws Exception {
        TiDBSchema schema = globalState.getSchema();
        List<TiDBTable> tables = schema.getDatabaseTables();
        String descIdxName = null;
        String descTblName = null;
        String descColName = null;

        for (TiDBTable t : tables) {
            if (t.isView()) continue;
            for (TableIndex idx : t.getIndexes()) {
                String name = idx.getIndexName().toLowerCase();
                if (name.contains("desc") && !name.equals("primary")) {
                    List<TiDBColumn> idxCols = getIndexColumnsFromSchema(t, idx.getIndexName());
                    if (!idxCols.isEmpty()) {
                        descIdxName = idx.getIndexName();
                        descTblName = t.getName();
                        descColName = idxCols.get(0).getName();
                        break;
                    }
                }
            }
            if (descIdxName != null) break;
        }

        if (descIdxName == null) {
            TiDBTable table = getRandomIndexableTable();
            if (table == null) return;
            List<TiDBColumn> indexableCols = getIndexableColumns(table);
            if (indexableCols.isEmpty()) return;
            TiDBColumn col = Randomly.fromList(indexableCols);
            descTblName = table.getName();
            descColName = col.getName();
            descIdxName = "desc_idx_" + Math.abs(col.getName().hashCode() % 10000);
            try {
                globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + descIdxName + " ON " + descTblName
                    + " (" + descColName + " DESC);", errors, true));
                tablesNeedingAnalyze.add(descTblName);
            } catch (Exception e) { return; }
        }

        int limit = Randomly.fromOptions(5, 10, 20, 50);
        String whereClause = "";
        if (Randomly.getBoolean()) {
            whereClause = " WHERE " + descColName + " IS NOT NULL";
        }

        String useQuery = "SELECT /*+ USE_INDEX(" + descTblName + ", " + descIdxName + ") */ * FROM "
            + descTblName + whereClause + " ORDER BY " + descColName + " DESC LIMIT " + limit + ";";
        String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + descTblName + ", " + descIdxName + ") */ * FROM "
            + descTblName + whereClause + " ORDER BY " + descColName + " DESC LIMIT " + limit + ";";

        lastQueryString = "[DESC_IDX] " + useQuery;

        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = exec(useQuery);
        if (r1 == null) return;
        List<String> r2 = exec(ignoreQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, useQuery, "TIDB_DESC_INDEX");
        if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_DESC_INDEX"); }
    }

    // ==================== [P1] Mode 32: DROP COLUMN + Index ====================

    private void checkDropColumnIndex() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> columns = table.getColumns();
        if (columns.size() < 3) return;

        String tblName = table.getName();

        List<TiDBColumn> candidates = new ArrayList<>();
        for (TiDBColumn col : columns) {
            if (!col.isPrimaryKey()) {
                String tn = col.getType().toString().toUpperCase();
                if (!tn.contains("TEXT") && !tn.contains("BLOB") && !tn.contains("JSON")) {
                    candidates.add(col);
                }
            }
        }
        if (candidates.isEmpty()) return;

        TiDBColumn colToDrop = Randomly.fromList(candidates);
        String colName = colToDrop.getName();

        String idxName = "dropcol_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            tablesNeedingAnalyze.add(tblName);
        } catch (Exception e) { }

        String countQuery = "SELECT COUNT(*) FROM " + tblName + ";";
        List<String> countBefore = exec(countQuery);
        if (countBefore == null) return;

        // Pre-check: skip columns referenced by generated columns (thorough fix for false positives)
        // TiDB rejects DROP COLUMN if any generated column depends on it.
        try {
            List<String> genDepCheck = execInternal(
                    "SELECT COLUMN_NAME FROM information_schema.COLUMNS WHERE TABLE_SCHEMA = DATABASE()"
                    + " AND TABLE_NAME = '" + tblName + "' AND EXTRA LIKE '%generated%'"
                    + " AND GENERATION_EXPRESSION LIKE '%" + colName + "%' LIMIT 1;");
            if (genDepCheck != null && !genDepCheck.isEmpty()) {
                return; // Column is referenced by a generated column — skip
            }
        } catch (Exception e) {
            // Safety: if check fails, proceed (the error handler below will catch it)
        }

        ExpectedErrors dropErrors = new ExpectedErrors();
        dropErrors.add("can't drop");
        dropErrors.add("column is indexed");
        dropErrors.add("part of partitioning");
        dropErrors.add("doesn't exist");
        dropErrors.add("does not exist");
        dropErrors.add("Information schema is changed");
        dropErrors.add("Unsupported");
        dropErrors.add("generated column dependency"); // TiDB: column referenced by generated column

        try {
            String dropSQL = "ALTER TABLE " + tblName + " DROP COLUMN " + colName + ";";
            log(dropSQL);
            globalState.executeStatement(new SQLQueryAdapter(dropSQL, dropErrors, true));
        } catch (Throwable e) {
            // Use catch(Throwable) because SQLQueryAdapter.checkException() throws AssertionError
            // (which is NOT a subclass of Exception) when error message is not in ExpectedErrors.
            return;
        }
        refreshSchema();

        lastQueryString = "[DROP_COL] ALTER TABLE " + tblName + " DROP COLUMN " + colName;

        List<String> countAfter = exec(countQuery);
        if (countAfter == null) return;
        assertResultSorted(countBefore, countAfter, countQuery, "TIDB_DROP_COL_COUNT");
    }

    public String getLastQueryString() {
        return lastQueryString;
    }

    // ==================== [P1] Mode 33: Collation + Index ====================

    private void checkCollationIndex() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> columns = table.getColumns();
        List<TiDBColumn> stringCols = new ArrayList<>();
        for (TiDBColumn col : columns) {
            String typeName = col.getType().toString().toUpperCase();
            if (typeName.contains("CHAR") || typeName.contains("VARCHAR") || typeName.contains("TEXT")) {
                // Root-cause fix: TiDB does not allow modifying collation on indexed columns.
                // Filter out columns that already participate in any index to prevent
                // "Unsupported modifying collation ... when index is defined on it" errors.
                if (!isColumnIndexed(table.getName(), col.getName())) {
                    stringCols.add(col);
                }
            }
        }
        if (stringCols.isEmpty()) return;

        TiDBColumn col = Randomly.fromList(stringCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Root-cause fix: save original collation so we can restore it after testing.
        // Without this, checkCollationIndex() permanently changes a column's collation,
        // which poisons all subsequent cross-table comparisons (JOIN, subquery) in other
        // oracle methods, causing "Illegal mix of collations" crashes.
        // See: database3.log, database5.log
        String originalCollation = getColumnCollation(tblName, colName);
        if (originalCollation == null) return; // cannot determine collation, skip

        String collation = Randomly.fromOptions("utf8mb4_bin", "utf8mb4_general_ci", "utf8mb4_0900_ai_ci");
        String idxName = "coll_idx_" + Math.abs(colName.hashCode() % 10000);
        boolean collationChanged = false;
        try {
            ExpectedErrors collErrors = new ExpectedErrors();
            collErrors.add("index already exist");
            collErrors.add("Duplicate key name");
            collErrors.add("Specified key was too long");
            collErrors.add("BLOB or TEXT");
            collErrors.add("used in key specification");
            collErrors.add("Unsupported modifying collation"); // safety net
            // TiDB does not support CREATE INDEX with COLLATE clause;
            // instead, ALTER the column's collation first, then create a regular index
            String fullType = col.getType().toString();
            String alterSQL = "ALTER TABLE " + tblName + " MODIFY COLUMN " + colName + " " + fullType + " COLLATE " + collation + ";";
            globalState.executeStatement(new SQLQueryAdapter(alterSQL, collErrors, true));
            collationChanged = true;
            String createIdxSQL = "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");";
            globalState.executeStatement(new SQLQueryAdapter(createIdxSQL, collErrors, true));
            tablesNeedingAnalyze.add(tblName);
            refreshSchema();
        } catch (Throwable e) {
            // collation may or may not have been changed — restore to be safe
            if (collationChanged) {
                restoreCollation(tblName, colName, col.getType().toString(), originalCollation);
                refreshSchema();
            }
            return;
        } // catch Throwable to also catch AssertionError from checkException

        try {
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            String val = (sampled != null && !sampled.isEmpty()) ? quoteValueForSQL(sampled.get(0), col) : "'test'";

            String useQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = " + val + " LIMIT 50;";
            String ignoreQuery = "SELECT /*+ IGNORE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = " + val + " LIMIT 50;";

            lastQueryString = "[COLLATION_IDX] " + useQuery;

            List<String> explainPlan1 = getExplainPlan(useQuery);
            List<String> explainPlan2 = getExplainPlan(ignoreQuery);
            if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

            List<String> r1 = exec(useQuery);
            if (r1 == null) return;
            List<String> r2 = exec(ignoreQuery);
            if (r2 == null) return;

            lastCompareFiltered = false;
            assertResultSorted(r1, r2, useQuery, "TIDB_COLLATION_INDEX");
            if (lastCompareFiltered) { countStarFallback(useQuery, ignoreQuery, "TIDB_COLLATION_INDEX"); }
        } finally {
            // Root-cause fix: always restore original collation to prevent poisoning
            // other oracle methods that do cross-table string column comparisons.
            if (collationChanged) {
                restoreCollation(tblName, colName, col.getType().toString(), originalCollation);
            }
        }
    }

    private String getColumnCollation(String tableName, String columnName) {
        try {
            List<String> result = execInternal(
                "SELECT COLLATION_NAME FROM information_schema.COLUMNS "
                + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName + "' "
                + "AND COLUMN_NAME = '" + columnName + "' LIMIT 1;");
            return (result != null && !result.isEmpty()) ? result.get(0) : null;
        } catch (Exception e) {
            return null;
        }
    }

    // Cleanup only — silently ignores failures (collation restoration is best-effort).
    private void restoreCollation(String tableName, String columnName, String fullType, String originalCollation) {
        try {
            ExpectedErrors restoreErrors = new ExpectedErrors();
            restoreErrors.add("Unsupported modifying collation");
            globalState.executeStatement(new SQLQueryAdapter(
                "ALTER TABLE " + tableName + " MODIFY COLUMN " + columnName + " " + fullType
                + " COLLATE " + originalCollation + ";", restoreErrors, true));
        } catch (Throwable t) {
            // Silently ignore — restoration is best-effort cleanup
        }
    }

    // TiDB doesn't support modifying collation on indexed columns; used to guard ALTER TABLE MODIFY.
    private boolean isColumnIndexed(String tableName, String columnName) {
        try {
            List<String> result = execInternal(
                    "SELECT 1 FROM information_schema.STATISTICS WHERE TABLE_SCHEMA = DATABASE()"
                    + " AND TABLE_NAME = '" + tableName + "'"
                    + " AND COLUMN_NAME = '" + columnName + "' LIMIT 1;");
            return result != null && !result.isEmpty();
        } catch (Exception e) {
            // On error, conservatively assume the column IS indexed to avoid the risky operation
            return true;
        }
    }

    // ==================== [P1] Mode 34: Implicit Type Conversion + Index ====================

    private void checkImplicitTypeConversionIndex() throws Exception {
        TiDBTable table = getRandomIndexableTable();
        if (table == null) return;
        List<TiDBColumn> indexableCols = getIndexableColumns(table);
        if (indexableCols.isEmpty()) return;

        TiDBColumn col = Randomly.fromList(indexableCols);
        String tblName = table.getName();
        String colName = col.getName();

        String idxName = "conv_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            tablesNeedingAnalyze.add(tblName);
        } catch (Exception e) { return; }

        List<String> sampled = sampleColumnValues(tblName, colName, 3);
        if (sampled == null || sampled.isEmpty()) return;
        String rawVal = sampled.get(0).trim();

        String typeName = col.getType().toString().toUpperCase();
        String correctQuery, conversionQuery;

        if (typeName.contains("INT")) {
            String intVal = rawVal.replace("'", "").trim();
            correctQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = " + intVal + " LIMIT 50;";
            conversionQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = '" + intVal + "' LIMIT 50;";
        } else if (typeName.contains("CHAR") || typeName.contains("VARCHAR") || typeName.contains("TEXT")) {
            String strVal = rawVal;
            if (strVal.startsWith("'") && strVal.endsWith("'")) {
                strVal = strVal.substring(1, strVal.length() - 1);
            }
            correctQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = '" + strVal.replace("'", "''") + "' LIMIT 50;";
            conversionQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " + 0 = '" + strVal.replace("'", "''") + "' + 0 LIMIT 50;";
        } else if (typeName.contains("FLOAT") || typeName.contains("DOUBLE") || typeName.contains("DECIMAL")) {
            String numVal = rawVal.replace("'", "").trim();
            correctQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = " + numVal + " LIMIT 50;";
            conversionQuery = "SELECT /*+ USE_INDEX(" + tblName + ", " + idxName + ") */ * FROM "
                + tblName + " WHERE " + colName + " = '" + numVal + "' LIMIT 50;";
        } else {
            return;
        }

        lastQueryString = "[TYPE_CONV_IDX] correct=" + correctQuery + " conversion=" + conversionQuery;

        List<String> r1 = exec(correctQuery);
        if (r1 == null) return;
        List<String> r2 = exec(conversionQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        assertResultSorted(r1, r2, correctQuery, "TIDB_TYPE_CONV_INDEX");
        if (lastCompareFiltered) { countStarFallback(correctQuery, conversionQuery, "TIDB_TYPE_CONV_INDEX"); }
    }

    // ==================== [P1] Statistics Tracking ====================

    private void trackMode(int mode) {
        checkCount++;
        String key = String.valueOf(mode);
        modeStats.computeIfAbsent(key, k -> new java.util.concurrent.atomic.AtomicInteger(0)).incrementAndGet();

        if (checkCount % STATS_REPORT_INTERVAL == 0) {
            try {
                StringBuilder sb = new StringBuilder();
                sb.append("[TIDB_STATS] Check #").append(checkCount).append(" mode distribution: ");
                List<String> parts = new ArrayList<>();
                for (Map.Entry<String, java.util.concurrent.atomic.AtomicInteger> e : modeStats.entrySet()) {
                    parts.add("mode_" + e.getKey() + "=" + e.getValue().get());
                }
                sb.append(String.join(", ", parts));
                log(sb.toString());
            } catch (Exception e) { }
        }

        // Periodic data refresh
        if (checkCount - lastDataRefreshCheck >= DATA_REFRESH_INTERVAL) {
            lastDataRefreshCheck = checkCount;
            try {
                for (TiDBTable table : globalState.getSchema().getDatabaseTables()) {
                    if (table.isView()) continue;
                    List<String> countResult = execInternal("SELECT COUNT(*) FROM " + table.getName() + ";");
                    int rowCount = 0;
                    if (countResult != null && !countResult.isEmpty()) {
                        try { rowCount = Integer.parseInt(countResult.get(0).trim()); } catch (NumberFormatException e) { }
                    }
                    if (rowCount < 50) {
                        ExpectedErrors insertErrors = new ExpectedErrors();
                        TiDBErrors.addInsertErrors(insertErrors);
                        List<TiDBColumn> cols = table.getColumns();
                        if (cols.isEmpty()) continue;
                        StringBuilder colList = new StringBuilder();
                        for (int i = 0; i < cols.size(); i++) {
                            if (i > 0) colList.append(", ");
                            colList.append(cols.get(i).getName());
                        }
                        for (int batch = 0; batch < 20; batch++) {
                            StringBuilder sb = new StringBuilder();
                            sb.append("INSERT IGNORE INTO ").append(table.getName()).append("(").append(colList).append(") VALUES (");
                            for (int i = 0; i < cols.size(); i++) {
                                if (i > 0) sb.append(", ");
                                sb.append(generateRandomValueForColumn(cols.get(i)));
                            }
                            sb.append(");");
                            try {
                                globalState.executeStatement(new SQLQueryAdapter(sb.toString(), insertErrors, true));
                            } catch (Exception e) { }
                        }
                    }
                }
            } catch (Exception e) { }
        }
    }

    // ==================== Session Variable Save/Restore Helpers ====================

    private String saveSessionVariables(String setStatements) {
        StringBuilder saved = new StringBuilder();
        String[] stmts = setStatements.split(";");
        for (String stmt : stmts) {
            stmt = stmt.trim();
            if (stmt.isEmpty()) continue;
            String normalized = stmt.replace("SET SESSION", "").trim();
            int eqIdx = normalized.indexOf('=');
            if (eqIdx < 0) continue;
            String varName = normalized.substring(0, eqIdx).trim();
            try {
                List<String> result = execInternal("SHOW SESSION VARIABLES LIKE '" + varName + "';");
                if (result != null && !result.isEmpty()) {
                    String row = result.get(0);
                    // ComparatorHelper returns columns separated by " ||| "
                    String[] parts = row.split(" \\|\\|\\| ");
                    if (parts.length >= 2) {
                        saved.append("SET SESSION ").append(varName).append("=").append(parts[1].trim()).append(";");
                    }
                }
            } catch (Exception e) {
                // skip if we can't read
            }
        }
        return saved.toString();
    }

    private void restoreSessionVariables(String savedState) throws Exception {
        if (savedState == null || savedState.isEmpty()) return;
        String[] stmts = savedState.split(";");
        for (String stmt : stmts) {
            stmt = stmt.trim();
            if (stmt.isEmpty()) continue;
            globalState.executeStatement(new SQLQueryAdapter(stmt + ";", errors, true));
        }
    }

    // Cascades vs non-cascades optimizer via USE_INDEX_MERGE; detects result inconsistencies.
    private void checkComplexIndexQuery() throws Exception {
        TiDBTable table = getRandomTableWithIndexes();
        if (table == null) return;

        String queryString = generateIndexAwareQuery(table);
        lastQueryString = "[COMPLEX_IDX] " + queryString;

        // Switch cascades optimizer and compare results
        String cascadesQuery = "SELECT /*+ USE_INDEX_MERGE(" + table.getName() + ") */ "
                + queryString.substring(queryString.indexOf("SELECT") + 6);

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(cascadesQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        if (!compareQueries(queryString, cascadesQuery, "COMPLEX_IDX", queryString)) return;
    }
}
