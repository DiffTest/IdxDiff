package idxdiff.polardb;

import java.sql.ResultSet;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
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
import idxdiff.polardb.PolarDBErrors;
import idxdiff.mysql.MySQLGlobalState;
import idxdiff.mysql.MySQLSchema;
import idxdiff.mysql.MySQLSchema.MySQLColumn;
import idxdiff.mysql.MySQLSchema.MySQLIndex;
import idxdiff.mysql.MySQLSchema.MySQLTable;
import idxdiff.mysql.MySQLSchema.MySQLTables;
import idxdiff.mysql.MySQLVisitor;
import idxdiff.mysql.ast.MySQLBetweenOperation;
import idxdiff.mysql.ast.MySQLBinaryComparisonOperation;
import idxdiff.mysql.ast.MySQLBinaryComparisonOperation.BinaryComparisonOperator;
import idxdiff.mysql.ast.MySQLBinaryLogicalOperation;
import idxdiff.mysql.ast.MySQLBinaryLogicalOperation.MySQLBinaryLogicalOperator;
import idxdiff.mysql.ast.MySQLColumnReference;
import idxdiff.mysql.ast.MySQLConstant;
import idxdiff.mysql.ast.MySQLExpression;
import idxdiff.mysql.ast.MySQLInOperation;
import idxdiff.mysql.ast.MySQLJoin;
import idxdiff.mysql.ast.MySQLJoin.JoinType;
import idxdiff.mysql.ast.MySQLSelect;
import idxdiff.mysql.ast.MySQLSelect.SelectType;
import idxdiff.mysql.ast.MySQLTableReference;
import idxdiff.mysql.ast.MySQLUnaryPostfixOperation;
import idxdiff.mysql.ast.MySQLUnaryPostfixOperation.UnaryPostfixOperator;
import idxdiff.mysql.gen.MySQLExpressionGenerator;
import idxdiff.mysql.gen.MySQLHintGenerator;
import idxdiff.mysql.gen.MySQLRandomQuerySynthesizer;
import idxdiff.mysql.gen.datadef.MySQLIndexGenerator;

/**
 * PolarDB Index Oracle — verifies that different index strategies produce
 * identical query results. Uses MySQL-compatible syntax (PolarDB is MySQL 8.0-compatible).
 *
 * Active test modes:
 * <ul>
 * <li>0: CREATE_INDEX_CONSISTENCY — query before/after index creation</li>
 * <li>1: DROP_INDEX_CONSISTENCY — query before/after index drop</li>
 * <li>2: FORCE_INDEX_VS_DEFAULT — FORCE INDEX vs default plan</li>
 * <li>3: IGNORE_INDEX_VS_DEFAULT — IGNORE INDEX vs default plan</li>
 * <li>4: STRAIGHT_JOIN_VS_OPTIMIZER [DISABLED]</li>
 * <li>5: OPTIMIZER_SWITCH_INDEX [DISABLED]</li>
 * <li>6: ORDER_BY_INDEX_SORT [DISABLED]</li>
 * <li>7: INDEX_HINT_CONSISTENCY [DISABLED]</li>
 * <li>8: MULTI_INDEX_CREATE — create multiple indexes, compare plans</li>
 * <li>9: AGGREGATE_PLAN — aggregate query with different optimizer settings</li>
 * <li>10: JOIN_INDEX_SELECTION — JOIN with forced index on each table</li>
 * <li>11: INVISIBLE_INDEX — CREATE INDEX INVISIBLE, verify no effect</li>
 * <li>12: PREFIX_INDEX — prefix index on VARCHAR, compare results</li>
 * <li>13: HASH_VS_BTREE — HASH index vs BTREE index comparison</li>
 * <li>14: OPTIMIZER_HINT_INDEX [DISABLED]</li>
 * <li>15: INDEX_MERGE — index merge intersection/union</li>
 * <li>16: LOOSE_INDEX_SCAN — loose index scan on GROUP BY</li>
 * <li>17: COVERING_INDEX — index-only scan verification</li>
 * <li>18: ORDER_BY_LIMIT_INDEX — ORDER BY + LIMIT with index vs filesort</li>
 * <li>19: SUBQUERY_INDEX — subquery with index conditions</li>
 * <li>20: RANGE_BOUNDARY — range scan boundary correctness</li>
 * <li>21: TABLE_VERIFICATION — CHECK TABLE after index operations</li>
 * <li>22: UNIQUE_INDEX_CONSISTENCY — UNIQUE index data consistency</li>
 * <li>23: DROP_COLUMN_WITH_INDEX — DROP COLUMN with dependent index</li>
 * <li>24: FULLTEXT_INDEX [DISABLED]</li>
 * <li>25: ICP_CONSISTENCY — index_condition_pushdown on vs off</li>
 * <li>26: OPTIMIZER_SWITCH_DETAILED — pairwise optimizer switch comparison</li>
 * <li>27: SQL_SEMANTIC_EQUIVALENCE — equivalent rewrites produce same results</li>
 * <li>28: DETERMINISTIC_INDEX_QUERY — deterministic queries with index hints</li>
 * <li>29: NULL_INDEX_HANDLING — NULL values in indexed columns</li>
 * <li>30: FUNCTIONAL_INDEX — functional index via generated column</li>
 * <li>31: DML_INDEX_CONSISTENCY — DML operations maintain index consistency</li>
 * <li>32: DESC_INDEX_SORT — DESC index sort order correctness</li>
 * <li>33: GENERATED_COLUMN_INDEX — generated column index</li>
 * <li>34: COLLATION_INDEX — collation-dependent index behavior</li>
 * <li>35: TYPE_MISMATCH_INDEX — type mismatch in indexed comparisons</li>
 * </ul>
 */
public class PolarDBIndexOracle implements TestOracle<MySQLGlobalState> {

    private final MySQLGlobalState globalState;
    private final ExpectedErrors errors;
    private String lastQueryString;
    private boolean dataPopulated = false;
    Periodic data refresh counter — prevents table degradation
    // from DROP COLUMN, DELETE, etc. causing long-running tests to lose effectiveness.
    private int checksSinceLastDataRefresh = 0;
    Effective test ratio tracking
    private int totalTests = 0;
    private int effectiveTests = 0;
    private int explainFiltered = 0;  // plansAreDifferent returned false
    private int queriesCompared = 0;  // actually executed both queries and compared results
    private int aggregateFallbackUsed = 0; // how many times COUNT(*) fallback was used

    // Flag: set to true when compareResultsSorted/Strict filters out a result difference
    private boolean lastCompareFiltered = false;

    MySQL allows max 64 indexes per table. Prune excess non-PRIMARY indexes
    // periodically to prevent "Too many keys specified" errors from dominating test output.
    private static final int MYSQL_MAX_INDEXES_PER_TABLE = 64;
    private static final int INDEX_PRUNE_THRESHOLD = 50;
    private static final int INDEX_PRUNE_TARGET = 20;
    private int checksSinceLastIndexPrune = 0;

    // ==================== P0: COUNT(*) Aggregate Fallback ====================

    // When compareResultsSorted/Strict filters out a difference due to LIMIT/GROUP BY non-determinism,
    // uses COUNT(*) as a deterministic fallback (strips SELECT cols, ORDER BY, LIMIT from both queries).
    private void countStarFallback(String queryA, String queryB, String mode) {
        try {
            String countA = wrapInCountStar(queryA);
            String countB = wrapInCountStar(queryB);
            if (countA == null || countB == null) return;

            List<String> cr1 = executeQuery(countA);
            if (cr1 == null) return;
            List<String> cr2 = executeQuery(countB);
            if (cr2 == null) return;

            aggregateFallbackUsed++;

            // COUNT(*) returns a single row with one value — direct comparison
            if (!cr1.equals(cr2)) {
                // Double-check with sorted (shouldn't matter for single row, but safe)
                List<String> s1 = new ArrayList<>(cr1);
                List<String> s2 = new ArrayList<>(cr2);
                s1.sort(PolarDBIndexOracle::nullSafeCompare);
                s2.sort(PolarDBIndexOracle::nullSafeCompare);
                if (!s1.equals(s2)) {
                    effectiveTests++;
                    List<String> combinedString = new ArrayList<>();
                    combinedString.add("-- [" + mode + "_COUNT_FALLBACK] Original query: " + queryA);
                    combinedString.add("-- [" + mode + "_COUNT_FALLBACK] Count A: " + countA + " => " + cr1);
                    combinedString.add("-- [" + mode + "_COUNT_FALLBACK] Count B: " + countB + " => " + cr2);
                    ComparatorHelper.assumeResultSetsAreEqual(cr1, cr2, countA, combinedString, globalState);
                }
            }
        } catch (Exception e) {
            // Ignore errors in fallback — the main comparison already handled
        }
    }

    // Wraps SELECT in SELECT COUNT(*): strips SELECT cols, ORDER BY, LIMIT; keeps FROM+hints+WHERE.
    private String wrapInCountStar(String query) {
        if (query == null) return null;
        String upper = query.toUpperCase().trim();

        // Find FROM position
        int fromIdx = upper.indexOf("FROM");
        if (fromIdx == -1) return null;

        // Extract FROM clause onward (preserves FORCE INDEX / IGNORE INDEX hints)
        String fromAndAfter = query.substring(fromIdx);

        // Find WHERE position
        String upperFrom = fromAndAfter.toUpperCase();
        int whereIdx = upperFrom.indexOf("WHERE");
        int groupByIdx = upperFrom.indexOf("GROUP BY");
        int orderByIdx = upperFrom.indexOf("ORDER BY");
        int limitIdx = upperFrom.indexOf("LIMIT");
        int havingIdx = upperFrom.indexOf("HAVING");

        // Build: SELECT COUNT(*) FROM ... WHERE ...
        // Keep FROM (with hints) and WHERE, strip everything else
        int endIdx = fromAndAfter.length();
        // Find the earliest clause after WHERE that we want to strip
        for (int idx : new int[]{groupByIdx, orderByIdx, limitIdx, havingIdx}) {
            if (idx > 0 && idx < endIdx) endIdx = idx;
        }
        // Also strip trailing semicolon
        String kept = fromAndAfter.substring(0, endIdx).trim();
        if (kept.endsWith(";")) kept = kept.substring(0, kept.length() - 1).trim();

        return "SELECT COUNT(*) " + kept + ";";
    }

    private static final double EPSILON = 1e-10;
    private static final double RELATIVE_TOLERANCE = 1e-6;

    public PolarDBIndexOracle(MySQLGlobalState globalState) {
        this.globalState = globalState;
        this.errors = buildExpectedErrors();
    }

    private ExpectedErrors buildExpectedErrors() {
        ExpectedErrors expectedErrors = ExpectedErrors.newErrors().build();
        PolarDBErrors.addIndexErrors(expectedErrors);
        return expectedErrors;
    }

    @Override
    public void check() throws Exception {
        // A. Ensure tables have sufficient data for the optimizer to consider indexes
        ensureSufficientData();
        Periodic data refresh: every 300 checks, re-insert data
        // to counteract table degradation from DROP COLUMN, DELETE, etc.
        if (++checksSinceLastDataRefresh > 300) {
            checksSinceLastDataRefresh = 0;
            dataPopulated = false; // Force re-run of ensureSufficientData next time
            ensureSufficientData();
        }
        Periodically prune excess indexes to prevent "Too many keys specified" errors.
        // MySQL allows max 64 indexes per table. The fuzzer keeps creating indexes, so we
        // periodically drop excess non-PRIMARY indexes when approaching the limit.
        if (++checksSinceLastIndexPrune >= 50) {
            checksSinceLastIndexPrune = 0;
            pruneExcessIndexes();
        }
        Track total tests and log effective test ratio periodically
        totalTests++;
        if (totalTests % 100 == 0) {
            log("[STATS] total=" + totalTests + " compared=" + queriesCompared
                    + " explainFiltered=" + explainFiltered + " bugsDetected=" + effectiveTests
                    + " (compareRate=" + String.format("%.1f", 100.0 * queriesCompared / Math.max(totalTests, 1)) + "%)");
        }
        try {
            // Removed duplicate modes (subsumed by other modes):
            //   5 (checkOptimizerSwitchIndex) — subsumed by mode 26 (checkOptimizerSwitchDetailed)
            //   6 (checkOrderByIndexSort) — subsumed by mode 18 (checkOrderByLimitIndex)
            //   7 (checkIndexHintConsistency) — subsumed by mode 2+3 (FORCE/IGNORE INDEX vs default)
            //  14 (checkOptimizerHintIndex) — overlaps with mode 2 (checkForceIndexVsDefault)
            // Weight strategy: new/complex features get 2x weight, mature features 1x
            // Rationale: newer and more complex index features have higher bug density
            int mode = Randomly.fromOptions(
                // === HIGH WEIGHT (2x): New/complex features, higher bug probability ===
                12, 12,     // Prefix Index (already found 3 bugs!)
                // Note: mode 24 (FULLTEXT) removed — PolarDB-X does not support FULLTEXT indexes
                17, 17,     // Covering Index (index-only scan)
                15, 15,     // Index Merge (complex optimizer path)
                16, 16,     // Loose Index Scan (rare optimizer path)
                28, 28,     // Deterministic Index Query (lowest IgnoreMe rate)
                25, 25,     // ICP on vs off (newer optimizer feature)
                26, 26,     // Optimizer Switch pairwise (complex interaction)
                20, 20,     // Range Boundary (edge cases)
                19, 19,     // Subquery + Index (complex plan)
                13, 13,     // Hash vs BTree (less common index type)
                23, 23,     // DROP COLUMN with index (DDL edge case)
                // === NORMAL WEIGHT (1x): Mature/stable features ===
                0, 1, 2, 3, 8, 9, 10, 11, 18, 21, 22, 29,
                // === P0 NEW: Functional Index, DML+Index, DESC Index ===
                30, 30,     // Functional Index (expression index, high bug probability)
                31, 31,     // DML + Index consistency (UPDATE/DELETE + verify)
                32, 32,     // DESC Index sort verification
                33, 33,     // Generated Column + Index (P1-1)
                34, 34,     // Collation + Index (P1-2)
                35, 35      // Type Mismatch + Index (P1-3)
            );
            switch (mode) {
            case 0: checkCreateIndexConsistency(); break;
            case 1: checkDropIndexConsistency(); break;
            case 2: checkForceIndexVsDefault(); break;
            case 3: checkIgnoreIndexVsDefault(); break;
            // DEPRECATED: case 4 (checkStraightJoinVsOptimizer) — not testing index, tests JOIN order only
            // case 4: checkStraightJoinVsOptimizer(); break;
            case 8: checkMultiIndexCreate(); break;
            case 9: checkAggregatePlan(); break;
            case 10: checkJoinIndexSelection(); break;
            case 11: checkInvisibleIndex(); break;
            case 12: checkPrefixIndex(); break;
            case 13: checkHashVsBtree(); break;
            // DEPRECATED: case 14 — overlaps with case 2 (checkForceIndexVsDefault)
            // case 14: checkOptimizerHintIndex(); break;
            // === Deep Index Bug Modes (B1-B6) ===
            case 15: checkIndexMerge(); break;           // B2: P0 - Index Merge
            case 16: checkLooseIndexScan(); break;       // B3: P0 - Loose Index Scan
            case 17: checkCoveringIndex(); break;         // B1: P1 - Covering Index
            case 18: checkOrderByLimitIndex(); break;     // B6: P1 - ORDER BY + LIMIT Index
            case 19: checkSubqueryIndex(); break;         // B5: P2 - Subquery + Index
            case 20: checkRangeBoundary(); break;         // B4: P2 - Range Boundary
            case 21: checkTableVerification(); break;      // CHECK TABLE after index
            case 22: checkUniqueIndexConsistency(); break; // UNIQUE INDEX data consistency
            case 23: checkDropColumnWithIndex(); break;    // DROP COLUMN with index
            // === P0: FULLTEXT Index removed for PolarDB-X (not supported) ===
            // case 24: checkFullTextIndex(); break;
            // === P3: New Metamorphic Strategies ===
            case 25: checkICPConsistency(); break;          ICP on vs off
            case 26: checkOptimizerSwitchDetailed(); break; Optimizer switch pairwise
            case 27: checkSQLSemanticEquivalence(); break;  SQL semantic equivalence
            case 28: checkDeterministicIndexQuery(); break;  Deterministic index query
            case 29: checkNullIndexHandling(); break;        // NULL index handling
            // === P0 NEW: Functional Index, DML+Index, DESC Index ===
            case 30: checkFunctionalIndex(); break;          Functional Index
            case 31: checkDMLIndexConsistency(); break;      DML + Index verification
            case 32: checkDescIndexSort(); break;            DESC Index sort
            // === P1: Generated Column, Collation, Type Mismatch ===
            case 33: checkGeneratedColumnIndex(); break;     // P1-1: Generated Column + Index
            case 34: checkCollationIndex(); break;           // P1-2: Collation + Index
            case 35: checkTypeMismatchIndex(); break;        // P1-3: Type Mismatch + Index
            }
        } catch (NullPointerException e) {
            throw new IgnoreMeException();
        }
    }

    // ==================== Mode 0: Create Index Consistency ====================

    private void checkCreateIndexConsistency() throws Exception {
        String queryString = generateIndexAwareOrASTQuery();
        lastQueryString = "[CREATE_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Create a random index
        try {
            SQLQueryAdapter createIndex = MySQLIndexGenerator.create(globalState);
            globalState.executeStatement(createIndex);
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_CREATE_INDEX");
    }

    // ==================== Mode 1: Drop Index Consistency ====================

    private void checkDropIndexConsistency() throws Exception {
        String queryString = generateIndexAwareOrASTQuery();
        lastQueryString = "[DROP_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Find and drop a random non-PRIMARY index
        MySQLSchema.MySQLIndex idxToDrop = getRandomNonPrimaryIndex();
        if (idxToDrop == null) return;

        String tableName = findTableForIndex(idxToDrop);
        if (tableName == null) return;

        try {
            ExpectedErrors dropErrors = new ExpectedErrors();
            dropErrors.add("Can't DROP");
            dropErrors.add("check that column/key exists");
            dropErrors.add("cannot be invisible");
            globalState.executeStatement(new SQLQueryAdapter(
                    "DROP INDEX " + idxToDrop.getIndexName() + " ON " + tableName + ";", dropErrors, true));
            analyzeTable(tableName);
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_DROP_INDEX");
    }

    // ==================== Mode 2: FORCE INDEX vs Default ====================

    private void checkForceIndexVsDefault() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        List<MySQLIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) {
            // Create an index first
            try {
                MySQLIndexGenerator.create(globalState);
                analyzeTable(table.getName());
            } catch (Exception e) {
                return;
            }
            tableIndexes = table.getIndexes();
            if (tableIndexes.isEmpty()) return;
        }

        MySQLIndex forceIdx = Randomly.fromList(tableIndexes);
        String idxName = forceIdx.getIndexName();
        String tblName = table.getName();

        // Use index-aware query: WHERE references this index's columns
        String queryString = generateIndexAwareQueryString(table, forceIdx);
        lastQueryString = "[FORCE_IDX] " + queryString;
        log(queryString);

        // Build forced query first for EXPLAIN comparison
        String forcedQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " FORCE INDEX(" + idxName + ")");

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(forcedQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        Verify FORCE INDEX version effectively uses the index
        if (!isIndexEffectivelyUsed(explainPlan2, idxName)) return;

        // Plan A: Default optimizer
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force specific index
        List<String> r2 = executeQuery(forcedQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_FORCE_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, forcedQuery, "POLARDB_FORCE_INDEX");
    }

    // ==================== Mode 3: IGNORE INDEX vs Default ====================

    private void checkIgnoreIndexVsDefault() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        List<MySQLIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) return;

        MySQLIndex ignoreIdx = Randomly.fromList(tableIndexes);
        String idxName = ignoreIdx.getIndexName();
        String tblName = table.getName();

        // Use index-aware query: WHERE references this index's columns
        String queryString = generateIndexAwareQueryString(table, ignoreIdx);
        lastQueryString = "[IGNORE_IDX] " + queryString;
        log(queryString);

        // Build ignored query first for EXPLAIN comparison
        String ignoredQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " IGNORE INDEX(" + idxName + ")");

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(ignoredQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        // Plan A: Default optimizer
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Ignore specific index → forces different plan
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_IGNORE_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, ignoredQuery, "POLARDB_IGNORE_INDEX");
    }

    // ==================== Mode 4: STRAIGHT_JOIN vs Optimizer ====================

    private void checkStraightJoinVsOptimizer() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().size() < 2) return;

        String queryString = generateASTJoinQuery();
        if (queryString == null) return;

        lastQueryString = "[STRAIGHT_JOIN] " + queryString;
        log(queryString);

        // Build STRAIGHT_JOIN query first for EXPLAIN comparison
        String straightQuery = queryString.replaceFirst("(?i)SELECT\\b", "SELECT STRAIGHT_JOIN");

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(straightQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        // Plan A: Default optimizer
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force STRAIGHT_JOIN (left-to-right join order, disables join reordering)
        List<String> r2 = executeQuery(straightQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_STRAIGHT_JOIN");
    }

    // ==================== Mode 5: Optimizer Switch (Index-related) ====================

    private void checkOptimizerSwitchIndex() throws Exception {
        // Try to generate an index-aware query when possible
        String queryString = null;
        MySQLSchema optSchema = globalState.getSchema();
        List<MySQLTable> optTables = optSchema.getDatabaseTables();
        if (!optTables.isEmpty()) {
            MySQLTable optTable = Randomly.fromList(optTables);
            List<MySQLIndex> optIndexes = optTable.getIndexes();
            if (!optIndexes.isEmpty()) {
                MySQLIndex optIdx = Randomly.fromList(optIndexes);
                queryString = generateIndexAwareQueryString(optTable, optIdx);
            }
        }
        if (queryString == null) queryString = generateASTQuery();
        lastQueryString = "[OPT_SWITCH_IDX] " + queryString;
        log(queryString);

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Disable index-related optimizations
        String switchVal = Randomly.fromOptions(
                "index_condition_pushdown=off,mrr=off,mrr_cost_based=off,skip_scan=off,batched_key_access=off",
                "index_condition_pushdown=off,mrr=on,mrr_cost_based=off",
                "condition_fanout_filter=off,subquery_materialization_cost_based=off",
                "block_nested_loop=off,batched_key_access=on",
                "index_condition_pushdown=off,skip_scan=off");

        // EXPLAIN filter: check if switch actually changes the plan
        List<String> explainPlan1 = getExplainPlan(queryString);
        boolean success = safeSetSwitch(switchVal);
        List<String> r2 = null;
        if (success) {
            try {
                List<String> explainPlan2 = getExplainPlan(queryString);
                if (plansAreDifferent(explainPlan1, explainPlan2)) {
                    r2 = executeQuery(queryString);
                }
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_OPT_SWITCH_IDX");
    }

    // ==================== Mode 6: ORDER BY Index Sort ====================

    private void checkOrderByIndexSort() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Generate a query with ORDER BY using AST
        String queryString = generateASTOrderedQuery();
        if (queryString == null) return;

        // Ensure an index exists
        try {
            MySQLIndexGenerator.create(globalState);
            analyzeAllTables();
        } catch (Exception e) {
            // index creation may fail
        }

        lastQueryString = "[ORDERBY_IDX] " + queryString;
        log(queryString);

        // Plan A: Default optimizer
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force different index strategy via optimizer_switch
        String switchVal = Randomly.fromOptions(
                "index_condition_pushdown=off,mrr=off,skip_scan=off",
                "index_condition_pushdown=off,mrr=on,mrr_cost_based=off",
                "condition_fanout_filter=off");

        // EXPLAIN filter: check if switch actually changes the plan
        List<String> explainPlan1 = getExplainPlan(queryString);
        boolean success = safeSetSwitch(switchVal);
        List<String> r2 = null;
        if (success) {
            try {
                List<String> explainPlan2 = getExplainPlan(queryString);
                if (plansAreDifferent(explainPlan1, explainPlan2)) {
                    r2 = executeQuery(queryString);
                }
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        // Strict comparison: order matters for ORDER BY
        compareResultsStrict(r1, r2, queryString, "POLARDB_ORDERBY_IDX");
    }

    // ==================== Mode 7: Index Hint Consistency ====================

    private void checkIndexHintConsistency() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        List<MySQLIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) return;

        MySQLIndex hintIdx = Randomly.fromList(tableIndexes);
        String idxName = hintIdx.getIndexName();
        String tblName = table.getName();

        // Use index-aware query: WHERE references this index's columns
        String queryString = generateIndexAwareQueryString(table, hintIdx);
        lastQueryString = "[IDX_HINT] " + queryString;
        log(queryString);

        // Plan A: USE INDEX
        String useQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " USE INDEX(" + idxName + ")");

        // Plan B: FORCE INDEX
        String forceQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " FORCE INDEX(" + idxName + ")");

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(useQuery);
        List<String> explainPlan2 = getExplainPlan(forceQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = executeQuery(useQuery);
        if (r1 == null) return;

        List<String> r2 = executeQuery(forceQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_IDX_HINT");
    }

    // ==================== Mode 8: Multi-Index Create ====================

    private void checkMultiIndexCreate() throws Exception {
        String queryString = generateIndexAwareOrASTQuery();
        lastQueryString = "[MULTI_IDX] " + queryString;
        log(queryString);

        // Execute before
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Create multiple indexes
        int numIndexes = Randomly.smallNumber() + 1;
        for (int i = 0; i < numIndexes; i++) {
            try {
                SQLQueryAdapter createIndex = MySQLIndexGenerator.create(globalState);
                globalState.executeStatement(createIndex);
            } catch (Exception e) {
                // index creation may fail
            }
        }
        analyzeAllTables();

        // Execute after
        List<String> r2 = executeQuery(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_MULTI_INDEX");
    }

    // ==================== Mode 9: Aggregate Plan ====================
    Now uses index-aware aggregate query instead of random AST

    private void checkAggregatePlan() throws Exception {
        Generate index-aware aggregate query referencing actual index columns
        String queryString = generateIndexAwareAggregateQuery();
        if (queryString == null) {
            // Fallback to AST aggregate if no indexes available
            queryString = generateASTAggregateQuery();
        }
        if (queryString == null) return;

        lastQueryString = "[AGG_PLAN] " + queryString;
        log(queryString);

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Disable some aggregation optimizations
        String switchVal = Randomly.fromOptions(
                "condition_fanout_filter=off,subquery_materialization_cost_based=off",
                "block_nested_loop=off",
                "index_condition_pushdown=off,mrr=off");

        // EXPLAIN filter: check if switch actually changes the plan
        List<String> explainPlan1 = getExplainPlan(queryString);
        boolean success = safeSetSwitch(switchVal);
        List<String> r2 = null;
        if (success) {
            try {
                List<String> explainPlan2 = getExplainPlan(queryString);
                if (plansAreDifferent(explainPlan1, explainPlan2)) {
                    r2 = executeQuery(queryString);
                }
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_AGG_PLAN");
    }

    // ==================== Mode 10: JOIN Index Selection ====================

    private void checkJoinIndexSelection() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().size() < 2) return;

        String queryString = generateASTJoinQuery();
        if (queryString == null) return;

        lastQueryString = "[JOIN_IDX] " + queryString;
        log(queryString);

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force different join strategy via optimizer_switch
        String switchVal = Randomly.fromOptions(
                "block_nested_loop=off",
                "batched_key_access=on",
                "condition_fanout_filter=off",
                "block_nested_loop=off,batched_key_access=on");

        // EXPLAIN filter: check if switch actually changes the plan
        List<String> explainPlan1 = getExplainPlan(queryString);
        boolean success = safeSetSwitch(switchVal);
        List<String> r2 = null;
        if (success) {
            try {
                List<String> explainPlan2 = getExplainPlan(queryString);
                if (plansAreDifferent(explainPlan1, explainPlan2)) {
                    r2 = executeQuery(queryString);
                }
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_JOIN_IDX");
    }

    // ==================== Mode 11: Invisible Index ====================

    // MySQL 8.0+ INVISIBLE indexes are ignored by the optimizer — creating one must not change results.
    private void checkInvisibleIndex() throws Exception {
        Pick table/column first, then generate query referencing that column
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        MySQLColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Generate query referencing this column for better index coverage
        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IS NOT NULL");
        String queryString;
        if (op.equals("IS NOT NULL")) {
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
        } else {
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + val + ";";
        }

        lastQueryString = "[INVISIBLE_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        String idxName = "inv_idx_" + Math.abs(col.getName().hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + table.getName()
                    + " (" + col.getName() + ") INVISIBLE;", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_INVISIBLE_IDX");

        Additional test: enable use_invisible_indexes to actually exercise
        // the INVISIBLE index, then compare FORCE INDEX vs IGNORE INDEX.
        // This detects bugs where the INVISIBLE index returns incorrect results when used.
        String countWhere = op.equals("IS NOT NULL")
            ? colName + " IS NOT NULL"
            : colName + " " + op + " " + val;
        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + countWhere + ";";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + countWhere + ";";
        boolean switchOk = safeSetSwitch("use_invisible_indexes=on");
        if (switchOk) {
            try {
                List<String> r3 = executeQuery(forceQ);
                if (r3 == null) return;
                List<String> r4 = executeQuery(ignoreQ);
                if (r4 == null) return;
                compareResultsSorted(r3, r4, forceQ, "POLARDB_INVISIBLE_IDX_USED");
            } finally {
                restoreDefaultSettings();
            }
        }
    }

    // ==================== Mode 12: Prefix Index ====================

    // Prefix index on col(N) should give same results as full index for equality.
    private void checkPrefixIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a VARCHAR column
        MySQLTable table = Randomly.fromList(tables);
        List<MySQLColumn> varCharCols = new ArrayList<>();
        for (MySQLColumn col : table.getColumns()) {
            if (col.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
                varCharCols.add(col);
            }
        }
        if (varCharCols.isEmpty()) return;

        MySQLColumn col = Randomly.fromList(varCharCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create a prefix index
        String idxName = "prefix_idx_" + Math.abs(colName.hashCode() % 10000);
        int prefixLen = Randomly.fromOptions(1, 2, 3, 5, 10);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " (" + colName + "(" + prefixLen + "));", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE TABLE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        Use varied WHERE conditions, not just IS NOT NULL
        String val = generateDataAwareValueForType(tblName, col);
        String whereCond;
        int patternType = Randomly.fromOptions(0, 1, 2, 3, 4);
        switch (patternType) {
        case 0: whereCond = colName + " IS NOT NULL"; break;
        case 1: whereCond = colName + " = " + val; break;
        case 2: whereCond = colName + " > " + val; break;
        case 3: whereCond = colName + " < " + val; break;
        default: whereCond = colName + " != " + val + " AND " + colName + " IS NOT NULL"; break;
        }
        String countDefault = "SELECT COUNT(*) FROM " + tblName + " WHERE " + whereCond + ";";
        String countForced = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereCond + ";";

        lastQueryString = "[PREFIX_IDX] " + countDefault;
        log(countDefault);

        List<String> r1 = executeQuery(countDefault);
        if (r1 == null) return;
        List<String> r2 = executeQuery(countForced);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, countDefault, "POLARDB_PREFIX_IDX");
    }

    // ==================== Mode 13: HASH vs BTREE ====================
    Now uses varied WHERE conditions instead of only IS NOT NULL

    // For InnoDB, HASH is silently converted to BTREE; tests that different index types don't corrupt results.
    private void checkHashVsBtree() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Create two indexes: one HASH, one BTREE
        String hashIdx = "hash_idx_" + Math.abs(colName.hashCode() % 10000);
        String btreeIdx = "btree_idx_" + Math.abs(colName.hashCode() % 10000);
        boolean hashCreated = false, btreeCreated = false;

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + hashIdx + " USING HASH ON " + tblName + " (" + colName + ");", errors, true));
            hashCreated = true;
        } catch (Exception e) { }
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + btreeIdx + " USING BTREE ON " + tblName + " (" + colName + ");", errors, true));
            btreeCreated = true;
        } catch (Exception e) { }

        if (!hashCreated || !btreeCreated) return;
        analyzeTable(tblName);

        Use varied WHERE conditions, not just IS NOT NULL ORDER BY
        String val = generateDataAwareValueForType(tblName, col);
        String whereCond;
        int patternType = Randomly.fromOptions(0, 1, 2, 3, 4, 5);
        switch (patternType) {
        case 0: whereCond = colName + " IS NOT NULL"; break;
        case 1: whereCond = colName + " = " + val; break;
        case 2: whereCond = colName + " > " + val; break;
        case 3: whereCond = colName + " < " + val; break;
        case 4: whereCond = colName + " >= " + val; break;
        default: whereCond = colName + " IS NOT NULL AND " + colName + " != " + val; break;
        }

        String queryString = "SELECT " + colName + " FROM " + tblName + " WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 100;";
        lastQueryString = "[HASH_VS_BTREE] " + queryString;
        log(queryString);

        String forceHash = "SELECT " + colName + " FROM " + tblName + " FORCE INDEX(" + hashIdx + ") WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 100;";
        String forceBtree = "SELECT " + colName + " FROM " + tblName + " FORCE INDEX(" + btreeIdx + ") WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 100;";

        List<String> r1 = executeQuery(forceHash);
        if (r1 == null) return;
        List<String> r2 = executeQuery(forceBtree);
        if (r2 == null) return;

        compareResultsStrict(r1, r2, queryString, "POLARDB_HASH_VS_BTREE");
        if (lastCompareFiltered) countStarFallback(forceHash, forceBtree, "POLARDB_HASH_VS_BTREE");
    }

    // ==================== Mode 14: Optimizer Hint Index ====================

    private void checkOptimizerHintIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Generate a query using AST
        MySQLSelect select = generateComplexSelect();
        if (select == null) return;

        // Plan A: No hint (default)
        String queryString = MySQLVisitor.asString(select) + ";";
        lastQueryString = "[OPT_HINT_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Add optimizer hint
        MySQLHintGenerator.generateHints(select, tables);
        String hintedQuery = MySQLVisitor.asString(select) + ";";

        // EXPLAIN filter: skip if hints didn't change the plan
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(hintedQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r2 = executeQuery(hintedQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_OPT_HINT_IDX");
    }

    // ==================== Mode 15: Index Merge (B2 - P0) ====================

    Mode 15: Uses generateDataAwareValueForType for better index hit rate
    private void checkIndexMerge() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        List<MySQLColumn> cols = new ArrayList<>(table.getColumns());
        Collections.shuffle(cols);
        MySQLColumn col1 = cols.get(0);
        MySQLColumn col2 = cols.get(1);
        String tblName = table.getName();
        String idx1Name = "imerge_a_" + Math.abs(col1.getName().hashCode() % 10000);
        String idx2Name = "imerge_b_" + Math.abs(col2.getName().hashCode() % 10000);
        boolean created1 = false, created2 = false;
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idx1Name + " ON " + tblName + " (" + col1.getName() + ");", errors, true));
            created1 = true;
        } catch (Exception e) { }
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idx2Name + " ON " + tblName + " (" + col2.getName() + ");", errors, true));
            created2 = true;
        } catch (Exception e) { }
        if (!created1 || !created2) return;
        analyzeTable(tblName);
        Use data-aware values instead of random values for better index hit
        String val1 = generateDataAwareValueForType(tblName, col1);
        String val2 = generateDataAwareValueForType(tblName, col2);
        String whereClause = col1.getName() + " = " + val1 + " OR " + col2.getName() + " = " + val2;
        if (Randomly.getBoolean()) {
            String val3 = generateDataAwareValueForType(tblName, col1);
            whereClause = col1.getName() + " BETWEEN " + val1 + " AND " + val3
                    + " OR " + col2.getName() + " IN (" + val2 + ", " + generateDataAwareValueForType(tblName, col2) + ")";
        }
        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereClause + ";";
        lastQueryString = "[INDEX_MERGE] " + queryString;
        log(queryString);

        Add EXPLAIN filter: only compare results if disabling
        // index_merge actually changes the execution plan. Without this filter,
        // many tests compare identical full-table-scan plans → wasted effort.
        List<String> plan1 = getExplainPlan(queryString);
        boolean success = safeSetSwitch("index_merge_intersection=off,index_merge_sort_union=off,index_merge_union=off");
        if (!success) return;
        List<String> plan2 = null;
        List<String> r2 = null;
        try {
            plan2 = getExplainPlan(queryString);
            if (!plansAreDifferent(plan1, plan2)) {
                // Plans are identical — index_merge was not being used anyway
                return;
            }
            // Plans differ — execute and compare
            List<String> r1 = executeQuery(queryString);
            if (r1 == null) return;
            r2 = executeQuery(queryString);
            if (r2 == null) return;
            compareResultsSorted(r1, r2, queryString, "POLARDB_INDEX_MERGE");
        } finally {
            restoreDefaultSettings();
        }
    }

    // ==================== Mode 16: Loose Index Scan (B3 - P0) ====================

    private void checkLooseIndexScan() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        List<MySQLColumn> cols = new ArrayList<>(table.getColumns());
        Collections.shuffle(cols);
        MySQLColumn col1 = cols.get(0);
        MySQLColumn col2 = cols.get(1);
        String tblName = table.getName();
        String idxName = "loose_idx_" + Math.abs(col1.getName().hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " (" + col1.getName() + ", " + col2.getName() + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }
        String aggFunc = Randomly.fromOptions("MIN", "MAX", "COUNT", "SUM");
        String queryString = "SELECT " + col1.getName() + ", " + aggFunc + "(" + col2.getName()
                + ") FROM " + tblName + " GROUP BY " + col1.getName() + ";";
        lastQueryString = "[LOOSE_SCAN] " + queryString;
        log(queryString);

        Use FORCE INDEX vs IGNORE INDEX comparison instead of
        // the incorrect "loosescan=off" optimizer_switch (which controls semijoin
        // loose scan, NOT the GROUP BY Loose Index Scan optimization).
        // Loose Index Scan for GROUP BY has no dedicated optimizer_switch —
        // it's automatically chosen by the optimizer based on index structure and cost.
        String forceQuery = "SELECT " + col1.getName() + ", " + aggFunc + "(" + col2.getName()
                + ") FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                + " GROUP BY " + col1.getName() + ";";
        String ignoreQuery = "SELECT " + col1.getName() + ", " + aggFunc + "(" + col2.getName()
                + ") FROM " + tblName + " IGNORE INDEX(" + idxName + ")"
                + " GROUP BY " + col1.getName() + ";";

        // EXPLAIN filter: only compare if plans actually differ
        List<String> plan1 = getExplainPlan(forceQuery);
        List<String> plan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(plan1, plan2)) return;

        List<String> r1 = executeQuery(forceQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQuery);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQuery, "POLARDB_LOOSE_SCAN");
    }

    // ==================== Mode 17: Covering Index (B1 - P1) ====================
    Now verifies "Using index" in EXPLAIN before comparing

    private void checkCoveringIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        List<MySQLColumn> cols = new ArrayList<>(table.getColumns());
        Collections.shuffle(cols);
        int numCols = Math.min(cols.size(), Randomly.fromOptions(2, 3));
        List<MySQLColumn> idxCols = cols.subList(0, numCols);
        String tblName = table.getName();
        String idxColList = idxCols.stream().map(MySQLColumn::getName).collect(Collectors.joining(", "));
        String idxName = "cover_idx_" + Math.abs(idxCols.get(0).getName().hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + idxColList + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }
        String selectCols = idxCols.stream().map(MySQLColumn::getName).collect(Collectors.joining(", "));
        MySQLColumn whereCol = idxCols.get(0);
        String val = generateDataAwareValueForType(tblName, whereCol);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String queryString = "SELECT " + selectCols + " FROM " + tblName
                + " WHERE " + whereCol.getName() + " " + op + " " + val + " ORDER BY " + idxCols.get(0).getName() + ";";
        lastQueryString = "[COVER_IDX] " + queryString;
        log(queryString);
        String forceQuery = "SELECT " + selectCols + " FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                + " WHERE " + whereCol.getName() + " " + op + " " + val + " ORDER BY " + idxCols.get(0).getName() + ";";

        Verify FORCE INDEX version triggers index-only scan ("Using index")
        List<String> explainForce = getExplainPlan(forceQuery);
        boolean isIndexOnlyScan = planHasExtra(explainForce, "Using index");
        if (!isIndexOnlyScan) {
            // FORCE INDEX didn't trigger index-only scan — SELECT may include non-index columns
            // Skip this test as it won't effectively test covering index behavior
            return;
        }

        List<String> r1 = executeQuery(forceQuery);
        if (r1 == null) return;
        String ignoreQuery = "SELECT " + selectCols + " FROM " + tblName + " IGNORE INDEX(" + idxName + ")"
                + " WHERE " + whereCol.getName() + " " + op + " " + val + " ORDER BY " + idxCols.get(0).getName() + ";";
        List<String> r2 = executeQuery(ignoreQuery);
        if (r2 == null) return;
        compareResultsStrict(r1, r2, queryString, "POLARDB_COVER_IDX");
        if (lastCompareFiltered) countStarFallback(forceQuery, ignoreQuery, "POLARDB_COVER_IDX");
    }

    // ==================== Mode 18: ORDER BY + LIMIT Index (B6 - P1) ====================
    Uses generateDataAwareValueForType instead of random values

    private void checkOrderByLimitIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "ordlim_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }
        int limit = Randomly.fromOptions(1, 5, 10, 20, 50);
        String direction = Randomly.fromOptions("ASC", "DESC");
        String whereClause = "";
        if (Randomly.getBoolean()) {
            Use data-aware values for better index hit rate
            String val = generateDataAwareValueForType(tblName, col);
            String op = Randomly.fromOptions(">", "<", ">=", "<=", "!=");
            whereClause = " WHERE " + colName + " " + op + " " + val;
        }
        String queryString = "SELECT * FROM " + tblName + whereClause
                + " ORDER BY " + colName + " " + direction + " LIMIT " + limit + ";";
        lastQueryString = "[ORDLIM_IDX] " + queryString;
        log(queryString);
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;
        String ignoreQuery = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ")"
                + whereClause + " ORDER BY " + colName + " " + direction + " LIMIT " + limit + ";";
        List<String> r2 = executeQuery(ignoreQuery);
        if (r2 == null) return;
        String upperQuery = queryString.toUpperCase();
        if (upperQuery.contains("LIMIT") && !hasUniqueOrderByTieBreaker(queryString)) {
            compareResultsSorted(r1, r2, queryString, "POLARDB_ORDLIM_IDX");
            if (lastCompareFiltered) countStarFallback(queryString, ignoreQuery, "POLARDB_ORDLIM_IDX");
        } else {
            compareResultsStrict(r1, r2, queryString, "POLARDB_ORDLIM_IDX");
            if (lastCompareFiltered) countStarFallback(queryString, ignoreQuery, "POLARDB_ORDLIM_IDX");
        }
    }

    // ==================== Mode 19: Subquery + Index (B5 - P2) ====================

    private void checkSubqueryIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = new ArrayList<>(schema.getDatabaseTables());
        if (tables.size() < 2) return;
        Collections.shuffle(tables);
        MySQLTable outerTable = tables.get(0);
        MySQLTable innerTable = tables.get(1);
        if (outerTable.getColumns().isEmpty() || innerTable.getColumns().isEmpty()) return;
        String outerTbl = outerTable.getName();
        String innerTbl = innerTable.getName();
        MySQLColumn outerCol = Randomly.fromList(outerTable.getColumns());
        MySQLColumn innerCol = Randomly.fromList(innerTable.getColumns());
        String outerIdx = "sq_out_" + Math.abs(outerCol.getName().hashCode() % 10000);
        String innerIdx = "sq_in_" + Math.abs(innerCol.getName().hashCode() % 10000);
        try {
            safeCreateIndex(outerTbl,
                    "CREATE INDEX " + outerIdx + " ON " + outerTbl + " (" + outerCol.getName() + ");");
        } catch (Exception e) { }
        try {
            safeCreateIndex(innerTbl,
                    "CREATE INDEX " + innerIdx + " ON " + innerTbl + " (" + innerCol.getName() + ");");
        } catch (Exception e) { }
        analyzeAllTables();
        String queryString;
        if (Randomly.getBoolean()) {
            queryString = "SELECT * FROM " + outerTbl + " WHERE " + outerCol.getName()
                    + " IN (SELECT " + innerCol.getName() + " FROM " + innerTbl + ");";
        } else {
            queryString = "SELECT * FROM " + outerTbl
                    + " WHERE EXISTS (SELECT 1 FROM " + innerTbl
                    + " WHERE " + innerTbl + "." + innerCol.getName() + " = " + outerTbl + "." + outerCol.getName() + ");";
        }
        lastQueryString = "[SUBQ_IDX] " + queryString;
        log(queryString);
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;
        String switchVal = Randomly.fromOptions(
                "subquery_materialization_cost_based=off",
                "firstmatch=off,loosescan=off,materialization=off",
                "semijoin=off");
        boolean success = safeSetSwitch(switchVal);
        List<String> r2 = null;
        if (success) {
            try { r2 = executeQuery(queryString); } finally { restoreDefaultSettings(); }
        }
        if (r2 == null) return;
        compareResultsSorted(r1, r2, queryString, "POLARDB_SUBQ_IDX");
    }

    // ==================== Mode 20: Range Boundary (B4 - P2) ====================
    Uses generateDataAwareValueForType instead of random values

    private void checkRangeBoundary() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "range_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }
        Randomly r = globalState.getRandomly();
        Use MIN/MAX for range boundaries to avoid impossible ranges (low > high)
        // This was the #1 cause of empty result sets in MySQL testing (~50% of range queries were useless)
        String[] minMax = getColumnMinMax(tblName, colName);
        getColumnMinMax() returns raw JDBC strings without quotes.
        // For VARCHAR columns, we must wrap values in quotes for valid SQL syntax.
        if (minMax != null && col.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
            if (!minMax[0].startsWith("'")) {
                minMax[0] = "'" + minMax[0].replace("'", "''") + "'";
            }
            if (!minMax[1].startsWith("'")) {
                minMax[1] = "'" + minMax[1].replace("'", "''") + "'";
            }
        }
        String val = generateDataAwareValueForType(tblName, col);
        String lowVal, highVal;
        if (minMax != null) {
            lowVal = minMax[0]; // guaranteed MIN
            highVal = minMax[1]; // guaranteed MAX
        } else {
            // Fallback: use two sampled values, but ensure they're in range via column data
            lowVal = generateDataAwareValueForType(tblName, col);
            highVal = generateDataAwareValueForType(tblName, col);
        }
        String whereClause;
        int variant = r.getInteger(0, 6);
        switch (variant) {
        case 0: whereClause = colName + " BETWEEN " + lowVal + " AND " + highVal + " OR " + colName + " IS NULL"; break;
        case 1:
            StringBuilder inList = new StringBuilder();
            for (int i = 0; i < r.getInteger(3, 10); i++) {
                if (i > 0) inList.append(", ");
                inList.append(generateDataAwareValueForType(tblName, col));
            }
            whereClause = colName + " IN (" + inList + ")";
            break;
        case 2: whereClause = colName + " > " + val + " OR " + colName + " IS NULL"; break;
        case 3: whereClause = colName + " != " + val + " AND " + colName + " IS NOT NULL"; break;
        case 4: whereClause = colName + " >= " + lowVal + " AND " + colName + " <= " + highVal; break;
        default: whereClause = colName + " > " + lowVal + " AND (" + colName + " < " + highVal + " OR " + colName + " IS NULL)"; break;
        }
        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereClause + ";";
        lastQueryString = "[RANGE_BOUND] " + queryString;
        log(queryString);
        String forceQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereClause + ";";
        List<String> r1 = executeQuery(forceQuery);
        if (r1 == null) return;
        String ignoreQuery = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereClause + ";";
        List<String> r2 = executeQuery(ignoreQuery);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, queryString, "POLARDB_RANGE_BOUND");
        if (lastCompareFiltered) countStarFallback(forceQuery, ignoreQuery, "POLARDB_RANGE_BOUND");
    }

    // ==================== Mode 21: CHECK TABLE Verification ====================

    // Runs CHECK TABLE after index creation to detect InnoDB index corruption bugs.
    private void checkTableVerification() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        String tblName = table.getName();

        // Verify the table actually exists in the database (Java-side schema may be stale
        // due to DDL operations like RENAME, DROP, failed ALTER TABLE, etc.)
        try {
            List<String> existence = executeQuery(
                    "SELECT TABLE_NAME FROM information_schema.TABLES WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '"
                            + tblName + "';");
            if (existence == null || existence.isEmpty()) return; // Table doesn't exist — stale cache, not a bug
        } catch (Exception e) {
            return; // Cannot verify existence — skip
        }

        // First, create some indexes to stress-test
        try {
            MySQLIndexGenerator.create(globalState);
            analyzeTable(tblName);
        } catch (Exception e) { }

        // Re-verify existence after index creation (index DDL may fail and drop the table)
        try {
            List<String> existence = executeQuery(
                    "SELECT TABLE_NAME FROM information_schema.TABLES WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '"
                            + tblName + "';");
            if (existence == null || existence.isEmpty()) return;
        } catch (Exception e) {
            return;
        }

        // Run CHECK TABLE
        String checkQuery = "CHECK TABLE " + tblName + " EXTENDED;";
        lastQueryString = "[CHECK_TABLE] " + checkQuery;
        log(checkQuery);

        try {
            List<String> result = executeQuery(checkQuery);
            if (result == null) return;

            // Check for non-OK status in results, but skip "doesn't exist" (stale schema false positive)
            for (String row : result) {
                if (row.contains("doesn't exist") || row.contains("does not exist")) {
                    // Table vanished between existence check and CHECK TABLE — stale schema, not a bug
                    return;
                }
                if (row.contains("error") || row.contains("Error") || row.contains("warning") || row.contains("Warning")) {
                    throw new AssertionError("POLARDB_CHECK_TABLE: CHECK TABLE reported issue!\n"
                            + "Table: " + tblName + "\nResult: " + row);
                }
            }
        } catch (AssertionError e) {
            throw e; // Re-throw our detected bugs
        } catch (Exception e) {
            // CHECK TABLE itself might fail — that could be a bug too
            return;
        }

        // Also: compare COUNT(*) before and after ANALYZE to detect stats inconsistency
        String countQuery = "SELECT COUNT(*) FROM " + tblName + ";";
        List<String> countBefore = executeQuery(countQuery);
        if (countBefore == null) return;

        try {
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE TABLE " + tblName + ";", true));
        } catch (Exception e) { return; }

        List<String> countAfter = executeQuery(countQuery);
        if (countAfter == null) return;

        compareResultsSorted(countBefore, countAfter, countQuery, "POLARDB_CHECK_TABLE");
    }

    // ==================== Mode 22: UNIQUE INDEX Consistency ====================

    private void checkUniqueIndexConsistency() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        Exclude AUTO_INCREMENT columns — CREATE UNIQUE INDEX on them triggers
        // "ALTER TABLE causes auto_increment resequencing" error.
        List<MySQLColumn> nonAutoIncCols = new ArrayList<>();
        for (MySQLColumn c : table.getColumns()) {
            if (!c.isAutoIncrement()) {
                nonAutoIncCols.add(c);
            }
        }
        if (nonAutoIncCols.isEmpty()) return;
        MySQLColumn col = Randomly.fromList(nonAutoIncCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Count rows before
        String countBefore = "SELECT COUNT(*) FROM " + tblName + ";";
        List<String> r1 = executeQuery(countBefore);
        if (r1 == null) return;

        Before CREATE UNIQUE INDEX, make all INVISIBLE indexes on this column VISIBLE.
        // MySQL's CREATE UNIQUE INDEX can internally rebuild indexes and fail with
        // "A primary key index cannot be invisible" if there are invisible indexes on the column.
        makeColumnIndexesVisible(tblName, colName);

        // Create UNIQUE INDEX
        String idxName = "uniq_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE UNIQUE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) {
            // UNIQUE constraint violation means duplicates exist — that's expected
            return;
        }

        // Count rows after — should be the same
        List<String> r2 = executeQuery(countBefore);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, countBefore, "POLARDB_UNIQUE_IDX_COUNT");

        // Compare query with/without FORCE INDEX on the unique index
        String queryDefault = "SELECT " + colName + " FROM " + tblName + " WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " LIMIT 100;";
        String queryForced = "SELECT " + colName + " FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " LIMIT 100;";

        lastQueryString = "[UNIQUE_IDX] " + queryDefault;
        log(queryDefault);

        List<String> r3 = executeQuery(queryDefault);
        if (r3 == null) return;
        List<String> r4 = executeQuery(queryForced);
        if (r4 == null) return;

        compareResultsStrict(r3, r4, queryDefault, "POLARDB_UNIQUE_IDX");
        if (lastCompareFiltered) countStarFallback(queryDefault, queryForced, "POLARDB_UNIQUE_IDX");
    }

    // ==================== Mode 23: DROP COLUMN with Index ====================

    private void checkDropColumnWithIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return; // Need at least 2 columns to drop one

        String tblName = table.getName();

        Find columns that are safe to drop — exclude columns referenced by
        // generated columns. MySQL rejects DROP COLUMN if the column has a generated column
        // dependency ("Column 'X' has a generated column dependency").
        // We query information_schema.COLUMNS to find generated columns and their expressions,
        // then exclude any base columns referenced in those expressions.
        Set<String> columnsWithGenDependency = getColumnsWithGeneratedDependency(tblName);

        // Find a non-primary-key column that is safe to drop
        List<MySQLColumn> candidates = new ArrayList<>();
        for (MySQLColumn col : table.getColumns()) {
            if (!col.isPrimaryKey() && !columnsWithGenDependency.contains(col.getName().toLowerCase())) {
                candidates.add(col);
            }
        }
        if (candidates.isEmpty()) return;

        MySQLColumn col = Randomly.fromList(candidates);
        String colName = col.getName();

        // Create an index on this column
        Before CREATE INDEX, make all INVISIBLE indexes on this table VISIBLE.
        // MySQL's CREATE INDEX internally triggers a table rebuild, and can fail with
        // "A primary key index cannot be invisible" if there are invisible indexes on the table.
        makeTableIndexesVisible(tblName);

        String idxName = "dropcol_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }

        // Query with the column
        String queryBefore = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
        lastQueryString = "[DROP_COL_IDX] " + queryBefore;
        log(queryBefore);

        List<String> r1 = executeQuery(queryBefore);
        // r1 can be null — we still try the DROP

        Before DROP COLUMN, make all INVISIBLE indexes on this column VISIBLE.
        // MySQL's ALTER TABLE DROP COLUMN internally rebuilds indexes, and can fail with
        // "A primary key index cannot be invisible" if there are invisible indexes on the column.
        // Making them visible first avoids this false-positive trigger.
        makeColumnIndexesVisible(tblName, colName);

        // Drop the column (this should also drop the index)
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "ALTER TABLE " + tblName + " DROP COLUMN " + colName + ";", errors, true));
            analyzeAllTables();
        } catch (Exception e) {
            // ALTER TABLE DROP COLUMN may fail for various reasons
            return;
        }

        // Verify the index was removed
        // Refresh schema
        try {
            globalState.updateSchema();
        } catch (Exception e) { return; }

        // Try a simple query to make sure the table isn't corrupted
        String queryAfter = "SELECT COUNT(*) FROM " + tblName + ";";
        try {
            List<String> r2 = executeQuery(queryAfter);
            // If we get here without error, the table is still queryable
        } catch (Exception e) {
            // Table corruption after DROP COLUMN — this IS a bug
            throw new AssertionError("POLARDB_DROP_COL_IDX: Table corrupted after DROP COLUMN!\n"
                    + "Table: " + tblName + ", Dropped column: " + colName + "\nError: " + e.getMessage());
        }
    }


    // MySQL rejects DROP COLUMN when the column is referenced by a generated column expression.
    // Returns lowercased names of both generated columns and their base column dependencies.
    private Set<String> getColumnsWithGeneratedDependency(String tableName) {
        Set<String> blocked = new HashSet<>();
        try {
            // Find all generated columns and their expressions for this table
            String query = "SELECT COLUMN_NAME, GENERATION_EXPRESSION FROM information_schema.COLUMNS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName
                    + "' AND EXTRA LIKE '%GENERATED%';";
            List<String> result = executeQuery(query);
            if (result == null || result.isEmpty()) return blocked;

            // For each generated column, extract base column references from the expression
            Set<String> generatedColumns = new HashSet<>();
            for (String row : result) {
                if (row == null || row.isEmpty()) continue;
                // Result format: col_name ||| generation_expression
                String[] parts = row.split(java.util.regex.Pattern.quote(COLUMN_DELIMITER));
                if (parts.length >= 1) {
                    generatedColumns.add(parts[0].trim().toLowerCase());
                }
                if (parts.length >= 2) {
                    // Parse the generation expression for column references
                    String expr = parts[1].trim();
                    // Match column name patterns like c0, c1, c2, etc. and idx_t0.c0, t0.c0
                    java.util.regex.Pattern colPattern = java.util.regex.Pattern.compile("\\b(c\\d+)\\b");
                    java.util.regex.Matcher m = colPattern.matcher(expr);
                    while (m.find()) {
                        blocked.add(m.group(1).toLowerCase());
                    }
                    // Also match patterns like idx_t0.c0 or t0.c0
                    java.util.regex.Pattern qualifiedCol = java.util.regex.Pattern.compile("\\b\\w+\\.(c\\d+)\\b");
                    m = qualifiedCol.matcher(expr);
                    while (m.find()) {
                        blocked.add(m.group(1).toLowerCase());
                    }
                }
            }
            // Also block the generated columns themselves
            blocked.addAll(generatedColumns);
        } catch (Exception e) {
            // Best-effort: if we can't query, return empty set (fallback to error handling)
        }
        return blocked;
    }

    // Makes INVISIBLE indexes on a column VISIBLE before ALTER TABLE DROP COLUMN.
    // MySQL rejects column drops that trigger a table rebuild if any index is invisible.
    private void makeColumnIndexesVisible(String tableName, String colName) {
        try {
            // Query information_schema for invisible indexes on this column
            String query = "SELECT DISTINCT s.INDEX_NAME FROM information_schema.STATISTICS s "
                    + "JOIN information_schema.TABLES t ON s.TABLE_SCHEMA = t.TABLE_SCHEMA AND s.TABLE_NAME = t.TABLE_NAME "
                    + "JOIN information_schema.COLUMNS c ON s.TABLE_SCHEMA = c.TABLE_SCHEMA AND s.TABLE_NAME = c.TABLE_NAME AND s.COLUMN_NAME = c.COLUMN_NAME "
                    + "WHERE s.TABLE_SCHEMA = DATABASE() AND s.TABLE_NAME = '" + tableName + "' "
                    + "AND s.COLUMN_NAME = '" + colName + "';";
            List<String> invisibleIndexes = executeQuery(
                    "SELECT INDEX_NAME FROM information_schema.STATISTICS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName + "' "
                    + "AND COLUMN_NAME = '" + colName + "' "
                    + "AND INDEX_NAME != 'PRIMARY';");
            if (invisibleIndexes == null || invisibleIndexes.isEmpty()) return;

            // For each index on this column, try to make it visible
            ExpectedErrors alterErrors = new ExpectedErrors();
            alterErrors.add("cannot be invisible");
            alterErrors.add("doesn't exist");
            for (String idxName : invisibleIndexes) {
                // Strip any formatting artifacts from query result
                String cleanIdxName = idxName.trim();
                try {
                    Use backticks around index name to handle
                    // reserved words and special characters safely.
                    globalState.executeStatement(new SQLQueryAdapter(
                            "ALTER TABLE " + tableName + " ALTER INDEX `" + cleanIdxName + "` VISIBLE;",
                            alterErrors, true));
                } catch (Exception e) {
                    // Ignore — some indexes (e.g., PRIMARY) cannot be made invisible/visible
                }
            }
        } catch (Exception e) {
            // Best-effort: if we can't query information_schema, proceed anyway
        }
    }

    // Makes all INVISIBLE indexes on the table VISIBLE before CREATE INDEX to prevent
    // "A primary key index cannot be invisible" errors during the table rebuild.
    private void safeCreateIndex(String tableName, String createIndexSQL) throws Exception {
        makeTableIndexesVisible(tableName);
        globalState.executeStatement(new SQLQueryAdapter(createIndexSQL, errors, true));
    }

    private void makeTableIndexesVisible(String tableName) {
        try {
            List<String> allIndexes = executeQuery(
                    "SELECT INDEX_NAME FROM information_schema.STATISTICS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName + "' "
                    + "AND INDEX_NAME != 'PRIMARY';");
            if (allIndexes == null || allIndexes.isEmpty()) return;

            ExpectedErrors alterErrors = new ExpectedErrors();
            alterErrors.add("cannot be invisible");
            alterErrors.add("doesn't exist");
            for (String idxName : allIndexes) {
                String cleanIdxName = idxName.trim();
                if (cleanIdxName.isEmpty()) continue;
                try {
                    globalState.executeStatement(new SQLQueryAdapter(
                            "ALTER TABLE " + tableName + " ALTER INDEX `" + cleanIdxName + "` VISIBLE;",
                            alterErrors, true));
                } catch (Exception e) {
                    // Ignore — some indexes (e.g., PRIMARY) cannot be made invisible/visible
                }
            }
        } catch (Exception e) {
            // Best-effort: if we can't query information_schema, proceed anyway
        }
    }

    // Samples actual column values so WHERE conditions match real data (not random values missing the data).
    private List<String> sampleColumnValues(String tableName, String colName, int limit) {
        try {
            String query = "SELECT " + colName + " FROM " + tableName
                    + " WHERE " + colName + " IS NOT NULL ORDER BY RAND() LIMIT " + limit + ";";
            return executeQuery(query);
        } catch (Exception e) {
            return null;
        }
    }

    // ==================== AST-Based Query Generation ====================

    private MySQLSelect generateComplexSelect() {
        MySQLSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return null;

        try {
            MySQLTables targetTables = schema.getRandomTableNonEmptyTables();
            List<MySQLColumn> columns = targetTables.getColumns();
            List<MySQLTable> tables = targetTables.getTables();

            MySQLExpressionGenerator gen = new MySQLExpressionGenerator(globalState).setColumns(columns);

            MySQLSelect select = new MySQLSelect();
            select.setSelectType(Randomly.fromOptions(SelectType.values()));

            // Fetch columns — use AST-generated expressions
            List<MySQLExpression> fetchColumns = new ArrayList<>();
            if (Randomly.getBooleanWithRatherLowProbability()) {
                fetchColumns.add(MySQLConstant.createIntConstant(1));
            } else {
                List<MySQLColumn> subset = Randomly.nonEmptySubset(columns);
                for (int i = 0; i < subset.size(); i++) {
                    fetchColumns.add(gen.generateExpression(0));
                }
            }
            select.setFetchColumns(fetchColumns);

            // JOINs — 40%+ queries involve multi-table JOINs for index coverage testing
            List<MySQLJoin> complexJoinClauses = new ArrayList<>();
            if (tables.size() > 1 && (Randomly.getBoolean() || Randomly.getBoolean())) {
                // 75% chance: use index-friendly JOIN conditions
                if (Randomly.getBoolean()) {
                    // Exclude the driving table from join candidates to prevent
                    // "Not unique table/alias" when the same table appears in both
                    // FROM and JOIN clauses
                    List<MySQLTable> joinCandidates = new ArrayList<>(tables.subList(1, tables.size()));
                    if (!joinCandidates.isEmpty()) {
                        complexJoinClauses = MySQLJoin.getRandomJoinClauses(joinCandidates, globalState);
                    }
                } else {
                    complexJoinClauses = generateIndexFriendlyJoinClauses(tables);
                }
            }

            // FROM tables: only include the first (driving) table when JOINs are present.
            // When a JOIN table has the same name as the driving table, assign aliases
            // to avoid "Not unique table/alias" error.
            List<MySQLExpression> fromList = new ArrayList<>();
            if (!complexJoinClauses.isEmpty()) {
                String drivingName = tables.get(0).getName();
                boolean hasDuplicateName = false;
                int aliasCounter = 0;
                for (MySQLJoin jc : complexJoinClauses) {
                    if (jc.getTable().getName().equals(drivingName)) {
                        hasDuplicateName = true;
                        jc.setAlias("t_" + aliasCounter++);
                    }
                }
                if (hasDuplicateName) {
                    fromList.add(new MySQLTableReference(tables.get(0), "t0"));
                } else {
                    fromList.add(new MySQLTableReference(tables.get(0)));
                }
            } else {
                for (MySQLTable t : tables) {
                    fromList.add(new MySQLTableReference(t));
                }
            }
            select.setFromList(fromList);
            select.setJoinClauses(complexJoinClauses);

            // WHERE — B. Index-aware WHERE: 70% chance to use index-friendly condition
            if (Randomly.getBooleanWithRatherLowProbability() || Randomly.getBoolean()) {
                MySQLExpression indexWhere = tryGenerateIndexFriendlyWhere(tables, gen);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                } else {
                    select.setWhereClause(gen.generateExpression(0));
                }
            }

            // GROUP BY
            if (Randomly.getBooleanWithRatherLowProbability()) {
                List<MySQLExpression> groupByExprs = new ArrayList<>();
                for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
                    groupByExprs.add(gen.generateExpression(0));
                }
                select.setGroupByExpressions(groupByExprs);
                if (Randomly.getBoolean()) {
                    select.setHavingClause(gen.generateExpression(0));
                }
            }

            // ORDER BY
            if (Randomly.getBoolean()) {
                select.setOrderByClauses(gen.generateOrderBys());
            }

            // Semantic fix: DISTINCT/DISTINCTROW + ORDER BY on non-SELECT columns is
            // invalid in SQL standard.  Since fetch columns and ORDER BY are generated
            // independently, downgrade to ALL to avoid false positives.
            // This does NOT mask real bugs — the Index Oracle tests index plan
            // correctness, not DISTINCT semantics.
            if (select.getOrderByClauses() != null && !select.getOrderByClauses().isEmpty()) {
                SelectType st = select.getFromOptions();
                if (st == SelectType.DISTINCT || st == SelectType.DISTINCTROW) {
                    select.setSelectType(SelectType.ALL);
                }
            }

            // LIMIT / OFFSET
            if (Randomly.getBoolean()) {
                select.setLimitClause(MySQLConstant.createIntConstant(
                        Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));
                if (Randomly.getBoolean()) {
                    select.setOffsetClause(MySQLConstant.createIntConstant(0));
                }
            }

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    private MySQLSelect generateAggregateSelect() {
        MySQLSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return null;

        try {
            MySQLTables targetTables = schema.getRandomTableNonEmptyTables();
            List<MySQLColumn> columns = targetTables.getColumns();

            MySQLExpressionGenerator gen = new MySQLExpressionGenerator(globalState).setColumns(columns);

            MySQLSelect select = new MySQLSelect();
            select.setFromList(targetTables.getTables().stream()
                    .map(t -> (MySQLExpression) new MySQLTableReference(t))
                    .collect(Collectors.toList()));

            // Aggregate fetch columns
            List<MySQLExpression> fetchColumns = new ArrayList<>();
            fetchColumns.add(gen.generateAggregate());
            if (Randomly.getBoolean()) {
                fetchColumns.add(gen.generateExpression(0));
            }
            select.setFetchColumns(fetchColumns);

            // WHERE — 50% chance to use index-friendly condition for better index testing
            if (Randomly.getBoolean()) {
                MySQLExpression indexWhere = tryGenerateIndexFriendlyWhere(targetTables.getTables(), gen);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                } else {
                    select.setWhereClause(gen.generateExpression(0));
                }
            }

            // GROUP BY
            if (Randomly.getBoolean()) {
                List<MySQLExpression> groupByExprs = new ArrayList<>();
                for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
                    groupByExprs.add(gen.generateExpression(0));
                }
                select.setGroupByExpressions(groupByExprs);
            }

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    private MySQLSelect generateJoinSelect() {
        MySQLSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().size() < 2) return null;

        try {
            MySQLTables targetTables = schema.getRandomTableNonEmptyTables();
            List<MySQLColumn> columns = targetTables.getColumns();
            List<MySQLTable> tables = targetTables.getTables();

            MySQLExpressionGenerator gen = new MySQLExpressionGenerator(globalState).setColumns(columns);

            MySQLSelect select = new MySQLSelect();

            // JOIN conditions — 50% chance to use index-friendly JOINs
            List<MySQLJoin> joinClauses;
            if (Randomly.getBoolean()) {
                // Exclude the driving table from join candidates to prevent
                // "Not unique table/alias" when the same table appears in both
                // FROM and JOIN clauses
                List<MySQLTable> joinCandidates = new ArrayList<>(tables.subList(1, tables.size()));
                if (!joinCandidates.isEmpty()) {
                    joinClauses = MySQLJoin.getRandomJoinClauses(joinCandidates, globalState);
                } else {
                    joinClauses = new ArrayList<>();
                }
            } else {
                joinClauses = generateIndexFriendlyJoinClauses(tables);
            }

            // FROM list: only include the first (driving) table when JOINs are present,
            // otherwise include all tables to avoid duplicate table alias errors.
            // When a JOIN table has the same name as the driving table, assign aliases
            // (e.g., FROM t0 AS t0 ... INNER JOIN t0 AS t_0 ON ...) to avoid
            // "Not unique table/alias" error.
            if (!joinClauses.isEmpty()) {
                String drivingName = tables.get(0).getName();
                boolean hasDuplicateName = false;
                int aliasCounter = 0;

                // Assign aliases to JOIN tables that duplicate the driving table name
                for (MySQLJoin jc : joinClauses) {
                    if (jc.getTable().getName().equals(drivingName)) {
                        hasDuplicateName = true;
                        jc.setAlias("t_" + aliasCounter++);
                    }
                }

                // If duplicates were found, also alias the driving table
                MySQLTableReference drivingRef;
                if (hasDuplicateName) {
                    drivingRef = new MySQLTableReference(tables.get(0), "t0");
                } else {
                    drivingRef = new MySQLTableReference(tables.get(0));
                }
                select.setFromList(Collections.singletonList(drivingRef));
            } else {
                select.setFromList(tables.stream()
                        .map(t -> (MySQLExpression) new MySQLTableReference(t))
                        .collect(Collectors.toList()));
            }
            select.setJoinClauses(joinClauses);

            // Fetch columns
            List<MySQLExpression> fetchColumns = new ArrayList<>();
            for (int i = 0; i < Math.min(columns.size(), Randomly.smallNumber() + 1); i++) {
                fetchColumns.add(gen.generateExpression(0));
            }
            select.setFetchColumns(fetchColumns);

            // WHERE — 50% chance to use index-friendly condition
            if (Randomly.getBoolean()) {
                MySQLExpression indexWhere = tryGenerateIndexFriendlyWhere(tables, gen);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                } else {
                    select.setWhereClause(gen.generateExpression(0));
                }
            }

            // LIMIT
            if (Randomly.getBoolean()) {
                select.setLimitClause(MySQLConstant.createIntConstant(
                        Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));
            }

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    // ==================== Index-Aware Query Generation ====================

    // Targets index columns in WHERE so the optimizer considers the index, making FORCE/IGNORE INDEX meaningful.
    private String generateIndexAwareQueryString(MySQLTable table, MySQLIndex index) {
        try {
            List<String> idxColNames = index.getColumnNames();
            if (idxColNames == null || idxColNames.isEmpty()) return generateASTQuery();

            // Resolve index column names to MySQLColumn objects
            List<MySQLColumn> idxCols = new ArrayList<>();
            for (String colName : idxColNames) {
                for (MySQLColumn col : table.getColumns()) {
                    if (col.getName().equals(colName)) {
                        idxCols.add(col);
                        break;
                    }
                }
            }
            if (idxCols.isEmpty()) return generateASTQuery();

            Randomly r = globalState.getRandomly();
            StringBuilder sb = new StringBuilder();

            // SELECT clause: mix of index columns and expressions
            sb.append("SELECT ");
            if (Randomly.getBoolean()) {
                // SELECT * for full row comparison
                sb.append("*");
            } else {
                // SELECT index columns + optional aggregate
                List<String> selectCols = new ArrayList<>();
                for (MySQLColumn col : idxCols) {
                    selectCols.add(col.getName());
                }
                // Add a non-index column occasionally for covering index test
                for (MySQLColumn col : table.getColumns()) {
                    if (!idxCols.contains(col) && Randomly.getBooleanWithRatherLowProbability()) {
                        selectCols.add(col.getName());
                        break;
                    }
                }
                sb.append(String.join(", ", selectCols));
            }

            // FROM clause
            sb.append(" FROM ").append(table.getName());

            // WHERE clause: use index columns for range/point lookups
            sb.append(" WHERE ");
            String whereClause = generateIndexColumnConditions(idxCols, table, r);
            sb.append(whereClause);

            // ORDER BY: use index columns (tests index-sorted ORDER BY vs filesort)
            if (Randomly.getBoolean()) {
                MySQLColumn orderCol = Randomly.fromList(idxCols);
                sb.append(" ORDER BY ").append(orderCol.getName());
                sb.append(Randomly.fromOptions(" ASC", " DESC"));
            }

            // LIMIT: increases chance of different plans (index scan vs table scan)
            if (Randomly.getBoolean()) {
                sb.append(" LIMIT ").append(r.getInteger(1, 100));
            }

            sb.append(";");
            return sb.toString();
        } catch (Exception e) {
            return generateASTQuery();
        }
    }

    private String generateIndexColumnConditions(List<MySQLColumn> idxCols, MySQLTable table, Randomly r) {
        String tableName = table.getName();
        List<String> conditions = new ArrayList<>();
        int numConditions = r.getInteger(1, Math.min(idxCols.size() + 1, 4));

        for (int i = 0; i < numConditions && i < idxCols.size(); i++) {
            MySQLColumn col = idxCols.get(i);
            String colName = col.getName();
            String condition;
            Reduced IS NULL weight: now 0-18 range (19 options), IS NULL only at case 18 (~5%)
            int opType = r.getInteger(0, 19); // 0-18: 19 options
            switch (opType) {
            case 0: // col = value (point lookup — best for ref access) — use sampled data
                condition = colName + " = " + generateDataAwareValueForType(tableName, col);
                break;
            case 1: // col > value (range scan) — use sampled data
                condition = colName + " > " + generateDataAwareValueForType(tableName, col);
                break;
            case 2: { // col BETWEEN a AND b (range scan) —guaranteed ordered
                String[] rangeVals = generateOrderedRangeValues(tableName, col);
                if (rangeVals != null) {
                    condition = colName + " BETWEEN " + rangeVals[0] + " AND " + rangeVals[1];
                } else {
                    condition = colName + " IS NOT NULL"; // fallback
                }
                break;
            }
            case 3: // col IN (...) (range scan with multiple values) — use sampled data
                StringBuilder inList = new StringBuilder();
                for (int j = 0; j < r.getInteger(2, 6); j++) {
                    if (j > 0) inList.append(", ");
                    inList.append(generateDataAwareValueForType(tableName, col));
                }
                condition = colName + " IN (" + inList + ")";
                break;
            case 18: IS NULL / IS NOT NULL — reduced weight (~5%)
                condition = Randomly.getBoolean() ? colName + " IS NULL" : colName + " IS NOT NULL";
                break;
            case 5: { // col >= val AND col <= val (closed range) —guaranteed ordered
                String[] rangeVals = generateOrderedRangeValues(tableName, col);
                if (rangeVals != null) {
                    condition = colName + " >= " + rangeVals[0] + " AND " + colName + " <= " + rangeVals[1];
                } else {
                    condition = colName + " IS NOT NULL"; // fallback
                }
                break;
            }
            case 6: // LIKE with sampled prefix for VARCHAR columns (targets prefix indexes)
                if (col.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
                    String likePattern = generateSampledLikePrefix(tableName, colName, Randomly.fromOptions(1, 2, 3, 5));
                    condition = colName + " LIKE " + likePattern;
                } else {
                    condition = colName + " != " + generateDataAwareValueForType(tableName, col);
                }
                break;
            case 7: // LEFT(col, N) = 'prefix' — targets prefix indexes specifically
                if (col.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
                    int prefixLen = Randomly.fromOptions(1, 2, 3, 5);
                    String likePattern = generateSampledLikePrefix(tableName, colName, prefixLen);
                    // Strip the trailing % and surrounding quotes from LIKE pattern
                    String prefixStr = likePattern;
                    if (prefixStr.endsWith("%'")) {
                        prefixStr = prefixStr.substring(0, prefixStr.length() - 2) + "'";
                    }
                    condition = "LEFT(" + colName + ", " + prefixLen + ") = " + prefixStr;
                } else {
                    condition = colName + " < " + generateDataAwareValueForType(tableName, col);
                }
                break;
            default: // col < value — use sampled data
                condition = colName + " < " + generateDataAwareValueForType(tableName, col);
                break;
            }
            conditions.add(condition);
        }

        // Also add conditions on non-index columns occasionally (tests index merge + filter)
        if (Randomly.getBooleanWithRatherLowProbability()) {
            for (MySQLColumn col : table.getColumns()) {
                if (!idxCols.contains(col) && Randomly.getBooleanWithRatherLowProbability()) {
                    conditions.add(col.getName() + " = " + generateDataAwareValueForType(tableName, col));
                    break;
                }
            }
        }

        // Combine with AND
        return String.join(" AND ", conditions);
    }

    // ==================== P0-A: Index-Aware Aggregate Query ====================

    private String generateIndexAwareAggregateQuery() {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return null;

        MySQLTable table = Randomly.fromList(tables);
        List<MySQLIndex> indexes = table.getIndexes();
        if (indexes.isEmpty()) {
            try {
                MySQLIndexGenerator.create(globalState);
                analyzeTable(table.getName());
                indexes = table.getIndexes();
            } catch (Exception e) { }
        }
        if (indexes.isEmpty()) return null;

        MySQLIndex idx = Randomly.fromList(indexes);
        List<String> idxColNames = idx.getColumnNames();
        if (idxColNames == null || idxColNames.isEmpty()) return null;

        // Resolve index columns
        List<MySQLColumn> idxCols = new ArrayList<>();
        for (String colName : idxColNames) {
            for (MySQLColumn col : table.getColumns()) {
                if (col.getName().equals(colName)) {
                    idxCols.add(col);
                    break;
                }
            }
        }
        if (idxCols.isEmpty()) return null;

        String tblName = table.getName();
        MySQLColumn groupByCol = idxCols.get(0); // Use first index column for GROUP BY
        MySQLColumn aggCol = idxCols.size() > 1 ? idxCols.get(1) : idxCols.get(0);
        Avoid SUM/AVG on FLOAT/DOUBLE columns — different execution plans
        // may accumulate floating-point values in different order, producing micro-precision
        // differences that are NOT real bugs but cause false positives.
        // For FLOAT/DOUBLE columns, only use COUNT/MIN/MAX (exact for any scan order).
        String aggFunc;
        boolean isFloatCol = (aggCol.getType() == MySQLSchema.MySQLDataType.FLOAT
                || aggCol.getType() == MySQLSchema.MySQLDataType.DOUBLE);
        if (isFloatCol) {
            aggFunc = Randomly.fromOptions("COUNT", "MIN", "MAX");
        } else {
            aggFunc = Randomly.fromOptions("COUNT", "SUM", "MIN", "MAX", "AVG");
        }

        String val = generateDataAwareValueForType(tblName, groupByCol);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String whereCond = groupByCol.getName() + " " + op + " " + val;

        // Aggregate query with GROUP BY on index column
        String queryString = "SELECT " + groupByCol.getName() + ", " + aggFunc + "(" + aggCol.getName() + ") FROM "
                + tblName + " WHERE " + whereCond + " GROUP BY " + groupByCol.getName();
        if (Randomly.getBoolean()) {
            queryString += " ORDER BY " + groupByCol.getName();
        }
        queryString += ";";
        return queryString;
    }

    // ==================== Query String Generators ====================

    private String generateASTQuery() {
        // Mix of AST-generated and random queries
        if (Randomly.getBooleanWithRatherLowProbability()) {
            return generateFallbackQuery();
        }
        try {
            MySQLSelect select = generateComplexSelect();
            if (select == null) return generateFallbackQuery();
            return MySQLVisitor.asString(select) + ";";
        } catch (Exception e) {
            return generateFallbackQuery();
        }
    }

    private String generateASTJoinQuery() {
        try {
            MySQLSelect select = generateJoinSelect();
            if (select == null) return null;
            return MySQLVisitor.asString(select) + ";";
        } catch (Exception e) {
            return null;
        }
    }

    private String generateASTAggregateQuery() {
        try {
            MySQLSelect select = generateAggregateSelect();
            if (select == null) return null;
            return MySQLVisitor.asString(select) + ";";
        } catch (Exception e) {
            return null;
        }
    }

    private String generateASTOrderedQuery() {
        MySQLSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return null;

        try {
            MySQLTables targetTables = schema.getRandomTableNonEmptyTables();
            List<MySQLColumn> columns = targetTables.getColumns();

            MySQLExpressionGenerator gen = new MySQLExpressionGenerator(globalState).setColumns(columns);

            MySQLSelect select = new MySQLSelect();
            select.setFromList(targetTables.getTables().stream()
                    .map(t -> (MySQLExpression) new MySQLTableReference(t))
                    .collect(Collectors.toList()));

            // Fetch columns
            List<MySQLExpression> fetchColumns = new ArrayList<>();
            List<MySQLColumn> subset = Randomly.nonEmptySubset(columns);
            for (int i = 0; i < subset.size(); i++) {
                fetchColumns.add(gen.generateExpression(0));
            }
            select.setFetchColumns(fetchColumns);

            // WHERE — 50% chance to use index-friendly condition for ORDER BY index testing
            if (Randomly.getBoolean()) {
                MySQLExpression indexWhere = tryGenerateIndexFriendlyWhere(targetTables.getTables(), gen);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                } else {
                    select.setWhereClause(gen.generateExpression(0));
                }
            }

            // ORDER BY — always present for this mode
            select.setOrderByClauses(gen.generateOrderBys());

            // LIMIT
            select.setLimitClause(MySQLConstant.createIntConstant(
                    Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1));

            return MySQLVisitor.asString(select) + ";";
        } catch (Exception e) {
            return null;
        }
    }

    private String generateFallbackQuery() {
        try {
            MySQLSelect select = MySQLRandomQuerySynthesizer.generate(globalState,
                    Randomly.smallNumber() + 1);
            if (select == null) return "SELECT 1;";
            select.setSelectType(SelectType.ALL);
            return MySQLVisitor.asString(select) + ";";
        } catch (Exception e) {
            return "SELECT 1;";
        }
    }

    // ==================== Index-Friendly JOIN Generation ====================

    // Uses simple column comparisons (not complex expressions) so the optimizer can use indexes on JOIN cols.
    private List<MySQLJoin> generateIndexFriendlyJoinClauses(List<MySQLTable> tables) {
        List<MySQLJoin> joinStatements = new ArrayList<>();
        if (tables.size() < 2) return joinStatements;

        try {
            List<JoinType> options = new ArrayList<>(Arrays.asList(JoinType.INNER, JoinType.LEFT, JoinType.RIGHT));
            int nrJoinClauses = (int) Math.min(tables.size() - 1, Randomly.getNotCachedInteger(1, Math.min(tables.size(), 3)));

            List<MySQLTable> remaining = new ArrayList<>(tables);
            MySQLTable firstTable = remaining.remove(0);

            for (int i = 0; i < nrJoinClauses && !remaining.isEmpty(); i++) {
                MySQLTable joinTable = Randomly.fromList(remaining);
                remaining.remove(joinTable);

                // Find columns with matching types between tables for join conditions
                MySQLExpression onClause = generateIndexJoinCondition(firstTable, joinTable);
                JoinType joinType = Randomly.fromList(options);

                joinStatements.add(new MySQLJoin(joinTable, onClause, joinType));
            }
        } catch (Exception e) {
            // fallback: return empty
        }
        return joinStatements;
    }

    private MySQLExpression generateIndexJoinCondition(MySQLTable t1, MySQLTable t2) {
        List<MySQLColumn> cols1 = t1.getColumns();
        List<MySQLColumn> cols2 = t2.getColumns();
        if (cols1.isEmpty() || cols2.isEmpty()) return MySQLConstant.createTrue();

        Randomly r = globalState.getRandomly();
        int numConditions = r.getInteger(1, 3); // 1-2 join conditions
        MySQLExpression combined = null;

        for (int i = 0; i < numConditions; i++) {
            MySQLColumn c1 = Randomly.fromList(cols1);
            MySQLColumn c2 = Randomly.fromList(cols2);

            MySQLExpression ref1 = MySQLColumnReference.create(c1, null);
            MySQLExpression ref2 = MySQLColumnReference.create(c2, null);

            MySQLExpression condition;
            int opType = r.getInteger(0, 4);
            switch (opType) {
            case 0: // t1.c0 = t2.c0 (equijoin - best for index use)
                condition = new MySQLBinaryComparisonOperation(ref1, ref2, BinaryComparisonOperator.EQUALS);
                break;
            case 1: // t1.c0 > t2.c0
                condition = new MySQLBinaryComparisonOperation(ref1, ref2, BinaryComparisonOperator.GREATER);
                break;
            case 2: // t1.c0 < t2.c0
                condition = new MySQLBinaryComparisonOperation(ref1, ref2, BinaryComparisonOperator.LESS);
                break;
            default: // t1.c0 >= t2.c0
                condition = new MySQLBinaryComparisonOperation(ref1, ref2, BinaryComparisonOperator.GREATER_EQUALS);
                break;
            }

            if (combined == null) {
                combined = condition;
            } else {
                combined = new MySQLBinaryLogicalOperation(combined, condition, MySQLBinaryLogicalOperator.AND);
            }
        }
        return combined != null ? combined : MySQLConstant.createTrue();
    }

    // ==================== A. Ensure Sufficient Data ====================

    private void ensureSufficientData() {
        if (dataPopulated) return;
        dataPopulated = true;

        //Create index-friendly tables FIRST, before populating data.
        // These tables have diverse column types (INT, VARCHAR, DECIMAL, DOUBLE, FLOAT)
        // and pre-built indexes (prefix, DESC, composite, FULLTEXT, INVISIBLE).
        // Without this, MySQL only has 1 table with 1-2 columns → most test modes skip.
        createIndexFriendlyTables();

        // Build expected errors for INSERT statements — these are common
        // constraint violations that can occur when inserting random data.
        // Without ExpectedErrors, SQLQueryAdapter.checkException() throws
        // AssertionError (which extends Error, not Exception), so
        // catch(Exception) cannot catch it.
        ExpectedErrors insertErrors = new ExpectedErrors();
        insertErrors.add("cannot be null");
        insertErrors.add("Duplicate entry");
        insertErrors.add("Data truncated");
        insertErrors.add("Data too long");
        insertErrors.add("Out of range");
        insertErrors.add("Incorrect");
        insertErrors.add("Check constraint");
        insertErrors.add("cannot insert into view");
        insertErrors.add("non-updateable view");
        insertErrors.add("division by zero");
        insertErrors.add("syntax error");
        insertErrors.add("doesn't exist");
        insertErrors.add("Unknown column");
        insertErrors.add("permission denied");
        insertErrors.add("out of memory");
        insertErrors.add("canceling statement");
        insertErrors.add("deadlock");

        try {
            MySQLSchema schema = globalState.getSchema();
            for (MySQLTable table : schema.getDatabaseTables()) {
                if (table.getColumns().isEmpty()) continue;
                // Skip views — cannot INSERT into views
                if (table.isView()) continue;
                Filter out generated columns (named gen_col_*) from INSERT target.
                // Generated columns are auto-computed by MySQL and cannot receive explicit values.
                List<MySQLColumn> insertableCols = table.getColumns().stream()
                        .filter(c -> !c.getName().startsWith("gen_col_"))
                        .collect(Collectors.toList());
                if (insertableCols.isEmpty()) continue;
                try {
                    for (int batch = 0; batch < 3; batch++) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("INSERT IGNORE INTO ").append(table.getName()).append("(");
                        sb.append(insertableCols.stream()
                                .map(c -> c.getName())
                                .collect(Collectors.joining(", ")));
                        sb.append(") VALUES ");
                        for (int row = 0; row < 50; row++) {
                            if (row > 0) sb.append(", ");
                            sb.append("(");
                            for (int col = 0; col < insertableCols.size(); col++) {
                                if (col > 0) sb.append(", ");
                                MySQLColumn c = insertableCols.get(col);
                                sb.append(generateRandomValueForType(c.getType()));
                            }
                            sb.append(")");
                        }
                        sb.append(";");
                        // Log the INSERT statement so that bugs found by the oracle
                        // can be reproduced from the log file alone. Without this,
                        // ensureSufficientData() generates random data that is not
                        // captured in the log, making it impossible to reproduce
                        // prefix index bugs involving multi-byte characters.
                        log(sb.toString());
                        globalState.executeStatement(new SQLQueryAdapter(sb.toString(), insertErrors, true));
                    }
                } catch (Exception e) { }
                try {
                    String analyzeStmt = "ANALYZE TABLE " + table.getName() + ";";
                    log(analyzeStmt);
                    globalState.executeStatement(new SQLQueryAdapter(analyzeStmt, true));
                } catch (Exception e) { }
            }
        } catch (Exception e) { }
    }

    private String generateRandomValueForType(MySQLSchema.MySQLDataType type) {
        Randomly r = globalState.getRandomly();
        switch (type) {
        case INT:
            //Use smaller range to avoid boundary values like 2147483647
            // that make `col < 2147483647` match ALL rows (no selectivity).
            // Math.abs(r.getInteger()) often hits INT_MAX which is useless for testing.
            return String.valueOf(Math.abs(r.getInteger()) % 100000);
        case VARCHAR:
            return "'" + generateRandomString(r).replace("'", "''").replace("\\", "\\\\") + "'";
        case FLOAT:
        case DOUBLE:
        case DECIMAL:
            // Use getFiniteDouble() to avoid Infinity/NaN, Math.abs for ZEROFILL safety
            return String.valueOf(Math.abs(r.getFiniteDouble()));
        default:
            return "NULL";
        }
    }

    // Fallback chain: sampled actual data (70%) → MIN/MAX → type-appropriate random.
    private String generateDataAwareValueForType(String tableName, MySQLColumn col) {
        // Priority 1: Try to use a sampled value from actual table data (70% chance)
        if (Randomly.getBooleanWithRatherLowProbability() || !Randomly.getBoolean()) {
            List<String> sampled = sampleColumnValues(tableName, col.getName(), 5);
            if (sampled != null && !sampled.isEmpty()) {
                String val = Randomly.fromList(sampled);
                Wrap VARCHAR values in quotes — sampled values are raw strings from DB
                if (col.getType() == MySQLSchema.MySQLDataType.VARCHAR && val != null && !val.equals("NULL")) {
                    val = "'" + sanitizeForSqlString(val) + "'";
                }
                return val;
            }
        }

        // Priority 2: Use MIN or MAX value from the column
        String minMax = tryGetMinMaxValue(tableName, col);
        if (minMax != null) {
            return minMax;
        }

        // Priority 3: Random value (last resort — least likely to hit index)
        return generateRandomValueForType(col.getType());
    }

    private String tryGetMinMaxValue(String tableName, MySQLColumn col) {
        try {
            String func = Randomly.getBoolean() ? "MIN" : "MAX";
            String query = "SELECT " + func + "(" + col.getName() + ") FROM " + tableName + ";";
            List<String> result = executeQuery(query);
            if (result != null && !result.isEmpty() && result.get(0) != null) {
                String val = result.get(0);
                // Wrap VARCHAR values in quotes if not already
                if (col.getType() == MySQLSchema.MySQLDataType.VARCHAR && !val.startsWith("'")) {
                    val = "'" + sanitizeForSqlString(val) + "'";
                }
                return val;
            }
        } catch (Exception e) { }
        return null;
    }

    // Returns {low, high} guaranteed low <= high using actual MIN/MAX; numeric interpolation for tighter range.
    private String[] generateOrderedRangeValues(String tableName, MySQLColumn col) {
        String[] minMax = getColumnMinMax(tableName, col.getName());
        if (minMax != null) {
            // minMax[0] = MIN, minMax[1] = MAX — already guaranteed ordered
            // 70% chance: use MIN/MAX directly for guaranteed hit
            // 30% chance: interpolate between them for narrower range
            if (Randomly.getBooleanWithRatherLowProbability()) {
                try {
                    // Try numeric interpolation for tighter range
                    double min = Double.parseDouble(minMax[0].replace("'", ""));
                    double max = Double.parseDouble(minMax[1].replace("'", ""));
                    if (min == max) {
                        return minMax; // single value range
                    }
                    // Pick two random points in [min, max]
                    double point1 = min + (max - min) * globalState.getRandomly().getDouble();
                    double point2 = min + (max - min) * globalState.getRandomly().getDouble();
                    double low = Math.min(point1, point2);
                    double high = Math.max(point1, point2);
                    if (col.getType() == MySQLSchema.MySQLDataType.INT) {
                        return new String[]{ String.valueOf((long) low), String.valueOf((long) high) };
                    } else {
                        return new String[]{ String.valueOf(low), String.valueOf(high) };
                    }
                } catch (NumberFormatException e) {
                    // VARCHAR or non-numeric — fall through to MIN/MAX
                }
            }
            return minMax;
        }

        // Fallback: generate two data-aware values and sort them numerically if possible
        String val1 = generateDataAwareValueForType(tableName, col);
        String val2 = generateDataAwareValueForType(tableName, col);
        try {
            double d1 = Double.parseDouble(val1.replace("'", ""));
            double d2 = Double.parseDouble(val2.replace("'", ""));
            if (d1 <= d2) {
                return new String[]{ val1, val2 };
            } else {
                return new String[]{ val2, val1 };
            }
        } catch (NumberFormatException e) {
            // VARCHAR — can't reliably sort, use MIN/MAX or skip BETWEEN
            return null;
        }
    }

    // Guarantees min <= max so BETWEEN min AND max is always valid; null if table is empty or on error.
    private String[] getColumnMinMax(String tableName, String colName) {
        try {
            List<String> minResult = executeQuery("SELECT MIN(" + colName + ") FROM " + tableName + ";");
            List<String> maxResult = executeQuery("SELECT MAX(" + colName + ") FROM " + tableName + ";");
            if (minResult != null && !minResult.isEmpty() && minResult.get(0) != null
                    && maxResult != null && !maxResult.isEmpty() && maxResult.get(0) != null) {
                return new String[]{ minResult.get(0), maxResult.get(0) };
            }
        } catch (Exception e) { }
        return null;
    }

    // Creates 2-3 tables (idx_t0/t1/t2) with diverse column types and pre-built indexes.
    // Without these, MySQL's default 1 table with 1-2 cols causes ~80% of test modes to be skipped.
    private void createIndexFriendlyTables() {
        ExpectedErrors tableErrors = new ExpectedErrors();
        tableErrors.add("already exists");
        tableErrors.add("Duplicate key name");
        tableErrors.add("Specified key was too long");
        tableErrors.add("BLOB or TEXT");
        tableErrors.add("used in key specification");
        tableErrors.add("Too many keys specified");

        // Check if index-friendly tables already exist
        try {
            MySQLSchema schema = globalState.getSchema();
            boolean hasIdxTable = false;
            for (MySQLTable t : schema.getDatabaseTables()) {
                if (t.getName().startsWith("idx_")) {
                    hasIdxTable = true;
                    break;
                }
            }
            if (hasIdxTable) return; // Already created in a previous iteration
        } catch (Exception e) { return; }

        // Create 2-3 index-friendly tables with diverse column types
        int numTables = Randomly.fromOptions(2, 2, 3);
        for (int t = 0; t < numTables; t++) {
            String tableName = "idx_t" + t;
            try {
                StringBuilder createSQL = new StringBuilder();
                createSQL.append("CREATE TABLE IF NOT EXISTS ").append(tableName).append(" (");

                if (t == 0) {
                    // Table 0: INT + VARCHAR — general index testing + prefix index + fulltext
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 INT NOT NULL, ");
                    createSQL.append("c2 INT, "); // nullable for NULL boundary testing
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 INT NOT NULL, ");
                    createSQL.append("c5 VARCHAR(255) NOT NULL, "); // VARCHAR(255) for prefix index testing
                    createSQL.append("c6 VARCHAR(255), "); // nullable VARCHAR
                    createSQL.append("c7 VARCHAR(255) NOT NULL");
                    createSQL.append(");");
                } else if (t == 1) {
                    // Table 1: INT + DECIMAL + DOUBLE — precision index testing
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 DECIMAL(10,2) NOT NULL, ");
                    createSQL.append("c2 DOUBLE NOT NULL, ");
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 DECIMAL(10,4), "); // nullable DECIMAL
                    createSQL.append("c5 VARCHAR(255) NOT NULL, ");
                    createSQL.append("c6 DOUBLE, "); // nullable DOUBLE
                    createSQL.append("c7 INT NOT NULL");
                    createSQL.append(");");
                } else {
                    // Table 2: INT + VARCHAR + FLOAT — FLOAT index approximation
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 FLOAT NOT NULL, ");
                    createSQL.append("c2 VARCHAR(255), "); // nullable VARCHAR
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 FLOAT, "); // nullable FLOAT
                    createSQL.append("c5 VARCHAR(255) NOT NULL, ");
                    createSQL.append("c6 INT, "); // nullable INT
                    createSQL.append("c7 FLOAT NOT NULL");
                    createSQL.append(");");
                }
                globalState.executeStatement(new SQLQueryAdapter(createSQL.toString(), tableErrors, true));

                // Pre-build diverse indexes — MySQL-specific features
                List<String> indexStmtsList = new ArrayList<>();
                if (t == 0) {
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0c1c3 ON " + tableName + " (c0, c1, c3);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c5 ON " + tableName + " (c5);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c5pre ON " + tableName + " (c5(10));"); // prefix index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0desc ON " + tableName + " (c0 DESC);"); // DESC index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c2 ON " + tableName + " (c2);"); // nullable index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0asc1desc ON " + tableName + " (c0 ASC, c1 DESC);"); // mixed sort
                    // INVISIBLE index (MySQL 8.0+ compatible feature)
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(
                                "CREATE INDEX idx_" + t + "_c3inv ON " + tableName + " (c3) INVISIBLE;", tableErrors, true));
                    } catch (Exception e) { }
                    // Note: FULLTEXT index skipped — PolarDB-X does not support FULLTEXT
                } else if (t == 1) {
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c1 ON " + tableName + " (c1);"); // DECIMAL index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c2 ON " + tableName + " (c2);"); // DOUBLE index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);"); // INT + DECIMAL composite
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0c2 ON " + tableName + " (c0, c2);"); // INT + DOUBLE composite
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c2desc ON " + tableName + " (c2 DESC);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c4 ON " + tableName + " (c4);"); // nullable DECIMAL
                } else {
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c1 ON " + tableName + " (c1);"); // FLOAT index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);"); // INT + FLOAT composite
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c5 ON " + tableName + " (c5);"); // VARCHAR index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c5pre ON " + tableName + " (c5(10));"); // prefix index
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c1desc ON " + tableName + " (c1 DESC);");
                    indexStmtsList.add("CREATE INDEX idx_" + t + "_c7 ON " + tableName + " (c7);"); // FLOAT index
                }

                for (String idxSQL : indexStmtsList) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(idxSQL, tableErrors, true));
                    } catch (Exception e) { }
                }

                // Insert initial data (200 rows) using type-aware generation
                ExpectedErrors insertErrors = new ExpectedErrors();
                insertErrors.add("cannot be null");
                insertErrors.add("Duplicate entry");
                insertErrors.add("Data truncated");
                insertErrors.add("Data too long");
                insertErrors.add("Out of range");
                insertErrors.add("Incorrect");
                Randomly r = globalState.getRandomly();

                for (int batch = 0; batch < 4; batch++) {
                    StringBuilder insertSQL = new StringBuilder();
                    insertSQL.append("INSERT IGNORE INTO ").append(tableName).append(" VALUES ");
                    for (int row = 0; row < 50; row++) {
                        if (row > 0) insertSQL.append(", ");
                        insertSQL.append("(");
                        // Generate values based on table type
                        if (t == 0) {
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c0 INT
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c1 INT
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : Math.abs(r.getInteger())).append(", "); // c2 INT nullable
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c3 INT
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c4 INT
                            insertSQL.append("'").append(generateRandomString(r).replace("'", "''").replace("\\", "\\\\")).append("', "); // c5 VARCHAR
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : "'" + generateRandomString(r).replace("'", "''").replace("\\", "\\\\") + "'").append(", "); // c6 VARCHAR nullable
                            insertSQL.append("'").append(generateRandomString(r).replace("'", "''").replace("\\", "\\\\")).append("'"); // c7 VARCHAR
                        } else if (t == 1) {
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c0 INT
                            insertSQL.append(String.format("%.2f", Math.abs(r.getFiniteDouble()))).append(", "); // c1 DECIMAL
                            insertSQL.append(Math.abs(r.getFiniteDouble())).append(", "); // c2 DOUBLE
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c3 INT
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : String.format("%.4f", Math.abs(r.getFiniteDouble()))).append(", "); // c4 DECIMAL nullable
                            insertSQL.append("'").append(generateRandomString(r).replace("'", "''").replace("\\", "\\\\")).append("', "); // c5 VARCHAR
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : Math.abs(r.getFiniteDouble())).append(", "); // c6 DOUBLE nullable
                            insertSQL.append(Math.abs(r.getInteger())); // c7 INT
                        } else {
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c0 INT
                            insertSQL.append(Math.abs(r.getFiniteDouble())).append(", "); // c1 FLOAT
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : "'" + generateRandomString(r).replace("'", "''").replace("\\", "\\\\") + "'").append(", "); // c2 VARCHAR nullable
                            insertSQL.append(Math.abs(r.getInteger())).append(", "); // c3 INT
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : Math.abs(r.getFiniteDouble())).append(", "); // c4 FLOAT nullable
                            insertSQL.append("'").append(generateRandomString(r).replace("'", "''").replace("\\", "\\\\")).append("', "); // c5 VARCHAR
                            insertSQL.append(Randomly.getBoolean() ? "NULL" : Math.abs(r.getInteger())).append(", "); // c6 INT nullable
                            insertSQL.append(Math.abs(r.getFiniteDouble())); // c7 FLOAT
                        }
                        insertSQL.append(")");
                    }
                    insertSQL.append(";");
                    log(insertSQL.toString());
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(insertSQL.toString(), insertErrors, true));
                    } catch (Exception e) { }
                }

                // ANALYZE TABLE for optimizer statistics
                try {
                    String analyzeStmt = "ANALYZE TABLE " + tableName + ";";
                    log(analyzeStmt);
                    globalState.executeStatement(new SQLQueryAdapter(analyzeStmt, true));
                } catch (Exception e) { }

            } catch (Exception e) { }
        }

        // Refresh schema to include the new tables
        try {
            globalState.updateSchema();
        } catch (Exception e) { }
    }

    // Uses sampled actual VARCHAR data to build a LIKE 'prefix%' pattern targeting prefix indexes.
    private String generateSampledLikePrefix(String tableName, String colName, int maxPrefixLen) {
        List<String> sampled = sampleColumnValues(tableName, colName, 5);
        if (sampled != null && !sampled.isEmpty()) {
            // Pick a random sampled value and extract its prefix
            String rawVal = Randomly.fromList(sampled);
            // Strip surrounding quotes if present (from executeQuery output)
            if (rawVal.length() >= 2 && rawVal.startsWith("'") && rawVal.endsWith("'")) {
                rawVal = rawVal.substring(1, rawVal.length() - 1);
            }
            if (!rawVal.isEmpty()) {
                int prefixLen = Math.min(rawVal.length(), maxPrefixLen);
                String prefix = rawVal.substring(0, prefixLen).replace("'", "''").replace("\\", "\\\\");
                return "'" + prefix + "%'";
            }
        }
        // Fallback: generate a random LIKE prefix
        Randomly r = globalState.getRandomly();
        String fallbackStr = r.getString();
        String likePrefix = fallbackStr.isEmpty() ? ""
                : fallbackStr.substring(0, Math.min(maxPrefixLen, fallbackStr.length()));
        return "'" + likePrefix.replace("'", "''").replace("\\", "\\\\") + "%'";
    }

    // ==================== B. Index-Aware WHERE Generation ====================

    // Analyzes actual table indexes to generate WHERE conditions targeting specific optimizer paths:
    // composite prefix/range scan, OR index merge, composite AND, IS NULL/IS NOT NULL, type-aware IN/LIKE.
    private MySQLExpression tryGenerateIndexFriendlyWhere(List<MySQLTable> tables, MySQLExpressionGenerator gen) {
        try {
            // Step 1: Collect index information — map columns to their indexes
            List<MySQLColumn> indexedCols = new ArrayList<>();  // all indexed columns
            List<List<MySQLColumn>> compositeIdxCols = new ArrayList<>();  // composite index column groups
            List<MySQLColumn> singleIdxCols = new ArrayList<>();  // columns with single-column indexes

            for (MySQLTable table : tables) {
                for (MySQLIndex idx : table.getIndexes()) {
                    List<String> idxColNames = idx.getColumnNames();
                    if (idxColNames == null || idxColNames.isEmpty()) continue;

                    // Resolve column names to MySQLColumn objects
                    List<MySQLColumn> idxColumns = new ArrayList<>();
                    for (String colName : idxColNames) {
                        for (MySQLColumn col : table.getColumns()) {
                            if (col.getName().equals(colName)) {
                                idxColumns.add(col);
                                if (!indexedCols.contains(col)) {
                                    indexedCols.add(col);
                                }
                                break;
                            }
                        }
                    }
                    if (idxColumns.size() >= 2) {
                        compositeIdxCols.add(idxColumns);
                    }
                    if (idxColumns.size() == 1) {
                        singleIdxCols.add(idxColumns.get(0));
                    }
                }
            }

            Randomly r = globalState.getRandomly();

            // Step 2: Choose a smart generation strategy based on available indexes
            int strategy;
            if (!compositeIdxCols.isEmpty() && singleIdxCols.size() >= 2 && Randomly.getBoolean()) {
                // All strategies available — pick randomly
                strategy = r.getInteger(0, 6);
            } else if (!compositeIdxCols.isEmpty()) {
                strategy = r.getInteger(0, 4); // strategies 0-3 (composite-focused)
            } else if (singleIdxCols.size() >= 2) {
                strategy = Randomly.fromOptions(0, 1, 4); // simple + index merge
            } else if (!indexedCols.isEmpty()) {
                strategy = r.getInteger(0, 2); // basic strategies only
            } else {
                // No indexes at all — fall back to all-columns approach
                return tryGenerateBasicWhere(tables, gen);
            }

            switch (strategy) {
            case 0: return generateCompositePrefixCondition(compositeIdxCols, r, gen);
            case 1: return generateFullCompositeCondition(compositeIdxCols, r, gen);
            case 2: return generateIndexMergeCondition(singleIdxCols, indexedCols, r, gen);
            case 3: return generateRangeWithNullCondition(indexedCols, r, gen);
            case 4: return generateMultiIndexOrCondition(indexedCols, r, gen);
            default: return generateTypeAwareCondition(indexedCols, r, gen);
            }
        } catch (Exception e) {
            return null;
        }
    }

    // Strategy 1: For composite index (c0,c1,c2), generates c0=val AND c1>val2 to trigger prefix range scan.
    private MySQLExpression generateCompositePrefixCondition(
            List<List<MySQLColumn>> compositeIdxCols, Randomly r, MySQLExpressionGenerator gen) {
        if (compositeIdxCols.isEmpty()) return null;
        List<MySQLColumn> idxCols = Randomly.fromList(compositeIdxCols);
        // Use first N columns (prefix) where N = 1..min(3, total)
        int prefixLen = Math.min(idxCols.size(), r.getInteger(1, 4));
        MySQLExpression combined = null;
        for (int i = 0; i < prefixLen; i++) {
            MySQLColumn col = idxCols.get(i);
            MySQLExpression colRef = MySQLColumnReference.create(col, null);
            MySQLExpression condition;
            if (i == 0) {
                // First column: use equality for best selectivity (ref access)
                condition = new MySQLBinaryComparisonOperation(colRef,
                        generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.EQUALS);
            } else if (i == prefixLen - 1 && Randomly.getBoolean()) {
                // Last prefix column: use range to trigger range scan
                condition = generateRangeCondition(colRef, col, r);
            } else {
                condition = generateSimpleIndexCondition(colRef, col, r);
            }
            combined = (combined == null) ? condition
                    : new MySQLBinaryLogicalOperation(combined, condition, MySQLBinaryLogicalOperator.AND);
        }
        return maybeAddComplexExtra(combined, gen);
    }

    // Strategy 2: Uses ALL composite index columns with equality to trigger unique/ref lookup.
    private MySQLExpression generateFullCompositeCondition(
            List<List<MySQLColumn>> compositeIdxCols, Randomly r, MySQLExpressionGenerator gen) {
        if (compositeIdxCols.isEmpty()) return null;
        List<MySQLColumn> idxCols = Randomly.fromList(compositeIdxCols);
        MySQLExpression combined = null;
        for (MySQLColumn col : idxCols) {
            MySQLExpression colRef = MySQLColumnReference.create(col, null);
            MySQLExpression condition = new MySQLBinaryComparisonOperation(colRef,
                    generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.EQUALS);
            combined = (combined == null) ? condition
                    : new MySQLBinaryLogicalOperation(combined, condition, MySQLBinaryLogicalOperator.AND);
        }
        return maybeAddComplexExtra(combined, gen);
    }

    // Strategy 3: OR across differently-indexed columns triggers MySQL index_merge optimization.
    private MySQLExpression generateIndexMergeCondition(
            List<MySQLColumn> singleIdxCols, List<MySQLColumn> indexedCols, Randomly r, MySQLExpressionGenerator gen) {
        // Need at least 2 differently-indexed columns
        List<MySQLColumn> candidates = new ArrayList<>(singleIdxCols.size() >= 2 ? singleIdxCols : indexedCols);
        if (candidates.size() < 2) return null;

        Collections.shuffle(candidates);
        MySQLColumn col1 = candidates.get(0);
        MySQLColumn col2 = candidates.get(1);

        MySQLExpression colRef1 = MySQLColumnReference.create(col1, null);
        MySQLExpression colRef2 = MySQLColumnReference.create(col2, null);

        // Use range-friendly conditions on both sides to trigger index_merge
        MySQLExpression cond1 = generateRangeCondition(colRef1, col1, r);
        MySQLExpression cond2 = generateRangeCondition(colRef2, col2, r);

        MySQLExpression orCond = new MySQLBinaryLogicalOperation(cond1, cond2, MySQLBinaryLogicalOperator.OR);
        return maybeAddComplexExtra(orCond, gen);
    }

    // Strategy 4: Range condition combined with IS NULL/IS NOT NULL to test index NULL boundary handling.
    private MySQLExpression generateRangeWithNullCondition(
            List<MySQLColumn> indexedCols, Randomly r, MySQLExpressionGenerator gen) {
        MySQLColumn col = Randomly.fromList(indexedCols);
        MySQLExpression colRef = MySQLColumnReference.create(col, null);

        MySQLExpression rangeCond = generateRangeCondition(colRef, col, r);

        // 50% chance: AND col IS NOT NULL, 50%: OR col IS NULL
        MySQLExpression nullCond;
        if (Randomly.getBoolean()) {
            nullCond = new MySQLUnaryPostfixOperation(
                    MySQLColumnReference.create(col, null), UnaryPostfixOperator.IS_NULL, false);
            MySQLExpression orNull = new MySQLBinaryLogicalOperation(rangeCond, nullCond, MySQLBinaryLogicalOperator.OR);
            return maybeAddComplexExtra(orNull, gen);
        } else {
            nullCond = new MySQLUnaryPostfixOperation(
                    MySQLColumnReference.create(col, null), UnaryPostfixOperator.IS_NULL, true);
            MySQLExpression andNotNull = new MySQLBinaryLogicalOperation(rangeCond, nullCond, MySQLBinaryLogicalOperator.AND);
            return maybeAddComplexExtra(andNotNull, gen);
        }
    }

    // Strategy 5: Combines conditions on 2-3 indexed columns with OR to trigger sort-union index merge.
    private MySQLExpression generateMultiIndexOrCondition(
            List<MySQLColumn> indexedCols, Randomly r, MySQLExpressionGenerator gen) {
        if (indexedCols.size() < 2) return null;
        int numCols = Math.min(indexedCols.size(), r.getInteger(2, 4));
        List<MySQLColumn> shuffled = new ArrayList<>(indexedCols);
        Collections.shuffle(shuffled);

        MySQLExpression combined = null;
        for (int i = 0; i < numCols; i++) {
            MySQLColumn col = shuffled.get(i);
            MySQLExpression colRef = MySQLColumnReference.create(col, null);
            MySQLExpression condition;
            // Vary the operator type per column to test different merge strategies
            int variant = r.getInteger(0, 3);
            switch (variant) {
            case 0: // IN condition — triggers index merge union
                condition = new MySQLInOperation(colRef, generateConstantList(col.getType(), r, 3, 6), false);
                break;
            case 1: // BETWEEN — triggers index merge sort-union
                condition = new MySQLBetweenOperation(colRef,
                        generateSimpleConstant(col.getType(), r), generateSimpleConstant(col.getType(), r));
                break;
            default: // Range comparison
                condition = generateRangeCondition(colRef, col, r);
                break;
            }
            combined = (combined == null) ? condition
                    : new MySQLBinaryLogicalOperation(combined, condition, MySQLBinaryLogicalOperator.OR);
        }
        return maybeAddComplexExtra(combined, gen);
    }

    // Strategy 6: Conditions tailored to column type (INT: IN/BETWEEN, VARCHAR: eq/IN, float: range) to hit type-specific optimizer paths.
    private MySQLExpression generateTypeAwareCondition(
            List<MySQLColumn> indexedCols, Randomly r, MySQLExpressionGenerator gen) {
        MySQLColumn col = Randomly.fromList(indexedCols);
        MySQLExpression colRef = MySQLColumnReference.create(col, null);
        MySQLExpression condition;

        switch (col.getType()) {
        case INT:
            // For INT: use IN with many values to test index merge / range optimizer
            if (Randomly.getBoolean()) {
                condition = new MySQLInOperation(colRef, generateConstantList(col.getType(), r, 5, 15), false);
            } else {
                // col BETWEEN small AND big — wide range scan
                condition = new MySQLBetweenOperation(colRef,
                        generateSimpleConstant(col.getType(), r), generateSimpleConstant(col.getType(), r));
            }
            break;
        case VARCHAR:
            // For VARCHAR: use equality or IN with short strings
            if (Randomly.getBoolean()) {
                condition = new MySQLBinaryComparisonOperation(colRef,
                        generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.EQUALS);
            } else {
                condition = new MySQLInOperation(colRef, generateConstantList(col.getType(), r, 2, 5), false);
            }
            break;
        case FLOAT:
        case DOUBLE:
        case DECIMAL:
            // For float: use range conditions (>, <) to test floating-point index scan
            condition = generateRangeCondition(colRef, col, r);
            break;
        default:
            condition = generateSimpleIndexCondition(colRef, col, r);
            break;
        }

        // 40% chance to combine with another condition on a different indexed column
        if (indexedCols.size() >= 2 && Randomly.getBooleanWithRatherLowProbability()) {
            MySQLColumn col2;
            do { col2 = Randomly.fromList(indexedCols); } while (col2 == col);
            MySQLExpression colRef2 = MySQLColumnReference.create(col2, null);
            MySQLExpression cond2 = generateSimpleIndexCondition(colRef2, col2, r);
            MySQLBinaryLogicalOperator logicOp = Randomly.fromOptions(
                    MySQLBinaryLogicalOperator.AND, MySQLBinaryLogicalOperator.AND, MySQLBinaryLogicalOperator.OR);
            condition = new MySQLBinaryLogicalOperation(condition, cond2, logicOp);
        }

        return maybeAddComplexExtra(condition, gen);
    }

    // ==================== Condition Building Helpers ====================

    private MySQLExpression generateRangeCondition(MySQLExpression colRef, MySQLColumn col, Randomly r) {
        int variant = r.getInteger(0, 4);
        switch (variant) {
        case 0: return new MySQLBinaryComparisonOperation(colRef,
                generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.GREATER);
        case 1: return new MySQLBinaryComparisonOperation(colRef,
                generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.LESS);
        case 2: return new MySQLBinaryComparisonOperation(colRef,
                generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.GREATER_EQUALS);
        case 3: return new MySQLBetweenOperation(colRef,
                generateSimpleConstant(col.getType(), r), generateSimpleConstant(col.getType(), r));
        default: return new MySQLBinaryComparisonOperation(colRef,
                generateSimpleConstant(col.getType(), r), BinaryComparisonOperator.LESS_EQUALS);
        }
    }

    private List<MySQLExpression> generateConstantList(MySQLSchema.MySQLDataType type, Randomly r, int min, int max) {
        List<MySQLExpression> list = new ArrayList<>();
        int count = r.getInteger(min, max + 1);
        for (int i = 0; i < count; i++) {
            list.add(generateSimpleConstant(type, r));
        }
        return list;
    }

    // Keeps condition diversity by occasionally ANDing a random extra expression.
    private MySQLExpression maybeAddComplexExtra(MySQLExpression combined, MySQLExpressionGenerator gen) {
        if (combined != null && Randomly.getBooleanWithRatherLowProbability()) {
            try {
                MySQLExpression randomExtra = gen.generateExpression(0);
                return new MySQLBinaryLogicalOperation(combined, randomExtra, MySQLBinaryLogicalOperator.AND);
            } catch (Exception e) { }
        }
        return combined;
    }

    // Fallback: basic WHERE with no index awareness — uses all columns unconditionally.
    private MySQLExpression tryGenerateBasicWhere(List<MySQLTable> tables, MySQLExpressionGenerator gen) {
        try {
            List<MySQLColumn> allCols = new ArrayList<>();
            for (MySQLTable table : tables) {
                allCols.addAll(table.getColumns());
            }
            if (allCols.isEmpty()) return null;
            Randomly r = globalState.getRandomly();
            int numConditions = (int) (r.getPositiveInteger() % 3) + 1;
            MySQLExpression combined = null;
            for (int i = 0; i < numConditions; i++) {
                MySQLColumn targetCol = Randomly.fromList(allCols);
                MySQLExpression colRef = MySQLColumnReference.create(targetCol, null);
                MySQLExpression condition = generateSimpleIndexCondition(colRef, targetCol, r);
                if (combined == null) {
                    combined = condition;
                } else {
                    MySQLBinaryLogicalOperator op = Randomly.fromOptions(
                            MySQLBinaryLogicalOperator.AND, MySQLBinaryLogicalOperator.AND, MySQLBinaryLogicalOperator.OR);
                    combined = new MySQLBinaryLogicalOperation(combined, condition, op);
                }
            }
            return maybeAddComplexExtra(combined, gen);
        } catch (Exception e) {
            return null;
        }
    }

    private MySQLExpression generateSimpleIndexCondition(MySQLExpression colRef, MySQLColumn col, Randomly r) {
        int opType = r.getInteger(0, 7);
        switch (opType) {
        case 0: { // col = value
            MySQLExpression val = generateSimpleConstant(col.getType(), r);
            return new MySQLBinaryComparisonOperation(colRef, val, BinaryComparisonOperator.EQUALS);
        }
        case 1: { // col > value
            MySQLExpression val = generateSimpleConstant(col.getType(), r);
            return new MySQLBinaryComparisonOperation(colRef, val, BinaryComparisonOperator.GREATER);
        }
        case 2: { // col < value
            MySQLExpression val = generateSimpleConstant(col.getType(), r);
            return new MySQLBinaryComparisonOperation(colRef, val, BinaryComparisonOperator.LESS);
        }
        case 3: { // col BETWEEN a AND b
            MySQLExpression left = generateSimpleConstant(col.getType(), r);
            MySQLExpression right = generateSimpleConstant(col.getType(), r);
            return new MySQLBetweenOperation(colRef, left, right);
        }
        case 4: { // col IS NULL
            return new MySQLUnaryPostfixOperation(colRef, UnaryPostfixOperator.IS_NULL, false);
        }
        case 5: { // col IN (v1, v2, v3) — uses simple constants
            List<MySQLExpression> inList = new ArrayList<>();
            for (int i = 0; i < r.getInteger(2, 5); i++) {
                inList.add(generateSimpleConstant(col.getType(), r));
            }
            return new MySQLInOperation(colRef, inList, false);
        }
        case 6: { // col >= value
            MySQLExpression val = generateSimpleConstant(col.getType(), r);
            return new MySQLBinaryComparisonOperation(colRef, val, BinaryComparisonOperator.GREATER_EQUALS);
        }
        default: { // col <= value
            MySQLExpression val = generateSimpleConstant(col.getType(), r);
            return new MySQLBinaryComparisonOperation(colRef, val, BinaryComparisonOperator.LESS_EQUALS);
        }
        }
    }

    private MySQLExpression generateSimpleConstant(MySQLSchema.MySQLDataType type, Randomly r) {
        switch (type) {
        case INT:
            //Use smaller range to avoid boundary values like 2147483647
            return MySQLConstant.createIntConstant(r.getInteger(0, 100000));
        case VARCHAR:
            return MySQLConstant.createStringConstant(generateRandomString(r).replace("'", "''"));
        case FLOAT:
        case DOUBLE:
        case DECIMAL:
            // No createDoubleConstant — use string representation for float values
            return MySQLConstant.createStringConstant(String.valueOf(r.getDouble()));
        default:
            //Use smaller range for default case too
            return MySQLConstant.createIntConstant(r.getInteger(0, 100000));
        }
    }

    // Escapes '' and \\ for SQL string literals; strips control chars (newline, NUL, tab, etc.) that break syntax.
    private static String sanitizeForSqlString(String val) {
        // Remove control characters that can break SQL string literals
        // Keep printable chars and standard whitespace (space only)
        StringBuilder sb = new StringBuilder(val.length());
        for (int i = 0; i < val.length(); i++) {
            char c = val.charAt(i);
            if (c == '\'') {
                sb.append("''");
            } else if (c == '\\') {
                sb.append("\\\\");
            } else if (c >= 0x20 && c < 0x7F) {
                // Printable ASCII — keep as-is
                sb.append(c);
            } else if (c == ' ') {
                sb.append(c);
            } else if (Character.isDefined(c) && !Character.isISOControl(c)) {
                // Non-control Unicode (multi-byte chars, CJK, etc.) — keep
                sb.append(c);
            }
            // else: drop control characters (newline, tab, NUL, etc.)
        }
        return sb.toString();
    }

    // 20% chance produces multi-byte Unicode (Hebrew/CJK/Emoji) to stress-test prefix index range scans.
    private String generateRandomString(Randomly r) {
        if (Randomly.getBooleanWithRatherLowProbability()) {
            return generateMultiByteString(r);
        }
        return r.getString();
    }

    // Covers Hebrew (2-byte), Latin Extended (2-byte), CJK (3-byte), Emoji surrogate pairs (4-byte),
    // and mixed multi-byte+ASCII (e.g., 0xD6B2+'/') — the exact pattern from the prefix index bug report.
    private static String generateMultiByteString(Randomly r) {
        int strategy = r.getInteger(0, 6);
        StringBuilder sb = new StringBuilder();
        switch (strategy) {
        case 0: {
            // Hebrew characters (2-byte UTF-8) — covers the exact bug scenario
            // Hebrew accent ZINOR (U+05B2) = 0xD6B2 in UTF-8
            int len = r.getInteger(1, 4);
            for (int i = 0; i < len; i++) {
                sb.append((char) r.getInteger(0x0590, 0x05FF));
            }
            // Optionally append ASCII to create mixed encoding
            if (Randomly.getBoolean()) {
                String asciiPart = r.getString();
                if (!asciiPart.isEmpty()) {
                    sb.append(asciiPart.substring(0, Math.min(2, asciiPart.length())));
                }
            }
            break;
        }
        case 1: {
            // Latin Extended / accented characters (2-byte UTF-8)
            int len = r.getInteger(1, 4);
            for (int i = 0; i < len; i++) {
                sb.append((char) r.getInteger(0x00C0, 0x024F));
            }
            break;
        }
        case 2: {
            // CJK characters (3-byte UTF-8)
            int len = r.getInteger(1, 3);
            for (int i = 0; i < len; i++) {
                sb.append((char) r.getInteger(0x4E00, 0x9FFF));
            }
            break;
        }
        case 3: {
            // Surrogate pair for Emoji (4-byte UTF-8) — high surrogate + low surrogate
            char high = (char) r.getInteger(0xD83D, 0xD83E);
            char low = (char) r.getInteger(0xDC00, 0xDE00);
            sb.append(high).append(low);
            break;
        }
        case 4: {
            // Mixed: single multi-byte char + ASCII punctuation (exact bug pattern)
            // Pick a random 2-byte UTF-8 character
            char multiByte = (char) r.getInteger(0x0080, 0x07FF);
            sb.append(multiByte);
            // Append common ASCII chars that appear in range comparisons
            String asciiSuffix = Randomly.fromOptions("/", "&", "0", "a", "Z", " ", "-", ".");
            sb.append(asciiSuffix);
            break;
        }
        default: {
            // Random mix of ASCII and multi-byte characters
            int len = r.getInteger(1, 5);
            for (int i = 0; i < len; i++) {
                if (Randomly.getBoolean()) {
                    // ASCII character
                    sb.append((char) r.getInteger(0x20, 0x7F));
                } else {
                    // Multi-byte character (2-byte UTF-8 range)
                    sb.append((char) r.getInteger(0x0080, 0x07FF));
                }
            }
            break;
        }
        }
        return sb.toString();
    }

    // ==================== Index Management Helpers ====================

    private void ensureIndexesExist() {
        try {
            // Collect existing index signatures to avoid duplicates
            Set<String> existingIndexSigs = collectExistingIndexSignatures();
            int numIndexes = Randomly.smallNumber() + 1;
            int created = 0;
            for (int i = 0; i < numIndexes * 3 && created < numIndexes; i++) {
                try {
                    // Check if we already have enough indexes
                    Set<String> currentSigs = collectExistingIndexSignatures();
                    if (currentSigs.size() >= 10) break; // Don't over-create indexes
                    SQLQueryAdapter createIndex = MySQLIndexGenerator.create(globalState);
                    globalState.executeStatement(createIndex);
                    created++;
                } catch (Exception e) { }
            }
            analyzeAllTables();
        } catch (Exception e) { }
    }

    private Set<String> collectExistingIndexSignatures() {
        Set<String> sigs = new HashSet<>();
        try {
            MySQLSchema schema = globalState.getSchema();
            for (MySQLTable table : schema.getDatabaseTables()) {
                for (MySQLIndex idx : table.getIndexes()) {
                    List<String> colNames = idx.getColumnNames();
                    if (colNames != null && !colNames.isEmpty()) {
                        List<String> sorted = new ArrayList<>(colNames);
                        Collections.sort(sorted);
                        sigs.add(table.getName() + ":" + String.join(",", sorted));
                    }
                }
            }
        } catch (Exception e) { }
        return sigs;
    }

    private void analyzeAllTables() {
        try {
            MySQLSchema schema = globalState.getSchema();
            for (MySQLTable table : schema.getDatabaseTables()) {
                try {
                    globalState.executeStatement(new SQLQueryAdapter(
                            "ANALYZE TABLE " + table.getName() + ";", true));
                } catch (Exception e) { }
            }
        } catch (Exception e) { }
    }

    // Faster than analyzeAllTables() when only one table's indexes were modified.
    private void analyzeTable(String tableName) {
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "ANALYZE TABLE " + tableName + ";", true));
        } catch (Exception e) {
            // ANALYZE TABLE is best-effort
        }
    }

    private MySQLSchema.MySQLIndex getRandomNonPrimaryIndex() {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLSchema.MySQLIndex> allIndexes = new ArrayList<>();
        for (MySQLTable table : schema.getDatabaseTables()) {
            for (MySQLIndex idx : table.getIndexes()) {
                String name = idx.getIndexName();
                if (!name.equals("PRIMARY") && !name.equals("`PRIMARY`") && name.startsWith("i")) {
                    allIndexes.add(idx);
                }
            }
        }
        if (allIndexes.isEmpty()) return null;
        return Randomly.fromList(allIndexes);
    }

    private String findTableForIndex(MySQLSchema.MySQLIndex targetIdx) {
        MySQLSchema schema = globalState.getSchema();
        for (MySQLTable table : schema.getDatabaseTables()) {
            for (MySQLIndex idx : table.getIndexes()) {
                if (idx == targetIdx) {
                    return table.getName();
                }
            }
        }
        return null;
    }

    // ==================== Helper Methods ====================

    private void log(String queryString) {
        if (globalState.getOptions().logEachSelect()) {
            globalState.getLogger().writeCurrent(queryString);
        }
    }

    private List<String> executeQuery(String queryString) throws Exception {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(queryString, errors, globalState, " ||| ");
        } catch (IgnoreMeException e) {
            return null;
        }
    }

    private boolean safeSetSwitch(String switchVal) {
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "SET SESSION optimizer_switch = '" + switchVal + "';", true));
            return true;
        } catch (Throwable e) {
            // Catches both Exception and AssertionError (which extends Error, not Exception).
            // AssertionError can arise when SQLQueryAdapter.checkException encounters an
            // unexpected SQL error (e.g., an unsupported optimizer_switch value in this
            // MySQL version).  Catching Throwable here is safe because this method only
            // sets session variables — it never executes test queries whose result-set
            // mismatches would indicate a real bug.
            return false;
        }
    }

    private void restoreDefaultSettings() throws Exception {
        globalState.executeStatement(new SQLQueryAdapter(
                "SET SESSION optimizer_switch = 'default';", true));
    }

    // GROUP BY with only constant expressions (GROUP BY NULL, GROUP BY 1+2, etc.) collapses all rows into one group;
    // MySQL picks arbitrary non-aggregated column values depending on execution plan — different indexes yield different rows.
    private boolean hasNonDeterministicGroupBy(String query) {
        String upperQuery = query.toUpperCase();
        if (!upperQuery.contains("GROUP BY")) return false;

        // === Check 1: GROUP BY with no column references at all (constant GROUP BY) ===
        // Extract the GROUP BY clause content
        int groupByStart = upperQuery.indexOf("GROUP BY");
        if (groupByStart == -1) return false;
        String afterGroupBy = query.substring(groupByStart + "GROUP BY".length()).trim();

        // Find the end of GROUP BY clause (before HAVING, ORDER BY, LIMIT, or end)
        int endIdx = afterGroupBy.length();
        for (String keyword : new String[]{" HAVING ", " ORDER BY ", " LIMIT ", " INTO "}) {
            int idx = afterGroupBy.toUpperCase().indexOf(keyword);
            if (idx != -1 && idx < endIdx) {
                endIdx = idx;
            }
        }
        String groupByExpr = afterGroupBy.substring(0, endIdx).trim();

        // Check if the GROUP BY expression contains any column reference.
        String[] groupByParts = groupByExpr.split(",");
        boolean groupByHasColumnRef = false;
        for (String part : groupByParts) {
            String trimmed = part.trim();
            if (trimmed.matches(".*\\bt\\d+\\.c\\d+\\b.*") ||
                trimmed.matches(".*\\bc\\d+\\b.*")) {
                groupByHasColumnRef = true;
                break;
            }
        }
        if (!groupByHasColumnRef) {
            // All GROUP BY expressions are constants → non-deterministic
            return true;
        }

        // === Check 2: SELECT has non-aggregated column references ===
        // MySQL's non-standard GROUP BY allows SELECT columns that are neither
        // aggregated nor in GROUP BY. The value picked for such columns is
        // non-deterministic (depends on execution plan / index scan order).
        // This is the case that caused database2.log false positive:
        //   SELECT (t0.c0) NOT IN (CAST(t0.c0 AS SIGNED)) ...
        //   GROUP BY IFNULL(NOT(t0.c0), constant)
        // The GROUP BY maps ALL non-NULL rows to one group, and the representative
        // row depends on which index is used.
        if (hasNonAggregatedSelectColumns(query)) {
            return true;
        }

        return false;
    }

    // SELECT columns not inside an aggregate are non-deterministic when GROUP BY is present (MySQL picks arbitrary row per group).
    private boolean hasNonAggregatedSelectColumns(String query) {
        String upperQuery = query.toUpperCase();

        // Extract SELECT clause (between SELECT and FROM)
        int selectStart = upperQuery.indexOf("SELECT");
        if (selectStart == -1) return false;

        // Handle SELECT DISTINCT
        int fromIdx = upperQuery.indexOf("FROM");
        if (fromIdx == -1 || fromIdx <= selectStart) return false;

        String selectClause = query.substring(selectStart + "SELECT".length(), fromIdx).trim();
        // Remove DISTINCT keyword if present
        if (selectClause.toUpperCase().startsWith("DISTINCT")) {
            selectClause = selectClause.substring("DISTINCT".length()).trim();
        }
        // Remove STRAIGHT_JOIN keyword if present
        if (selectClause.toUpperCase().startsWith("STRAIGHT_JOIN")) {
            selectClause = selectClause.substring("STRAIGHT_JOIN".length()).trim();
        }

        // Now check if selectClause contains any column references NOT inside aggregates.
        // Aggregate functions: COUNT, SUM, MIN, MAX, AVG, GROUP_CONCAT, ANY_VALUE, BIT_AND, BIT_OR, BIT_XOR, STD, STDDEV, VARIANCE, JSON_ARRAYAGG, JSON_OBJECTAGG
        // We use a simple heuristic: strip out aggregate function contents, then check
        // if the remaining text has column references.

        // Remove aggregate function contents recursively
        String cleaned = removeAggregateFunctions(selectClause);

        // Check if remaining text contains column references
        if (cleaned.matches(".*\\bt\\d+\\.c\\d+\\b.*") ||
            cleaned.matches(".*\\bc\\d+\\b.*")) {
            return true;
        }

        return false;
    }

    // Strips aggregate function arguments so only non-aggregated column refs remain (handles nested parens).
    private String removeAggregateFunctions(String expr) {
        String[] aggregateFunctions = {
            "COUNT", "SUM", "MIN", "MAX", "AVG", "GROUP_CONCAT",
            "ANY_VALUE", "BIT_AND", "BIT_OR", "BIT_XOR",
            "STD", "STDDEV", "STDDEV_POP", "STDDEV_SAMP",
            "VAR_POP", "VAR_SAMP", "VARIANCE",
            "JSON_ARRAYAGG", "JSON_OBJECTAGG"
        };

        String result = expr;
        for (String func : aggregateFunctions) {
            // Case-insensitive removal: find FUNC( ... ) and replace with FUNC()
            result = removeFunctionCall(result, func);
        }
        return result;
    }

    // Replaces content inside a function call with empty parens (handles nested parens).
    // E.g., COUNT(t0.c0 + t0.c1) → COUNT(), SUM(IF(t0.c0 > 0, t0.c0, 0)) → SUM().
    private String removeFunctionCall(String expr, String funcName) {
        String upperExpr = expr.toUpperCase();
        StringBuilder result = new StringBuilder();
        int i = 0;
        while (i < expr.length()) {
            // Check if funcName starts at this position
            if (i + funcName.length() <= upperExpr.length() &&
                upperExpr.substring(i, i + funcName.length()).equals(funcName)) {
                // Check it's not part of a longer identifier
                boolean isWordBoundaryBefore = (i == 0 || !Character.isLetterOrDigit(expr.charAt(i - 1)) && expr.charAt(i - 1) != '_');
                int endFunc = i + funcName.length();
                boolean isWordBoundaryAfter = (endFunc >= expr.length() || !Character.isLetterOrDigit(expr.charAt(endFunc)) && expr.charAt(endFunc) != '_');
                if (isWordBoundaryBefore && isWordBoundaryAfter) {
                    // Found the function name. Now find the opening paren
                    int j = endFunc;
                    while (j < expr.length() && Character.isWhitespace(expr.charAt(j))) j++;
                    if (j < expr.length() && expr.charAt(j) == '(') {
                        // Find the matching closing paren
                        int depth = 1;
                        int parenStart = j;
                        j++;
                        while (j < expr.length() && depth > 0) {
                            if (expr.charAt(j) == '(') depth++;
                            else if (expr.charAt(j) == ')') depth--;
                            j++;
                        }
                        // Replace the entire function call with funcName()
                        result.append(funcName).append("()");
                        i = j;
                        continue;
                    }
                }
            }
            result.append(expr.charAt(i));
            i++;
        }
        return result.toString();
    }

    private static int nullSafeCompare(String a, String b) {
        if (a == null && b == null) return 0;
        if (a == null) return -1;
        if (b == null) return 1;
        return a.compareTo(b);
    }

    // Sorted comparison for un-ordered result sets; LIMIT without ORDER BY skipped (non-deterministic).
    // Sets lastCompareFiltered=true when filtered so callers can use COUNT(*) fallback.
    private void compareResultsSorted(List<String> r1, List<String> r2, String queryString, String mode) throws Exception {
        lastCompareFiltered = false; // Reset flag
        queriesCompared++; // Track how many queries were actually compared
        // Quick equality check
        if (r1.equals(r2)) return;

        // Null-safe sorted comparison
        List<String> sorted1 = new ArrayList<>(r1);
        List<String> sorted2 = new ArrayList<>(r2);
        sorted1.sort(PolarDBIndexOracle::nullSafeCompare);
        sorted2.sort(PolarDBIndexOracle::nullSafeCompare);
        if (sorted1.equals(sorted2)) return;

        // Approximate numeric comparison (null-safe)
        if (areApproximatelyEqual(sorted1, sorted2)) return;

        String upperQuery = queryString.toUpperCase();

        // LIMIT without ORDER BY → non-deterministic row selection, skip mismatch
        if (upperQuery.contains("LIMIT") && !upperQuery.contains("ORDER BY")) {
            lastCompareFiltered = true; Flag for COUNT(*) fallback
            return;
        }

        // GROUP BY with constant expressions (no column refs) → non-deterministic.
        if (hasNonDeterministicGroupBy(queryString)) {
            lastCompareFiltered = true; Flag for COUNT(*) fallback
            return;
        }

        REMOVED: GROUP BY with different result set sizes filter.
        // GROUP BY on deterministic expressions should always produce the same number of rows.
        // Non-deterministic GROUP BY is already handled above.
        // Different sizes = real bug (missing/extra rows from index plan).

        REMOVED: LIMIT with different result sizes blanket filter.
        // This was too aggressive — different sizes with LIMIT can indicate a real bug
        // (one plan returns fewer rows than it should). Non-deterministic LIMIT is
        // handled below by checking ORDER BY tie-breaker uniqueness.

        // LIMIT + ORDER BY: If ORDER BY has unique sort keys → deterministic → report.
        // If ORDER BY only has non-unique columns → the subset of rows selected by LIMIT
        // is itself non-deterministic (different plans may pick different tied rows),
        // so both order AND content can differ — skip entirely to avoid false positives.
        if (upperQuery.contains("LIMIT") && upperQuery.contains("ORDER BY")) {
            if (hasUniqueOrderByTieBreaker(queryString)) {
                // ORDER BY has unique tie-breaker → result should be fully deterministic
                // Fall through to report the bug
            } else {
                // No unique tie-breaker + LIMIT → row selection is non-deterministic
                lastCompareFiltered = true; Flag for COUNT(*) fallback
                return;
            }
        }

        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] Query: " + queryString);
        effectiveTests++; Count this as an effective test
        ComparatorHelper.assumeResultSetsAreEqual(r1, r2, queryString, combinedString, globalState);
    }

    // Strict (ordered) comparison; LIMIT+ORDER BY with a unique tie-breaker is compared strictly.
    private void compareResultsStrict(List<String> r1, List<String> r2, String queryString, String mode) throws Exception {
        queriesCompared++; // Track how many queries were actually compared
        if (r1.equals(r2)) return;

        String upperQuery = queryString.toUpperCase();

        // LIMIT without ORDER BY → non-deterministic, skip
        if (upperQuery.contains("LIMIT") && !upperQuery.contains("ORDER BY")) {
            return;
        }

        // GROUP BY with different result set sizes → non-deterministic
        if (r1.size() != r2.size() && upperQuery.contains("GROUP BY")) {
            return;
        }

        // LIMIT with different result sizes → check if ORDER BY is unique
        if (r1.size() != r2.size() && upperQuery.contains("LIMIT")) {
            if (!hasUniqueOrderByTieBreaker(queryString)) {
                return; // Non-unique ORDER BY + LIMIT → non-deterministic
            }
            // Unique ORDER BY + LIMIT but different sizes → real bug, fall through
        }

        if (areApproximatelyEqual(r1, r2)) return;

        // LIMIT + ORDER BY: If unique tie-breaker → deterministic → report.
        // Otherwise row selection is non-deterministic → skip to avoid false positives.
        if (upperQuery.contains("LIMIT") && upperQuery.contains("ORDER BY")) {
            if (hasUniqueOrderByTieBreaker(queryString)) {
                // Deterministic ORDER BY → different order = real bug → fall through
            } else {
                // No unique tie-breaker + LIMIT → row selection is non-deterministic
                return;
            }
        }

        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] Query: " + queryString);
        effectiveTests++; Count this as an effective test
        ComparatorHelper.assumeResultSetsAreEqual(r1, r2, queryString, combinedString, globalState);
    }

    // ==================== P1: Tie-Breaker Detection ====================

    // Returns null on parse failure (conservative: treats as non-unique tie-breaker).
    private Set<String> extractFromTables(String queryString) {
        try {
            String upper = queryString.toUpperCase();
            int fromIdx = upper.indexOf("FROM ");
            if (fromIdx == -1) return null;

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

            String[] parts = fromClause.split(",");
            for (String part : parts) {
                String trimmed = part.trim();
                trimmed = trimmed.replaceAll("(?i)\\s+AS\\s+\\S+", "");
                trimmed = trimmed.replaceAll("(?i)^(t\\d+)(\\s+\\S+)?$", "$1");
                trimmed = trimmed.trim();
                if (trimmed.matches("t\\d+")) {
                    tables.add(trimmed);
                }
            }

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

    private boolean hasUniqueOrderByTieBreaker(String queryString) {
        try {
            String upperQuery = queryString.toUpperCase();
            int orderByIdx = upperQuery.indexOf("ORDER BY");
            if (orderByIdx == -1) return false;

            String afterOrderBy = queryString.substring(orderByIdx + "ORDER BY".length());
            // Find end of ORDER BY clause
            int endIdx = afterOrderBy.length();
            for (String kw : new String[]{" LIMIT ", " OFFSET ", " INTO ", " FOR "}) {
                int idx = afterOrderBy.toUpperCase().indexOf(kw);
                if (idx != -1 && idx < endIdx) endIdx = idx;
            }
            String orderByClause = afterOrderBy.substring(0, endIdx).trim();

            // Only check tables that actually appear in the FROM clause.
            // This prevents false matches where table t0 has PK column c0,
            // but the query is on table t1 (which has no such unique constraint on c0).
            Set<String> fromTables = extractFromTables(queryString);
            if (fromTables == null) {
                return false;
            }

            // Check each ORDER BY expression for primary key or unique column references
            MySQLSchema schema = globalState.getSchema();
            for (String part : orderByClause.split(",")) {
                String expr = part.trim();
                // Remove ASC/DESC suffix
                expr = expr.replaceAll("(?i)\\s+(ASC|DESC)\\s*$", "").trim();

                // Check if this expression references a primary key or unique column
                for (MySQLTable table : schema.getDatabaseTables()) {
                    String tblName = table.getName();
                    // Only consider tables that appear in the FROM clause
                    if (!fromTables.contains(tblName)) continue;
                    for (MySQLColumn col : table.getColumns()) {
                        if (col.isPrimaryKey()) {
                            // Use exact match (equals), NOT contains(), to avoid false positives.
                            // contains() matches column refs inside complex expressions
                            // like CAST(... IN (t0.c0) ...), which do NOT guarantee unique ordering.
                            // Only a direct column reference (e.g., ORDER BY t0.c0 or ORDER BY c0)
                            // preserves the uniqueness guarantee of the primary key.
                            String colRef1 = tblName + "." + col.getName();
                            String colRef2 = col.getName();
                            if (expr.equals(colRef1) || expr.equals(colRef2)) {
                                return true;
                            }
                        }
                    }
                    // Also check unique indexes — but must verify no NULL values exist.
                    // MySQL UNIQUE indexes allow multiple NULLs, making ORDER BY non-deterministic.
                    for (MySQLIndex idx : table.getIndexes()) {
                        if (idx.isUnique() && idx.getColumnNames().size() == 1) {
                            String idxCol = idx.getColumnNames().get(0);
                            String colRef1 = tblName + "." + idxCol;
                            if (expr.equals(colRef1) || expr.equals(idxCol)) {
                                if (!columnHasNullValues(table, idxCol)) {
                                    return true;
                                }
                                // Column has NULLs → not a reliable tie-breaker
                            }
                        }
                    }
                }
            }
            return false;
        } catch (Exception e) {
            return false;
        }
    }

    // Conservative: returns true on error (assumes NULLs exist, disqualifying column as tie-breaker).
    private boolean columnHasNullValues(MySQLTable table, String columnName) {
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

    // ==================== P5: EXPLAIN Plan Verification ====================

    private List<String> getExplainPlan(String queryString) {
        List<String> plan = new ArrayList<>();
        try {
            String explainQuery = "EXPLAIN " + queryString;
            try (Statement stmt = globalState.getConnection().createStatement();
                 ResultSet rs = stmt.executeQuery(explainQuery)) {
                while (rs.next()) {
                    String id = rs.getString("id");
                    String table = rs.getString("table");
                    String type = rs.getString("type");
                    String key = rs.getString("key");
                    String rows = rs.getString("rows");
                    String extra = rs.getString("Extra");
                    plan.add(id + "|" + table + "|" + type + "|" + key + "|" + rows + "|" + extra);
                }
            }
        } catch (Exception e) {
            // EXPLAIN may fail for various reasons
        }
        return plan;
    }

    // Compares type+key+Extra fields; same type+key but different Extra (e.g., "Using index" vs "Using where",
    // ICP vs no-ICP) still counts as different — these execution strategies can produce different results.
    private boolean plansAreDifferent(List<String> plan1, List<String> plan2) {
        if (plan1.isEmpty() || plan2.isEmpty()) return true; // Can't verify, assume different
        if (plan1.size() != plan2.size()) return true;

        for (int i = 0; i < plan1.size(); i++) {
            String[] parts1 = plan1.get(i).split("\\|");
            String[] parts2 = plan2.get(i).split("\\|");
            // Compare type (access method) and key (index used)
            String type1 = parts1.length > 2 ? parts1[2] : "";
            String type2 = parts2.length > 2 ? parts2[2] : "";
            String key1 = parts1.length > 3 ? parts1[3] : "";
            String key2 = parts2.length > 3 ? parts2[3] : "";

            // Ignore NULL comparisons (subqueries may have NULL table)
            if (type1.equals("NULL") || type2.equals("NULL")) continue;

            if (!type1.equals(type2) || !key1.equals(key2)) {
                return true; // Plans differ in access method or index
            }

            Also compare Extra field (index 5) for execution strategy differences
            String extra1 = parts1.length > 5 ? parts1[5] : "";
            String extra2 = parts2.length > 5 ? parts2[5] : "";
            if (!extra1.equals(extra2)) {
                // Normalize: remove row estimate differences that are not execution-relevant.
                // Extra can contain "rows=100" which varies between plans but doesn't affect
                // result correctness. Only compare the execution strategy keywords.
                String normExtra1 = normalizeExtraField(extra1);
                String normExtra2 = normalizeExtraField(extra2);
                if (!normExtra1.equals(normExtra2)) {
                    return true; // Different execution strategies
                }
            }
        }
        explainFiltered++; // Track how many tests were filtered out by identical plans
        return false; // Plans are identical
    }

    // Strips rows=/cost= estimates (vary per plan) but keeps execution-strategy keywords like "Using index".
    private String normalizeExtraField(String extra) {
        if (extra == null) return "";
        // Remove row/cost estimates that vary between plans
        return extra.replaceAll("rows=\\d+", "rows=N")
                    .replaceAll("cost=[\\d.]+", "cost=N")
                    .trim();
    }

    // Effective types: ref/range/const/eq_ref — excludes ALL (table scan) and index (full index scan).
    private boolean isIndexEffectivelyUsed(List<String> plan, String targetIndex) {
        Set<String> effectiveTypes = new HashSet<>(Arrays.asList(
                "ref", "range", "const", "eq_ref", "ref_or_null", "unique_subquery", "index_subquery"));
        for (String line : plan) {
            String[] parts = line.split("\\|");
            String type = parts.length > 2 ? parts[2] : "";
            String key = parts.length > 3 ? parts[3] : "";
            if (key.equals(targetIndex) && effectiveTypes.contains(type)) {
                return true;
            }
        }
        return false;
    }

    private boolean planHasExtra(List<String> plan, String extraPattern) {
        for (String line : plan) {
            if (line.contains(extraPattern)) {
                return true;
            }
        }
        return false;
    }

    // Falls back to AST query only if no index exists after attempting to create one.
    private String generateIndexAwareOrASTQuery() {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (!tables.isEmpty()) {
            MySQLTable table = Randomly.fromList(tables);
            List<MySQLIndex> indexes = table.getIndexes();
            // If no indexes exist, try to create one first
            if (indexes.isEmpty()) {
                try {
                    MySQLIndexGenerator.create(globalState);
                    analyzeTable(table.getName());
                    indexes = table.getIndexes();
                } catch (Exception e) {
                    // index creation may fail
                }
            }
            if (!indexes.isEmpty()) {
                MySQLIndex idx = Randomly.fromList(indexes);
                return generateIndexAwareQueryString(table, idx);
            }
        }
        return generateASTQuery();
    }

    // Column delimiter used by executeQuery via getResultSetAllColumnsAsString.
    private static final String COLUMN_DELIMITER = " ||| ";

    private boolean areApproximatelyEqual(List<String> r1, List<String> r2) {
        if (r1.size() != r2.size()) return false;
        for (int i = 0; i < r1.size(); i++) {
            String s1 = r1.get(i);
            String s2 = r2.get(i);
            if (s1 == null && s2 == null) continue;
            if (s1 == null || s2 == null) return false;
            if (s1.equals(s2)) continue;
            // Multi-column rows: split by delimiter and compare column-by-column
            if (s1.contains(COLUMN_DELIMITER) && s2.contains(COLUMN_DELIMITER)) {
                String[] cols1 = s1.split(java.util.regex.Pattern.quote(COLUMN_DELIMITER));
                String[] cols2 = s2.split(java.util.regex.Pattern.quote(COLUMN_DELIMITER));
                if (cols1.length != cols2.length) return false;
                boolean allColsApproxOrEqual = true;
                for (int j = 0; j < cols1.length; j++) {
                    if (cols1[j].equals(cols2[j])) continue;
                    if (isApproximatelyEqualNumeric(cols1[j], cols2[j])) continue;
                    allColsApproxOrEqual = false;
                    break;
                }
                if (allColsApproxOrEqual) continue;
            }
            // Single-column fallback: try numeric comparison on the whole string
            if (isApproximatelyEqualNumeric(s1, s2)) continue;
            return false;
        }
        return true;
    }

    // Integer values require exact match (COUNT=100 vs 99 is a real bug, not floating-point noise).
    // Float/DOUBLE uses 1e-10 relative tolerance — old 1e-6 was masking COUNT(*)=99.9999 vs 100.
    private boolean isApproximatelyEqualNumeric(String s1, String s2) {
        Fast path: if both look like integers, require exact match
        if (isIntegerString(s1) && isIntegerString(s2)) {
            return s1.equals(s2); // "100" != "99" → real bug
        }

        try {
            double d1 = Double.parseDouble(s1);
            double d2 = Double.parseDouble(s2);
            if (Double.isNaN(d1) || Double.isNaN(d2)) return Double.isNaN(d1) && Double.isNaN(d2);
            if (Double.isInfinite(d1) || Double.isInfinite(d2)) return d1 == d2;
            double diff = Math.abs(d1 - d2);
            double maxVal = Math.max(Math.abs(d1), Math.abs(d2));
            if (maxVal < EPSILON) return diff < EPSILON;
            Much tighter tolerance: 1e-10 instead of 1e-6
            // Index bugs in COUNT/SUM/AVG typically cause off-by-1 or larger errors,
            // not micro-floating-point differences. 1e-6 was masking COUNT(*)=100 vs 99.9999.
            return diff / maxVal < 1e-10;
        } catch (NumberFormatException e) {
            return false;
        }
    }

    private boolean isIntegerString(String s) {
        if (s == null || s.isEmpty()) return false;
        int start = 0;
        if (s.charAt(0) == '-') start = 1;
        if (start >= s.length()) return false;
        for (int i = start; i < s.length(); i++) {
            if (!Character.isDigit(s.charAt(i))) return false;
        }
        return true;
    }

    // Mode 24 (FULLTEXT) removed — PolarDB-X does not support FULLTEXT indexes.

    private void checkFullTextIndex_REMOVED_DO_NOT_CALL() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with VARCHAR/TEXT columns
        MySQLTable table = Randomly.fromList(tables);
        List<MySQLColumn> textCols = new ArrayList<>();
        for (MySQLColumn col : table.getColumns()) {
            Skip generated columns — FULLTEXT index cannot be created on
            // VIRTUAL/STORED generated columns (MySQL limitation).
            if (col.getName().startsWith("gen_col_")) continue;
            if (col.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
                textCols.add(col);
            }
        }
        if (textCols.isEmpty()) return;

        String tblName = table.getName();
        MySQLColumn col = Randomly.fromList(textCols);
        String colName = col.getName();

        // Create FULLTEXT index
        Detect index name collision and regenerate a unique name.
        // The name is based on colName.hashCode() % 10000, which can collide
        // when different columns hash to the same value. If the generated name
        // already exists on this table (possibly on a different column), we
        // append a random suffix until we find a unique name. This ensures the
        // FULLTEXT index is actually created on the correct column, avoiding
        // false bug reports from MATCH...AGAINST on the wrong column.
        String ftIdxName = "ft_idx_" + Math.abs(colName.hashCode() % 10000);
        Set<String> existingIdxNames = new HashSet<>();
        for (MySQLIndex idx : table.getIndexes()) {
            existingIdxNames.add(idx.getIndexName().toLowerCase());
        }
        // If name collides, keep trying with random suffixes
        int maxRetries = 10;
        while (existingIdxNames.contains(ftIdxName.toLowerCase()) && maxRetries-- > 0) {
            ftIdxName = "ft_idx_" + Math.abs(colName.hashCode() % 10000) + "_" + Randomly.smallNumber();
        }
        if (existingIdxNames.contains(ftIdxName.toLowerCase())) {
            return; // Couldn't find a unique name, skip this test
        }

        ExpectedErrors ftErrors = new ExpectedErrors();
        ftErrors.add("FULLTEXT");
        ftErrors.add("Incorrect prefix key");
        ftErrors.add("used in key specification without a key length");
        ftErrors.add("BLOB/TEXT column");
        ftErrors.add("Data too long");
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE FULLTEXT INDEX " + ftIdxName + " ON " + tblName
                    + " (" + colName + ");", ftErrors, true));
            analyzeAllTables();
        } catch (Exception e) {
            return; // FULLTEXT index creation may fail for various reasons
        }

        // Sample some actual text values from the column to use as search terms
        List<String> sampledTexts = sampleColumnValues(tblName, colName, 5);
        String searchTerm;
        if (sampledTexts != null && !sampledTexts.isEmpty()) {
            // Extract a word from a sampled value
            String rawVal = Randomly.fromList(sampledTexts);
            // Strip quotes if present (only if length >= 2 to avoid SIOOBE on single-quote string "'")
            if (rawVal.length() >= 2 && rawVal.startsWith("'") && rawVal.endsWith("'")) {
                rawVal = rawVal.substring(1, rawVal.length() - 1);
            }
            // Get the first word (or short substring) as search term
            String[] words = rawVal.split("\\s+");
            if (words.length > 0 && !words[0].isEmpty()) {
                searchTerm = words[0].replaceAll("[^a-zA-Z0-9]", "");
                if (searchTerm.isEmpty()) {
                    searchTerm = "test";
                }
            } else {
                searchTerm = "test";
            }
        } else {
            searchTerm = Randomly.fromOptions("test", "hello", "world", "data", "index");
        }
        Ensure searchTerm length >= innodb_ft_min_token_size (default 3).
        // Shorter terms are silently ignored by FULLTEXT search → both queries return
        // empty set → comparison passes but test is useless.
        if (searchTerm.length() < 3) {
            searchTerm = searchTerm + "test"; // Pad to ensure >= 3 chars
        }

        // Generate MATCH ... AGAINST query variants
        String matchExpr = "MATCH(" + colName + ") AGAINST('" + searchTerm + "'";
        String searchMode = Randomly.fromOptions(
                "' " + searchTerm + " '",
                "'+" + searchTerm + "'",
                "'" + searchTerm + "*'",
                "'" + searchTerm + "'",
                "''"  // empty search — tests edge case
        );
        // Fix: use proper MATCH AGAINST syntax
        int queryVariant = Randomly.fromOptions(0, 1, 2, 3, 4);
        String queryString;
        String againstMode;
        switch (queryVariant) {
        case 0:
            // NATURAL LANGUAGE MODE (default)
            againstMode = "";
            queryString = "SELECT * FROM " + tblName
                    + " WHERE MATCH(" + colName + ") AGAINST('" + searchTerm + "');";
            break;
        case 1:
            // BOOLEAN MODE with +operator
            againstMode = " IN BOOLEAN MODE";
            queryString = "SELECT * FROM " + tblName
                    + " WHERE MATCH(" + colName + ") AGAINST('+" + searchTerm + "' IN BOOLEAN MODE);";
            break;
        case 2:
            // NATURAL LANGUAGE with COUNT
            againstMode = "";
            queryString = "SELECT COUNT(*) FROM " + tblName
                    + " WHERE MATCH(" + colName + ") AGAINST('" + searchTerm + "');";
            break;
        case 3:
            // WITH QUERY EXPANSION
            againstMode = " WITH QUERY EXPANSION";
            queryString = "SELECT * FROM " + tblName
                    + " WHERE MATCH(" + colName + ") AGAINST('" + searchTerm + "' WITH QUERY EXPANSION);";
            break;
        default:
            // BOOLEAN MODE with wildcard
            againstMode = " IN BOOLEAN MODE";
            queryString = "SELECT * FROM " + tblName
                    + " WHERE MATCH(" + colName + ") AGAINST('" + searchTerm + "*' IN BOOLEAN MODE);";
            break;
        }

        lastQueryString = "[FULLTEXT_IDX] " + queryString;
        log(queryString);

        // Plan A: Default (may or may not use FULLTEXT index)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: FORCE INDEX (force FULLTEXT index scan)
        String forceQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " FORCE INDEX(" + ftIdxName + ")");

        List<String> r2 = executeQuery(forceQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_FULLTEXT_IDX");
        if (lastCompareFiltered) countStarFallback(queryString, forceQuery, "POLARDB_FULLTEXT_IDX");
    }

    // ==================== Mode 25: ICP (Index Condition Pushdown) Consistency ====================

    // ICP correctness: storage engine evaluates WHERE during index scan; type conversion or charset differences
    // between engine and server layers can cause ICP-on vs ICP-off results to diverge.
    private void checkICPConsistency() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        List<MySQLIndex> indexes = table.getIndexes();

        // Create an index if none exist
        if (indexes.isEmpty()) {
            try {
                MySQLIndexGenerator.create(globalState);
                analyzeTable(table.getName());
                indexes = table.getIndexes();
            } catch (Exception e) { return; }
        }
        if (indexes.isEmpty()) return;

        MySQLIndex idx = Randomly.fromList(indexes);
        List<String> idxColNames = idx.getColumnNames();
        if (idxColNames == null || idxColNames.isEmpty()) return;

        // Resolve index columns
        List<MySQLColumn> idxCols = new ArrayList<>();
        for (String colName : idxColNames) {
            for (MySQLColumn col : table.getColumns()) {
                if (col.getName().equals(colName)) {
                    idxCols.add(col);
                    break;
                }
            }
        }
        if (idxCols.isEmpty()) return;

        String tblName = table.getName();
        String idxName = idx.getIndexName();

        // Find non-index columns for the ICP pushdown condition
        List<MySQLColumn> nonIdxCols = new ArrayList<>();
        for (MySQLColumn col : table.getColumns()) {
            if (!idxCols.contains(col)) {
                nonIdxCols.add(col);
            }
        }
        // ICP needs at least one non-index column for pushdown conditions
        // but we can also test with index-only conditions (covering index + ICP)
        // when there are no non-index columns

        // Build WHERE: index column condition (triggers index range scan)
        MySQLColumn idxCol = idxCols.get(0);
        String idxVal = generateDataAwareValueForType(tblName, idxCol);
        String idxOp = Randomly.fromOptions(">", ">=", "<", "<=", "=");
        StringBuilder whereSb = new StringBuilder();
        whereSb.append(idxCol.getName()).append(" ").append(idxOp).append(" ").append(idxVal);

        // Generate complex ICP pushdown condition
        // ICP bugs occur when storage engine and server layer evaluate conditions differently.
        // Key triggers: LIKE patterns, REGEXP, CAST, nested functions, string operations,
        // implicit type conversion, character set handling, CASE WHEN.
        String icpCondition = generateICPPushdownCondition(tblName, table.getColumns(), nonIdxCols, idxCols);
        if (icpCondition != null) {
            whereSb.append(" AND ").append(icpCondition);
        }

        // Use COUNT(*) for deterministic comparison — completely avoids ORDER BY/LIMIT issues
        String baseQuery = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                + " WHERE " + whereSb + ";";

        lastQueryString = "[ICP_TEST] " + baseQuery;
        log(baseQuery);

        // Plan A: ICP enabled (default)
        List<String> r1 = executeQuery(baseQuery);
        if (r1 == null) return;

        // Plan B: ICP disabled — conditions evaluated only in server layer
        boolean success = safeSetSwitch("index_condition_pushdown=off");
        List<String> r2 = null;
        if (success) {
            try {
                r2 = executeQuery(baseQuery);
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        // COUNT(*) comparison — no false positives from ORDER BY/LIMIT
        compareResultsSorted(r1, r2, baseQuery, "POLARDB_ICP");
    }

    // Must reference non-leading index cols so optimizer uses them as ICP rather than index range.
    // ICP bugs surface with LIKE, REGEXP, CAST, charset functions — engine evaluates differently from server.
    private String generateICPPushdownCondition(String tblName, List<MySQLColumn> allCols,
            List<MySQLColumn> nonIdxCols, List<MySQLColumn> idxCols) {
        if (nonIdxCols.isEmpty() && idxCols.size() <= 1) return null;

        // Prefer non-index columns for ICP (80%), but also test with secondary index columns (20%)
        MySQLColumn icpCol;
        if (!nonIdxCols.isEmpty() && Randomly.getBoolean()) {
            icpCol = Randomly.fromList(nonIdxCols);
        } else if (idxCols.size() > 1) {
            // Use a non-leading index column — still gets ICP pushdown
            icpCol = idxCols.get(1);
        } else if (!nonIdxCols.isEmpty()) {
            icpCol = Randomly.fromList(nonIdxCols);
        } else {
            return null;
        }

        String colName = icpCol.getName();
        String colType = icpCol.getType().toString().toUpperCase();
        boolean isString = colType.contains("CHAR") || colType.contains("TEXT") || colType.contains("VARCHAR");
        boolean isInt = colType.contains("INT");
        boolean isFloat = colType.contains("FLOAT") || colType.contains("DOUBLE") || colType.contains("DECIMAL");

        // Sample a real value from the column for data-aware conditions
        String sampledVal = generateDataAwareValueForType(tblName, icpCol);

        // Choose a complex ICP-triggering condition variant
        // Weight towards string operations (most ICP bugs are charset-related)
        int variant;
        if (isString) {
            variant = Randomly.fromOptions(0, 1, 2, 3, 4, 5, 6, 7, 8);
        } else if (isInt) {
            variant = Randomly.fromOptions(9, 10, 11, 12, 13, 14);
        } else if (isFloat) {
            variant = Randomly.fromOptions(9, 10, 11, 15);
        } else {
            variant = Randomly.fromOptions(0, 9);
        }

        switch (variant) {
        // ===== String column ICP conditions =====
        case 0: {
            // LIKE with wildcard — tests pattern matching in storage engine
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            String pattern;
            if (sampled != null && !sampled.isEmpty()) {
                String raw = Randomly.fromList(sampled).replace("'", "");
                if (raw.isEmpty()) {
                    pattern = "a";
                } else {
                    int prefixLen = Math.min(raw.length(), 3);
                    pattern = raw.substring(0, prefixLen);
                }
            } else {
                pattern = "a";
            }
            return colName + " LIKE '" + pattern.replace("'", "''") + "%'";
        }
        case 1: {
            // LIKE with both-side wildcards — harder for storage engine to evaluate correctly
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            String substring;
            if (sampled != null && !sampled.isEmpty()) {
                String raw = Randomly.fromList(sampled).replace("'", "");
                if (raw.isEmpty() || raw.length() < 2) {
                    substring = "a";
                } else {
                    int start = Math.min(1, raw.length() - 1);
                    int end = Math.min(start + 2, raw.length());
                    substring = raw.substring(start, end);
                }
            } else {
                substring = "a";
            }
            return colName + " LIKE '%" + substring.replace("'", "''") + "%'";
        }
        case 2: {
            // UPPER/LOWER comparison — tests charset handling in storage engine
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            String target;
            if (sampled != null && !sampled.isEmpty()) {
                target = Randomly.fromList(sampled).replace("'", "").toUpperCase();
            } else {
                target = "A";
            }
            return "UPPER(" + colName + ") = '" + target.replace("'", "''") + "'";
        }
        case 3: {
            // TRIM + comparison — tests string function pushdown
            return "TRIM(" + colName + ") IS NOT NULL";
        }
        case 4: {
            // LENGTH comparison — tests byte-length vs char-length in storage engine
            // (multi-byte charset columns can have different LENGTH results)
            return "LENGTH(" + colName + ") > 0";
        }
        case 5: {
            // CHAR_LENGTH vs LENGTH — exposes multi-byte charset bugs
            return "CHAR_LENGTH(" + colName + ") = LENGTH(" + colName + ")";
        }
        case 6: {
            // CONCAT with constant — tests string function evaluation
            return "CONCAT(" + colName + ", '') IS NOT NULL";
        }
        case 7: {
            // SUBSTRING comparison — tests offset handling in storage engine
            return "SUBSTRING(" + colName + ", 1, 1) IS NOT NULL";
        }
        case 8: {
            // COALESCE on string — tests NULL handling in ICP
            return "COALESCE(" + colName + ", 'x') = 'x' OR " + colName + " IS NOT NULL";
        }

        // ===== Numeric column ICP conditions =====
        case 9: {
            // CAST type conversion — tests INT vs SIGNED/UNSIGNED handling
            return "CAST(" + colName + " AS SIGNED) >= 0";
        }
        case 10: {
            // ABS comparison — tests function pushdown
            return "ABS(" + colName + ") < 2147483647";
        }
        case 11: {
            // Arithmetic expression — tests operator evaluation in ICP
            return "(" + colName + " + 0) >= 0";
        }
        case 12: {
            // MOD operation — tests division handling
            return "MOD(" + colName + ", 2) = 0";
        }
        case 13: {
            // Comparison with computed value — tests expression evaluation
            return colName + " >= " + sampledVal + " - 1";
        }
        case 14: {
            // Nested CAST: CAST(col AS UNSIGNED) — tests unsigned conversion in storage engine
            return "CAST(" + colName + " AS UNSIGNED) < 18446744073709551615";
        }
        case 15: {
            // ROUND on float — tests floating-point function pushdown
            return "ROUND(" + colName + ", 2) >= 0";
        }
        default:
            return colName + " IS NOT NULL";
        }
    }

    // ==================== Mode 26: Detailed Optimizer Switch Comparison ====================

    // Tests one specific optimizer switch at a time with data-aware WHERE (unlike mode 5 which randomizes combinations).
    private void checkOptimizerSwitchDetailed() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Create index if needed
        List<MySQLIndex> indexes = table.getIndexes();
        if (indexes.isEmpty()) {
            try {
                MySQLIndexGenerator.create(globalState);
                analyzeTable(tblName);
                indexes = table.getIndexes();
            } catch (Exception e) { return; }
        }
        if (indexes.isEmpty()) return;

        // Use COUNT(*) for deterministic comparison — avoids ORDER BY/LIMIT issues
        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions(">", ">=", "<", "<=", "=");
        String idxName = Randomly.fromList(indexes).getIndexName();
        String query = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                + " WHERE " + colName + " " + op + " " + val + ";";

        lastQueryString = "[OPT_SWITCH_DETAIL] " + query;
        log(query);

        // Plan A: Default settings
        List<String> r1 = executeQuery(query);
        if (r1 == null) return;

        // Plan B: Toggle a specific optimizer switch
        // PolarDB-X compatible subset (removed: engine_condition_pushdown, exists_subquery_materialization, in_to_exists)
        String switchVal = Randomly.fromOptions(
                "mrr=on,mrr_cost_based=off",
                "mrr=off",
                "batched_key_access=off",
                "condition_fanout_filter=off",
                "skip_scan=off",
                "index_condition_pushdown=off",
                "subquery_materialization_cost_based=off",
                "semijoin=off",
                "firstmatch=off",
                "loosescan=off",
                "materialization=off",
                "index_merge_intersection=off",
                "index_merge_union=off",
                "index_merge_sort_union=off");

        boolean success = safeSetSwitch(switchVal);
        List<String> r2 = null;
        if (success) {
            try {
                r2 = executeQuery(query);
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        compareResultsSorted(r1, r2, query, "POLARDB_OPT_SWITCH_DETAIL");
    }

    // ==================== Mode 27: SQL Semantic Equivalence ====================

    // IN vs OR, BETWEEN vs >=AND<=, NOT IN vs AND<>: semantically identical but may use different plans, revealing optimizer bugs.
    private void checkSQLSemanticEquivalence() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Ensure an index exists on this column
        String idxName = "seq_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { }

        // Generate data-aware values
        String val1 = generateDataAwareValueForType(tblName, col);
        String val2 = generateDataAwareValueForType(tblName, col);
        String val3 = generateDataAwareValueForType(tblName, col);

        int variant = Randomly.fromOptions(0, 1, 2, 3, 4);
        String queryA, queryB;
        String modeTag;

        switch (variant) {
        case 0:
            // IN vs OR: SELECT COUNT(*) ... WHERE col IN (v1,v2,v3) vs col=v1 OR col=v2 OR col=v3
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " IN (" + val1 + ", " + val2 + ", " + val3 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " = " + val1 + " OR " + colName + " = " + val2
                    + " OR " + colName + " = " + val3 + ";";
            modeTag = "POLARDB_SEMANTIC_IN_VS_OR";
            break;
        case 1: {
            // BETWEEN vs >= AND <= —ensure ordered range
            double d1, d2;
            try { d1 = Double.parseDouble(val1.replace("'", "")); d2 = Double.parseDouble(val2.replace("'", "")); }
            catch (NumberFormatException e) { d1 = 0; d2 = 0; }
            String lowV = (d1 <= d2) ? val1 : val2;
            String highV = (d1 <= d2) ? val2 : val1;
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " BETWEEN " + lowV + " AND " + highV + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " >= " + lowV + " AND " + colName + " <= " + highV + ";";
            modeTag = "POLARDB_SEMANTIC_BETWEEN";
            break;
        }
        case 2:
            // NOT IN vs AND <>
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " NOT IN (" + val1 + ", " + val2 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " <> " + val1 + " AND " + colName + " <> " + val2 + ";";
            modeTag = "POLARDB_SEMANTIC_NOT_IN";
            break;
        case 3:
            // IN vs UNION ALL — IN processes all values in one index scan,
            // UNION ALL forces separate index scans per value → different execution paths
            // IMPORTANT: val1 and val2 must be different! When they are equal:
            //   IN (v, v) deduplicates → counts each row once
            //   UNION ALL of =v and =v → counts each row twice
            // This semantic mismatch is a false positive, not a real bug.
            if (val1.equals(val2)) {
                // Regenerate val2 until it differs from val1
                for (int attempt = 0; attempt < 5 && val1.equals(val2); attempt++) {
                    val2 = generateDataAwareValueForType(tblName, col);
                }
                if (val1.equals(val2)) return; // Cannot generate distinct values — skip
            }
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " IN (" + val1 + ", " + val2 + ");";
            queryB = "SELECT SUM(cnt) FROM ("
                    + "SELECT COUNT(*) AS cnt FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val1
                    + " UNION ALL "
                    + "SELECT COUNT(*) AS cnt FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val2
                    + ") t;";
            modeTag = "POLARDB_SEMANTIC_IN_VS_UNION";
            break;
        default:
            // EXISTS vs JOIN — semantically equivalent for COUNT(*)
            // requires 2 tables, fallback to NOT IN if only 1 table
            if (schema.getDatabaseTables().size() >= 2) {
                MySQLTable table2 = Randomly.fromList(schema.getDatabaseTables());
                if (!table2.getColumns().isEmpty() && !table2.getName().equals(tblName)) {
                    MySQLColumn col2 = Randomly.fromList(table2.getColumns());
                    String tbl2 = table2.getName();
                    String col2Name = col2.getName();
                    queryA = "SELECT COUNT(*) FROM " + tblName + " t1"
                            + " WHERE EXISTS (SELECT 1 FROM " + tbl2 + " t2 WHERE t1." + colName + " = t2." + col2Name + ");";
                    queryB = "SELECT COUNT(DISTINCT t1." + colName + ") FROM " + tblName + " t1"
                            + " INNER JOIN " + tbl2 + " t2 ON t1." + colName + " = t2." + col2Name + ";";
                    modeTag = "POLARDB_SEMANTIC_EXISTS_VS_JOIN";
                    break;
                }
            }
            // Fallback: BETWEEN variant —ensure ordered range
            double fd1, fd2;
            try { fd1 = Double.parseDouble(val1.replace("'", "")); fd2 = Double.parseDouble(val2.replace("'", "")); }
            catch (NumberFormatException e) { fd1 = 0; fd2 = 0; }
            String floV = (fd1 <= fd2) ? val1 : val2;
            String fhiV = (fd1 <= fd2) ? val2 : val1;
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " BETWEEN " + floV + " AND " + fhiV + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ")"
                    + " WHERE " + colName + " >= " + floV + " AND " + colName + " <= " + fhiV + ";";
            modeTag = "POLARDB_SEMANTIC_BETWEEN";
            break;
        }

        lastQueryString = "[SEMANTIC_EQ] A=" + queryA + " B=" + queryB;
        log(queryA);
        log(queryB);

        List<String> r1 = executeQuery(queryA);
        if (r1 == null) return;
        List<String> r2 = executeQuery(queryB);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryA, modeTag);
    }

    // ==================== Mode 28: Deterministic Index Query (P4) ====================

    private MySQLColumn getPrimaryKeyColumn(MySQLTable table) {
        for (MySQLColumn col : table.getColumns()) {
            if (col.isPrimaryKey()) return col;
        }
        return null;
    }

    // 7 templates: equality/range ORDER BY PK, COUNT(*), LIMIT, BETWEEN, IN, covering-index COUNT(*), composite.
    private String buildDeterministicQuery(MySQLTable table, MySQLIndex targetIdx,
            List<MySQLColumn> idxCols, Map<MySQLColumn, String> sampledVals) {
        String tblName = table.getName();
        String idxName = targetIdx.getIndexName();
        MySQLColumn firstCol = idxCols.get(0);
        String colName = firstCol.getName();
        String val = sampledVals.get(firstCol);
        if (val == null) return null;

        // Get PK column for ORDER BY determinism
        MySQLColumn pkCol = getPrimaryKeyColumn(table);
        String orderCol = (pkCol != null) ? pkCol.getName() : colName;

        Randomly r = globalState.getRandomly();
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String query;
        int variant = r.getInteger(0, 7);
        switch (variant) {
        case 0:
            // Template 1: SELECT * with equality/range, ORDER BY PK
            query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " " + op + " " + val + " ORDER BY " + orderCol + ";";
            break;
        case 1:
            // Template 2: SELECT COUNT(*) with equality/range
            query = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " " + op + " " + val + ";";
            break;
        case 2:
            // Template 3: SELECT * LIMIT with equality/range
            query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " " + op + " " + val + " ORDER BY " + orderCol + " LIMIT 10;";
            break;
        case 3: {
            // Template 4: BETWEEN range scan —guaranteed ordered
            String[] rangeVals = generateOrderedRangeValues(tblName, firstCol);
            if (rangeVals != null) {
                query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " BETWEEN " + rangeVals[0] + " AND " + rangeVals[1] + " ORDER BY " + orderCol + ";";
            } else {
                query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val + " ORDER BY " + orderCol + ";";
            }
            break;
        }
        case 4: {
            // Template 5: IN list (multiple point lookups)
            StringBuilder inList = new StringBuilder();
            for (int j = 0; j < r.getInteger(2, 5); j++) {
                if (j > 0) inList.append(", ");
                inList.append(generateDataAwareValueForType(tblName, firstCol));
            }
            query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IN (" + inList + ") ORDER BY " + orderCol + ";";
            break;
        }
        case 5:
            Template 6: Covering index scan — use COUNT(*) for determinism.
            // Previously used ORDER BY non-unique colName + LIMIT 50, which was always
            // filtered out by compareResultsStrict's non-determinism check → test was useless.
            // COUNT(*) is always deterministic regardless of scan order.
            query = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " " + op + " " + val + ";";
            break;
        case 6: {
            // Template 7: Multi-column composite index conditions (use prefix columns)
            StringBuilder where = new StringBuilder();
            int numCols = Math.min(idxCols.size(), r.getInteger(1, 3));
            for (int i = 0; i < numCols; i++) {
                MySQLColumn ic = idxCols.get(i);
                String icVal = sampledVals.get(ic);
                if (icVal == null) icVal = generateDataAwareValueForType(tblName, ic);
                if (i > 0) where.append(" AND ");
                if (i == 0) {
                    where.append(ic.getName()).append(" = ").append(icVal);
                } else {
                    String icOp = Randomly.fromOptions("=", ">", "<", ">=", "<=");
                    where.append(ic.getName()).append(" ").append(icOp).append(" ").append(icVal);
                }
            }
            query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + where + " ORDER BY " + orderCol + ";";
            break;
        }
        default:
            query = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val + " ORDER BY " + orderCol + ";";
            break;
        }
        return query;
    }

    // Deterministic index query: WHERE uses sampled index column values; FORCE INDEX vs default plan comparison.
    private void checkDeterministicIndexQuery() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        String tblName = table.getName();

        // Ensure at least one non-PK index exists
        List<MySQLIndex> indexes = table.getIndexes();
        boolean hasNonPK = false;
        for (MySQLIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY") && !idx.getIndexName().equals("`PRIMARY`")) {
                hasNonPK = true;
                break;
            }
        }
        if (!hasNonPK) {
            try {
                MySQLIndexGenerator.create(globalState);
                analyzeTable(tblName);
                indexes = table.getIndexes();
                for (MySQLIndex idx : indexes) {
                    if (!idx.getIndexName().equals("PRIMARY") && !idx.getIndexName().equals("`PRIMARY`")) {
                        hasNonPK = true;
                        break;
                    }
                }
            } catch (Exception e) { return; }
        }
        if (!hasNonPK) return;

        // Choose a non-PK index
        List<MySQLIndex> nonPKIndexes = new ArrayList<>();
        for (MySQLIndex idx : indexes) {
            if (!idx.getIndexName().equals("PRIMARY") && !idx.getIndexName().equals("`PRIMARY`")) {
                nonPKIndexes.add(idx);
            }
        }
        MySQLIndex targetIdx = Randomly.fromList(nonPKIndexes);
        List<String> idxColNames = targetIdx.getColumnNames();
        if (idxColNames == null || idxColNames.isEmpty()) return;

        // Resolve index column names to MySQLColumn objects
        List<MySQLColumn> idxCols = new ArrayList<>();
        for (String cn : idxColNames) {
            for (MySQLColumn col : table.getColumns()) {
                if (col.getName().equals(cn)) {
                    idxCols.add(col);
                    break;
                }
            }
        }
        if (idxCols.isEmpty()) return;

        // Sample values from index columns
        Map<MySQLColumn, String> sampledVals = new HashMap<>();
        for (MySQLColumn col : idxCols) {
            String val = generateDataAwareValueForType(tblName, col);
            if (val != null) {
                sampledVals.put(col, val);
            }
        }
        if (sampledVals.isEmpty()) return;

        // Build query A (with specific index forced) using index columns
        String queryA = buildDeterministicQuery(table, targetIdx, idxCols, sampledVals);
        if (queryA == null) return;

        // Build query B (no index hint, default plan)
        String queryB = queryA.replaceAll(" FORCE INDEX\\([^)]+\\)", "");

        // EXPLAIN filter
        List<String> planA = getExplainPlan(queryA);
        List<String> planB = getExplainPlan(queryB);
        if (!plansAreDifferent(planA, planB)) return;

        lastQueryString = "[DET_IDX] A=" + queryA + " B=" + queryB;
        log(queryA);
        log(queryB);

        List<String> r1 = executeQuery(queryA);
        if (r1 == null) return;
        List<String> r2 = executeQuery(queryB);
        if (r2 == null) return;

        // Strict comparison: ORDER BY PK guarantees deterministic order
        compareResultsStrict(r1, r2, queryA, "POLARDB_DET_IDX");
        if (lastCompareFiltered) countStarFallback(queryA, queryB, "POLARDB_DET_IDX");
    }

    // ==================== Mode 29: NULL Index Handling ====================

    // NULL values stored separately in B-tree indexes; FORCE INDEX vs IGNORE INDEX comparison catches scans that miss or miscount NULLs.
    private void checkNullIndexHandling() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MySQLTable table = Randomly.fromList(tables);
        List<MySQLColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        // MySQLColumn doesn't track nullable info in schema — use all columns
        // and let the database handle IS NULL/IS NOT NULL appropriately
        MySQLColumn col = Randomly.fromList(columns);
        String tblName = table.getName();
        String colName = col.getName();

        // Create an index on this column
        String idxName = "null_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) {
            return;
        }

        // Check if the column actually has NULL values
        boolean hasNulls = false;
        try {
            List<String> nullCheck = executeQuery(
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
            whereCond = colName + " IS NULL";
            break;
        case 1:
            whereCond = colName + " IS NOT NULL";
            break;
        case 2:
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                whereCond = colName + " IS NULL OR " + colName + " = " + sampled.get(0);
            } else {
                whereCond = colName + " IS NULL";
            }
            break;
        case 3:
            sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                whereCond = colName + " IS NOT NULL AND " + colName + " >= " + sampled.get(0);
            } else {
                whereCond = colName + " IS NOT NULL";
            }
            break;
        default:
            // COUNT(*) WHERE IS NULL vs IS NOT NULL — compare with forced index
            String countNull = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NULL;";
            String countNotNull = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
            String countNullForce = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IS NULL;";
            String countNotNullForce = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL;";

            lastQueryString = "[NULL_IDX] NULL count check";

            List<String> rNullForce = executeQuery(countNullForce);
            if (rNullForce == null) return;
            List<String> rNullDefault = executeQuery(countNull);
            if (rNullDefault == null) return;
            compareResultsSorted(rNullForce, rNullDefault, countNull, "POLARDB_NULL_IDX_ISNULL");

            List<String> rNotNullForce = executeQuery(countNotNullForce);
            if (rNotNullForce == null) return;
            List<String> rNotNullDefault = executeQuery(countNotNull);
            if (rNotNullDefault == null) return;
            compareResultsSorted(rNotNullForce, rNotNullDefault, countNotNull, "POLARDB_NULL_IDX_ISNOTNULL");
            return;
        }

        // Build queries for comparison
        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";
        String forceQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";
        String ignoreQuery = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";

        lastQueryString = "[NULL_IDX] " + queryString;

        // EXPLAIN filter: skip if plans are identical
        List<String> explainPlan1 = getExplainPlan(forceQuery);
        List<String> explainPlan2 = getExplainPlan(ignoreQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = executeQuery(forceQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "POLARDB_NULL_IDX");
        if (lastCompareFiltered) countStarFallback(forceQuery, ignoreQuery, "POLARDB_NULL_IDX");
    }


// ==================== Mode 30: Functional Index (Expression Index) ====================

    private void checkFunctionalIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        Functional index requires InnoDB (MEMORY/HEAP/MyISAM etc. don't support generated columns)
        if (table.getEngine() != MySQLSchema.MySQLTable.MySQLEngine.INNO_DB) return;
        String tblName = table.getName();
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String colName = col.getName();
        FuncIdxTemplate template = pickFuncIdxTemplate(col);
        if (template == null) return;

        Skip overflow-prone functional index expressions when the column contains extreme values.
        // Expressions like -col on INT can overflow when col = -2147483648 (INT_MIN),
        // col+1 overflows when col = 2147483647 (INT_MAX), col*2 overflows for large values.
        // This prevents "Data truncation: Value is out of range for functional index" errors.
        if (template.needsInt) {
            boolean isBigInt = (col.getType() == MySQLSchema.MySQLDataType.BIGINT);
            String checkCol = colName;
            // Determine safe boundaries based on actual column type
            long minVal, maxVal, halfMax;
            if (isBigInt) {
                // BIGINT range: -9223372036854775808 to 9223372036854775807
                minVal = Long.MIN_VALUE;  // -9223372036854775808
                maxVal = Long.MAX_VALUE;  // 9223372036854775807
                halfMax = 4611686018427387903L; // ~half of BIGINT_MAX
            } else {
                // INT range: -2147483648 to 2147483647
                minVal = Integer.MIN_VALUE; // -2147483648
                maxVal = Integer.MAX_VALUE; // 2147483647
                halfMax = 1073741823L;      // ~half of INT_MAX
            }
            if (template.indexExprFormat.equals("-%s")) {
                // -col overflows when col = MIN (e.g., -(-2147483648) overflows INT)
                List<String> overflowCheck = executeQuery(
                    "SELECT 1 FROM " + tblName + " WHERE " + checkCol + " = " + minVal + " LIMIT 1;");
                if (overflowCheck == null || !overflowCheck.isEmpty()) return; // null=query error, skip for safety
            } else if (template.indexExprFormat.equals("%s + 1")) {
                // col+1 overflows when col >= MAX
                List<String> overflowCheck = executeQuery(
                    "SELECT 1 FROM " + tblName + " WHERE " + checkCol + " >= " + maxVal + " LIMIT 1;");
                if (overflowCheck == null || !overflowCheck.isEmpty()) return;
            } else if (template.indexExprFormat.equals("%s * 2")) {
                // col*2 overflows when |col| > halfMax
                List<String> overflowCheck = executeQuery(
                    "SELECT 1 FROM " + tblName + " WHERE " + checkCol + " > " + halfMax + " OR " + checkCol + " < -" + halfMax + " LIMIT 1;");
                if (overflowCheck == null || !overflowCheck.isEmpty()) return;
            }
        }

        String idxName = "func_idx_" + Math.abs((colName + template.indexExprFormat).hashCode() % 100000);
        String indexExpr = String.format(template.indexExprFormat, colName);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " ((" + indexExpr + "));", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }

        try {
            Wrap test body in try-finally to always drop the functional index afterwards.
            // Without cleanup, expressions like CAST(ABS(c0) AS BIGINT) persist on the table,
            // and subsequent DML (INSERT/UPDATE) with values like -9223372036854775808 trigger
            // "Value is out of range for functional index" — crashing the fuzzer.
            String exprForQuery = String.format(template.whereExprFormat, colName);
            String sampleQuery = "SELECT " + exprForQuery + " FROM " + tblName + " WHERE " + colName + " IS NOT NULL LIMIT 10;";
            List<String> sampledResults = executeQuery(sampleQuery);
            if (sampledResults == null || sampledResults.isEmpty()) return;
            List<String> nonNullSamples = new ArrayList<>();
            for (String s : sampledResults) {
                if (s != null && !s.equalsIgnoreCase("null") && !s.isEmpty()) nonNullSamples.add(s);
            }
            if (nonNullSamples.isEmpty()) return;
            String targetVal = Randomly.fromList(nonNullSamples);
            if (!isNumericString(targetVal)) {
                targetVal = "'" + targetVal.replace("'", "''") + "'";
            }

            String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
            String whereClause = "(" + exprForQuery + ") " + op + " " + targetVal;
            String forceQuery = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereClause + ";";
            String ignoreQuery = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereClause + ";";

            lastQueryString = "[FUNC_IDX] " + forceQuery;
            log(forceQuery);
            List<String> r1 = executeQuery(forceQuery);
            if (r1 == null) return;
            List<String> r2 = executeQuery(ignoreQuery);
            if (r2 == null) return;
            compareResultsSorted(r1, r2, forceQuery, "POLARDB_FUNC_IDX");

            if (Randomly.getBoolean()) {
                String selForce = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereClause + " ORDER BY " + exprForQuery + " LIMIT 50;";
                String selIgnore = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereClause + " ORDER BY " + exprForQuery + " LIMIT 50;";
                List<String> r3 = executeQuery(selForce);
                if (r3 == null) return;
                List<String> r4 = executeQuery(selIgnore);
                if (r4 == null) return;
                compareResultsStrict(r3, r4, selForce, "POLARDB_FUNC_IDX_ORDER");
            }
        } finally {
            Always drop the functional index after testing.
            // Prevents overflow errors on subsequent DML operations.
            try {
                globalState.executeStatement(new SQLQueryAdapter(
                    "DROP INDEX " + idxName + " ON " + tblName + ";", errors, true));
            } catch (Exception ignored) {}
        }
    }

    private static class FuncIdxTemplate {
        final String indexExprFormat;
        final String whereExprFormat;
        final boolean needsInt;
        final boolean needsVarchar;
        FuncIdxTemplate(String i, String w, boolean ni, boolean nv) { indexExprFormat=i; whereExprFormat=w; needsInt=ni; needsVarchar=nv; }
        static final FuncIdxTemplate[] INT_TEMPLATES = {
            new FuncIdxTemplate("%s + 1", "%s + 1", true, false),
            new FuncIdxTemplate("%s * 2", "%s * 2", true, false),
            Use CAST(ABS(%s) AS BIGINT) to avoid Data truncation when ABS(-2147483648) overflows SIGNED INT
            new FuncIdxTemplate("CAST(ABS(%s) AS BIGINT)", "ABS(%s)", true, false),
            new FuncIdxTemplate("MOD(%s, 10)", "MOD(%s, 10)", true, false),
            new FuncIdxTemplate("%s DIV 10", "%s DIV 10", true, false),
            new FuncIdxTemplate("-%s", "-%s", true, false),
            new FuncIdxTemplate("IFNULL(%s, 0)", "IFNULL(%s, 0)", true, false),
        };
        static final FuncIdxTemplate[] VARCHAR_TEMPLATES = {
            new FuncIdxTemplate("UPPER(%s)", "UPPER(%s)", false, true),
            new FuncIdxTemplate("LOWER(%s)", "LOWER(%s)", false, true),
            new FuncIdxTemplate("LEFT(%s, 3)", "LEFT(%s, 3)", false, true),
            new FuncIdxTemplate("LENGTH(%s)", "LENGTH(%s)", false, true),
            new FuncIdxTemplate("CHAR_LENGTH(%s)", "CHAR_LENGTH(%s)", false, true),
            new FuncIdxTemplate("REVERSE(%s)", "REVERSE(%s)", false, true),
            new FuncIdxTemplate("CONCAT(%s, '')", "CONCAT(%s, '')", false, true),
        };
    }

    private FuncIdxTemplate pickFuncIdxTemplate(MySQLColumn col) {
        MySQLSchema.MySQLDataType type = col.getType();
        if (type == MySQLSchema.MySQLDataType.INT || type == MySQLSchema.MySQLDataType.BIGINT)
            return Randomly.fromOptions(FuncIdxTemplate.INT_TEMPLATES);
        else if (type == MySQLSchema.MySQLDataType.VARCHAR)
            return Randomly.fromOptions(FuncIdxTemplate.VARCHAR_TEMPLATES);
        else if (type == MySQLSchema.MySQLDataType.FLOAT || type == MySQLSchema.MySQLDataType.DOUBLE || type == MySQLSchema.MySQLDataType.DECIMAL)
            Use CAST(ABS(%s) AS BIGINT) to avoid Data truncation when ABS(large_float) overflows BIGINT
            return Randomly.fromOptions(new FuncIdxTemplate("CAST(ABS(%s) AS BIGINT)","ABS(%s)",false,false), new FuncIdxTemplate("-%s","-%s",false,false), new FuncIdxTemplate("IFNULL(%s, 0)","IFNULL(%s, 0)",false,false));
        return null;
    }

    private static boolean isNumericString(String s) {
        if (s == null || s.isEmpty()) return false;
        try { Double.parseDouble(s); return true; } catch (NumberFormatException e) { return false; }
    }
// ==================== Mode 31: DML + Index Consistency ====================

    private void checkDMLIndexConsistency() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        List<MySQLIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) return;
        MySQLIndex idx = null;
        for (MySQLIndex candidate : tableIndexes) {
            if (!candidate.getIndexName().equalsIgnoreCase("PRIMARY")) { idx = candidate; break; }
        }
        if (idx == null) idx = Randomly.fromList(tableIndexes);
        String tblName = table.getName();
        String idxName = idx.getIndexName();
        MySQLColumn idxCol = null;
        List<String> idxColNames = idx.getColumnNames();
        if (idxColNames != null && !idxColNames.isEmpty()) {
            for (MySQLColumn c : table.getColumns()) {
                if (c.getName().equalsIgnoreCase(idxColNames.get(0))) { idxCol = c; break; }
            }
        }
        if (idxCol == null) {
            if (table.getColumns().isEmpty()) return;
            idxCol = table.getColumns().get(0);
        }
        String colName = idxCol.getName();

        Skip if index column is a generated column (cannot be used in UPDATE SET)
        if (colName.startsWith("gen_col_")) return;

        String dmlStmt = generateIndexDML(tblName, colName, idxCol);
        lastQueryString = "[DML_IDX] " + dmlStmt;
        log(dmlStmt);
        ExpectedErrors dmlErrors = new ExpectedErrors();
        dmlErrors.add("Duplicate entry"); dmlErrors.add("cannot be null");
        dmlErrors.add("Data truncated"); dmlErrors.add("Out of range");
        dmlErrors.add("doesn't have a default value"); dmlErrors.add("Lock wait timeout");
        dmlErrors.add("Deadlock"); dmlErrors.add("BIGINT value is out of range");
        dmlErrors.add("DOUBLE value is out of range"); dmlErrors.add("Incorrect");
        dmlErrors.add("PXC-"); dmlErrors.add("ERR_TDDL_");
        try { globalState.executeStatement(new SQLQueryAdapter(dmlStmt, dmlErrors, true)); }
        catch (Exception e) { return; }

        String val = generateDataAwareValueForType(tblName, idxCol);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IS NOT NULL");
        String whereCond = op.equals("IS NOT NULL") ? colName + " IS NOT NULL" : colName + " " + op + " " + val;
        String forceQuery = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereCond + ";";
        String ignoreQuery = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereCond + ";";
        List<String> r1 = executeQuery(forceQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQuery);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQuery, "POLARDB_DML_INDEX");

        if (Randomly.getBoolean()) {
            String selF = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 50;";
            String selI = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 50;";
            List<String> r3 = executeQuery(selF);
            if (r3 == null) return;
            List<String> r4 = executeQuery(selI);
            if (r4 == null) return;
            compareResultsStrict(r3, r4, selF, "POLARDB_DML_INDEX_ROWS");
        }
    }

    private String generateIndexDML(String tblName, String colName, MySQLColumn col) {
        String oldVal = generateDataAwareValueForType(tblName, col);
        String newVal = generateDataAwareValueForType(tblName, col);
        int variant = globalState.getRandomly().getInteger(0, 6);
        switch (variant) {
        case 0: return "UPDATE " + tblName + " SET " + colName + " = " + newVal + " WHERE " + colName + " = " + oldVal + " LIMIT 5;";
        case 1: return "DELETE FROM " + tblName + " WHERE " + colName + " = " + oldVal + " LIMIT 3;";
        case 2:
            if (col.getType() == MySQLSchema.MySQLDataType.INT || col.getType() == MySQLSchema.MySQLDataType.BIGINT)
                return "UPDATE " + tblName + " SET " + colName + " = " + colName + " + 1 WHERE " + colName + " > " + oldVal + " LIMIT 10;";
            return "UPDATE " + tblName + " SET " + colName + " = " + newVal + " WHERE " + colName + " = " + oldVal + " LIMIT 5;";
        case 3: return "DELETE FROM " + tblName + " WHERE " + colName + " > " + oldVal + " LIMIT 5;";
        case 4: return "UPDATE " + tblName + " SET " + colName + " = " + newVal + " WHERE " + colName + " > " + oldVal + " LIMIT 20;";
        default: return "DELETE FROM " + tblName + " WHERE " + colName + " = " + oldVal + " LIMIT 1;";
        }
    }

    // ==================== Mode 32: DESC Index Sort Verification ====================

    private void checkDescIndexSort() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        Skip non-InnoDB tables — MyISAM and other engines don't support DESC indexes.
        // MySQL reports: "The storage engine for the table doesn't support descending indexes"
        if (table.getEngine() != MySQLSchema.MySQLTable.MySQLEngine.INNO_DB) return;

        String tblName = table.getName();
        MySQLColumn col = Randomly.fromList(table.getColumns());
        String colName = col.getName();

        String idxName = "desc_idx_" + Math.abs(colName.hashCode() % 100000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + " DESC);", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) {
            idxName = findDescIndexOnTable(table);
            if (idxName == null) return;
        }

        String val = generateDataAwareValueForType(tblName, col);

        // Test 1: ORDER BY col DESC
        String q1F = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " > " + val + " ORDER BY " + colName + " DESC LIMIT 50;";
        String q1I = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " > " + val + " ORDER BY " + colName + " DESC LIMIT 50;";
        lastQueryString = "[DESC_IDX] " + q1F;
        log(q1F);
        List<String> r1 = executeQuery(q1F);
        if (r1 == null) return;
        List<String> r2 = executeQuery(q1I);
        if (r2 == null) return;
        compareResultsStrict(r1, r2, q1F, "POLARDB_DESC_IDX_ORDER");

        // Test 2: ORDER BY col ASC (backward scan)
        String q2F = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " > " + val + " ORDER BY " + colName + " ASC LIMIT 50;";
        String q2I = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " > " + val + " ORDER BY " + colName + " ASC LIMIT 50;";
        List<String> r3 = executeQuery(q2F);
        if (r3 == null) return;
        List<String> r4 = executeQuery(q2I);
        if (r4 == null) return;
        compareResultsStrict(r3, r4, q2F, "POLARDB_DESC_IDX_REVERSE");

        // Test 3: COUNT(*)
        String cntF = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " > " + val + ";";
        String cntI = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " > " + val + ";";
        List<String> r5 = executeQuery(cntF);
        List<String> r6 = executeQuery(cntI);
        if (r5 != null && r6 != null) compareResultsSorted(r5, r6, cntF, "POLARDB_DESC_IDX_COUNT");

        // Test 4: Mixed sort composite index
        if (table.getColumns().size() >= 2) {
            MySQLColumn col2 = null;
            for (MySQLColumn c : table.getColumns()) { if (!c.getName().equals(colName)) { col2 = c; break; } }
            if (col2 != null) {
                String col2Name = col2.getName();
                String mIdx = "mixed_desc_" + Math.abs((colName + col2Name).hashCode() % 100000);
                try {
                    globalState.executeStatement(new SQLQueryAdapter(
                        "CREATE INDEX " + mIdx + " ON " + tblName + " (" + colName + " ASC, " + col2Name + " DESC);", errors, true));
                    analyzeAllTables();
                    String mF = "SELECT * FROM " + tblName + " FORCE INDEX(" + mIdx + ") WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " ASC, " + col2Name + " DESC LIMIT 50;";
                    String mI = "SELECT * FROM " + tblName + " IGNORE INDEX(" + mIdx + ") WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " ASC, " + col2Name + " DESC LIMIT 50;";
                    List<String> rm1 = executeQuery(mF);
                    List<String> rm2 = executeQuery(mI);
                    if (rm1 != null && rm2 != null) compareResultsStrict(rm1, rm2, mF, "POLARDB_MIXED_DESC_IDX");
                } catch (Exception e) { /* may fail */ }
            }
        }
    }

    private String findDescIndexOnTable(MySQLTable table) {
        try {
            String q = "SELECT INDEX_NAME FROM INFORMATION_SCHEMA.STATISTICS WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + table.getName() + "' AND COLLATION = 'D' AND INDEX_NAME != 'PRIMARY' LIMIT 1;";
            List<String> result = executeQuery(q);
            if (result != null && !result.isEmpty()) {
                String name = result.get(0);
                if (name != null && !name.isEmpty() && !name.equalsIgnoreCase("null")) return name;
            }
        } catch (Exception e) { }
        return null;
    }

// ==================== Mode 33: Generated Column + Index ====================

    // VIRTUAL/STORED generated column with index; verifies FORCE vs IGNORE INDEX consistency and that
    // UPDATE on the base column keeps the generated column index consistent.
    private void checkGeneratedColumnIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MySQLTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        String tblName = table.getName();

        Skip non-InnoDB tables — only InnoDB supports generated columns.
        // HEAP/MEMORY, MyISAM, etc. will error with:
        // "'Specified storage engine' is not supported for generated columns."
        if (table.getEngine() != MySQLSchema.MySQLTable.MySQLEngine.INNO_DB) return;

        Skip tables with invisible indexes — ALTER TABLE ADD GENERATED COLUMN
        // triggers a table rebuild, and MySQL rejects with "A primary key index cannot be invisible"
        // if any unique/primary index on the table is invisible.
        if (hasInvisibleIndexes(tblName)) return;

        Filter out AUTO_INCREMENT columns — MySQL rejects generated columns
        // that reference AUTO_INCREMENT columns with:
        // "Generated column 'xxx' cannot refer to auto-increment column."
        Set<String> autoIncCols = getAutoIncrementColumns(tblName);
        List<MySQLColumn> candidateCols = new ArrayList<>();
        for (MySQLColumn c : table.getColumns()) {
            if (!autoIncCols.contains(c.getName().toLowerCase())) {
                candidateCols.add(c);
            }
        }
        if (candidateCols.isEmpty()) return;
        MySQLColumn col1 = candidateCols.get(0);
        String col1Name = col1.getName();
        Use random suffix to avoid "Duplicate column name" on repeated invocations
        String genColName = "gen_col_" + Math.abs(col1Name.hashCode() % 10000) + "_" + Randomly.smallNumber() + "_" + Randomly.smallNumber();
        Check if a column with this name already exists, skip if so
        Set<String> existingColNames = new HashSet<>();
        for (MySQLColumn c : table.getColumns()) {
            existingColNames.add(c.getName().toLowerCase());
        }
        if (existingColNames.contains(genColName.toLowerCase())) return;
        boolean isStored = Randomly.getBoolean();
        String storageType = isStored ? "STORED" : "VIRTUAL";

        // Choose expression based on column type
        String genExpr;
        String genColType;
        if (col1.getType() == MySQLSchema.MySQLDataType.INT || col1.getType() == MySQLSchema.MySQLDataType.BIGINT) {
            Pick expression first, then check for overflow-prone values in existing data.
            // Generated columns with expressions like col*2, ABS(col), IFNULL(col,0)+1 can cause
            // "Data truncation: Out of range value for column" when existing data has extreme values.
            boolean isBigInt = (col1.getType() == MySQLSchema.MySQLDataType.BIGINT);
            long minVal = isBigInt ? Long.MIN_VALUE : Integer.MIN_VALUE;
            long maxVal = isBigInt ? Long.MAX_VALUE : Integer.MAX_VALUE;
            long halfMax = isBigInt ? 4611686018427387903L : 1073741823L;

            genExpr = Randomly.fromOptions(
                col1Name + " * 2",
                "ABS(" + col1Name + ")",
                col1Name + " MOD 100",
                "IFNULL(" + col1Name + ", 0) + 1"
            );

            Skip overflow-prone generated column expressions when the column contains extreme values.
            // ALTER TABLE ADD COLUMN ... GENERATED ALWAYS AS (expr) evaluates expr for all existing rows,
            // so even a single row with an extreme value will cause Data truncation.
            if (genExpr.equals(col1Name + " * 2")) {
                // col*2 overflows when |col| > halfMax
                List<String> overflowCheck = executeQuery(
                    "SELECT 1 FROM " + tblName + " WHERE " + col1Name + " > " + halfMax
                    + " OR " + col1Name + " < -" + halfMax + " LIMIT 1;");
                if (overflowCheck == null || !overflowCheck.isEmpty()) return;
            } else if (genExpr.equals("ABS(" + col1Name + ")")) {
                // ABS(col) overflows when col = MIN (e.g., ABS(-2147483648) overflows INT)
                List<String> overflowCheck = executeQuery(
                    "SELECT 1 FROM " + tblName + " WHERE " + col1Name + " = " + minVal + " LIMIT 1;");
                if (overflowCheck == null || !overflowCheck.isEmpty()) return;
            } else if (genExpr.equals("IFNULL(" + col1Name + ", 0) + 1")) {
                // IFNULL(col,0)+1 overflows when col = MAX
                List<String> overflowCheck = executeQuery(
                    "SELECT 1 FROM " + tblName + " WHERE " + col1Name + " >= " + maxVal + " LIMIT 1;");
                if (overflowCheck == null || !overflowCheck.isEmpty()) return;
            }
            // col MOD 100 is always safe (result is always in [-99, 99])

            genColType = "BIGINT";
        } else if (col1.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
            genExpr = Randomly.fromOptions(
                "UPPER(" + col1Name + ")",
                "LEFT(" + col1Name + ", 5)",
                "LENGTH(" + col1Name + ")"
            );
            genColType = genExpr.startsWith("LENGTH") ? "INT" : "VARCHAR(255)";
        } else {
            // [FIX v2] For DOUBLE/FLOAT columns, use DOUBLE as the generated column type
            // instead of BIGINT. Previous fix used BIGINT + overflow check, but DOUBLE-to-BIGINT
            // comparison precision issues in MySQL caused the overflow check to miss extreme values
            // like 1.7976931348623157E308, resulting in "Data truncation: Out of range value".
            // Using DOUBLE genColType preserves the original range and avoids overflow entirely.
            genExpr = "IFNULL(" + col1Name + ", 0)";
            genColType = "DOUBLE";
        }

        // Step 1: Add Generated Column
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "ALTER TABLE " + tblName + " ADD COLUMN " + genColName
                + " " + genColType + " GENERATED ALWAYS AS (" + genExpr + ") " + storageType + ";",
                errors, true));
        } catch (Exception e) { return; }

        // Step 2: Create index on generated column
        String idxName = "gen_idx_" + Math.abs(genColName.hashCode() % 100000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + genColName + ");", errors, true));
            analyzeAllTables();
        } catch (Exception e) { return; }

        // Step 3: Verify index correctness
        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + genColName + " IS NOT NULL;";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + genColName + " IS NOT NULL;";

        lastQueryString = "[GEN_COL_IDX] " + forceQ;
        log(forceQ);

        List<String> r1 = executeQuery(forceQ);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQ);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQ, "POLARDB_GEN_COL_IDX");

        // Step 4: UPDATE base column, then re-verify generated column index
        String newVal = generateDataAwareValueForType(tblName, col1);
        String oldVal = generateDataAwareValueForType(tblName, col1);
        ExpectedErrors updErrors = new ExpectedErrors();
        updErrors.add("Duplicate entry"); updErrors.add("cannot be null");
        updErrors.add("Data truncated"); updErrors.add("Incorrect");
        updErrors.add("Out of range"); updErrors.add("BIGINT value is out of range");
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "UPDATE " + tblName + " SET " + col1Name + " = " + newVal
                + " WHERE " + col1Name + " = " + oldVal + " LIMIT 5;", updErrors, true));
        } catch (Exception e) { return; }

        // Re-verify after UPDATE
        List<String> r3 = executeQuery(forceQ);
        if (r3 == null) return;
        List<String> r4 = executeQuery(ignoreQ);
        if (r4 == null) return;
        compareResultsSorted(r3, r4, forceQ, "POLARDB_GEN_COL_IDX_AFTER_UPDATE");
    }
    // ALTER TABLE triggers a rebuild; MySQL rejects rebuild if any primary/unique index is invisible.
    private boolean hasInvisibleIndexes(String tableName) {
        try {
            String query = "SELECT INDEX_NAME FROM information_schema.STATISTICS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName
                    + "' AND INDEX_NAME != 'PRIMARY' LIMIT 1;";
            List<String> allIndexes = executeQuery(query);
            if (allIndexes == null || allIndexes.isEmpty()) return false;

            // Check visibility via SHOW INDEX which includes the Visible column
            String visQuery = "SHOW INDEX FROM " + tableName + " WHERE Visible = 'NO';";
            List<String> invisible = executeQuery(visQuery);
            return invisible != null && !invisible.isEmpty();
        } catch (Exception e) {
            // Best-effort: if we can't determine, conservatively return false
            return false;
        }
    }

    // MySQL rejects generated columns referencing AUTO_INCREMENT cols: "cannot refer to auto-increment column."
    private Set<String> getAutoIncrementColumns(String tableName) {
        Set<String> autoIncCols = new HashSet<>();
        try {
            String query = "SELECT COLUMN_NAME FROM information_schema.COLUMNS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName
                    + "' AND EXTRA LIKE '%auto_increment%';";
            List<String> result = executeQuery(query);
            if (result != null) {
                for (String row : result) {
                    if (row != null && !row.isEmpty()) {
                        // Handle multi-column rows — take first column
                        String colName = row.split(java.util.regex.Pattern.quote(COLUMN_DELIMITER))[0].trim();
                        autoIncCols.add(colName.toLowerCase());
                    }
                }
            }
        } catch (Exception e) {
            // Best-effort
        }
        return autoIncCols;
    }

// ==================== Mode 34: Collation + Index ====================

    // Creates a functional index with COLLATE (ci/bin/unicode) and compares FORCE vs IGNORE INDEX results.
    private void checkCollationIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with VARCHAR column
        MySQLTable table = null;
        MySQLColumn varcharCol = null;
        for (int attempt = 0; attempt < 5; attempt++) {
            MySQLTable t = Randomly.fromList(tables);
            for (MySQLColumn c : t.getColumns()) {
                if (c.getType() == MySQLSchema.MySQLDataType.VARCHAR) {
                    table = t; varcharCol = c; break;
                }
            }
            if (table != null) break;
        }
        if (table == null || varcharCol == null) return;

        String tblName = table.getName();
        String colName = varcharCol.getName();

        String collation = Randomly.fromOptions(
            "utf8mb4_general_ci", "utf8mb4_bin", "utf8mb4_unicode_ci"
        );
        String idxName = "collation_idx_" + Math.abs((colName + collation).hashCode() % 100000);

        // Create functional index with COLLATE
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName
                + " ((" + colName + " COLLATE " + collation + "));", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }

        // Sample values
        List<String> sampled = sampleColumnValues(tblName, colName, 5);
        if (sampled == null || sampled.isEmpty()) return;
        String val = Randomly.fromList(sampled);
        if (val == null || val.isEmpty() || val.equalsIgnoreCase("null")) return;
        // Ensure proper quoting
        if (!val.startsWith("'")) {
            val = "'" + val.replace("'", "''") + "'";
        }

        String whereClause = "(" + colName + " COLLATE " + collation + ") = " + val;

        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereClause + ";";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereClause + ";";

        lastQueryString = "[COLLATION_IDX] " + forceQ;
        log(forceQ);

        List<String> r1 = executeQuery(forceQ);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQ);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQ, "POLARDB_COLLATION_IDX");

        // Additional range comparison test
        if (Randomly.getBoolean()) {
            String rangeWhere = "(" + colName + " COLLATE " + collation + ") > " + val;
            String rForce = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + rangeWhere + ";";
            String rIgnore = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + rangeWhere + ";";
            List<String> r3 = executeQuery(rForce);
            if (r3 == null) return;
            List<String> r4 = executeQuery(rIgnore);
            if (r4 == null) return;
            compareResultsSorted(r3, r4, rForce, "POLARDB_COLLATION_IDX_RANGE");
        }
    }

    // ==================== Mode 35: Type Mismatch + Index ====================

    // Implicit type conversion (VARCHAR col = INT literal, INT col = '123abc') can prevent index use;
    // FORCE vs IGNORE INDEX must agree even when conversion truncates the lookup value.
    private void checkTypeMismatchIndex() throws Exception {
        MySQLSchema schema = globalState.getSchema();
        List<MySQLTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with VARCHAR column
        MySQLTable table = null;
        MySQLColumn varcharCol = null;
        MySQLColumn intCol = null;
        for (int attempt = 0; attempt < 5; attempt++) {
            MySQLTable t = Randomly.fromList(tables);
            for (MySQLColumn c : t.getColumns()) {
                if (c.getType() == MySQLSchema.MySQLDataType.VARCHAR && varcharCol == null) varcharCol = c;
                if ((c.getType() == MySQLSchema.MySQLDataType.INT || c.getType() == MySQLSchema.MySQLDataType.BIGINT) && intCol == null) intCol = c;
            }
            if (varcharCol != null) { table = t; break; }
            varcharCol = null; intCol = null;
        }
        if (table == null || varcharCol == null) return;

        String tblName = table.getName();
        String colName = varcharCol.getName();

        // Ensure index exists on VARCHAR column
        String idxName = "typemis_idx_" + Math.abs(colName.hashCode() % 100000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { /* may already exist */ }

        // Test 1: VARCHAR column compared with INT literal (implicit conversion)
        int intVal = globalState.getRandomly().getInteger(0, 1000);
        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + intVal + ";";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " = " + intVal + ";";

        lastQueryString = "[TYPE_MISMATCH] " + forceQ;
        log(forceQ);

        List<String> r1 = executeQuery(forceQ);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQ);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQ, "POLARDB_TYPE_MISMATCH_IDX");

        // Test 2: INT column compared with string (if available)
        if (intCol != null) {
            String intColName = intCol.getName();
            String intIdxName = "typemis_int_" + Math.abs(intColName.hashCode() % 100000);
            try {
                globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + intIdxName + " ON " + tblName + " (" + intColName + ");", errors, true));
            } catch (Exception e) { /* may exist */ }

            // WHERE int_col = '123abc' - MySQL truncates string to number
            String strVal = "'" + intVal + "abc'";
            String intForce = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + intIdxName + ") WHERE " + intColName + " = " + strVal + ";";
            String intIgnore = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + intIdxName + ") WHERE " + intColName + " = " + strVal + ";";

            List<String> r5 = executeQuery(intForce);
            if (r5 == null) return;
            List<String> r6 = executeQuery(intIgnore);
            if (r6 == null) return;
            compareResultsSorted(r5, r6, intForce, "POLARDB_TYPE_MISMATCH_INT");
        }
    }

    public String getLastQueryString() {
        return lastQueryString;
    }

    // Drops non-PRIMARY indexes when a table approaches MySQL's limit of 64 indexes.
    private void pruneExcessIndexes() {
        try {
            globalState.updateSchema();
        } catch (Exception e) {
            return;
        }
        MySQLSchema schema = globalState.getSchema();
        ExpectedErrors dropErrors = new ExpectedErrors();
        dropErrors.add("Can't DROP");
        dropErrors.add("check that column/key exists");

        for (MySQLTable table : schema.getDatabaseTables()) {
            List<MySQLIndex> indexes = table.getIndexes();
            if (indexes.size() < INDEX_PRUNE_THRESHOLD) continue;

            List<MySQLIndex> nonPrimaryIndexes = new ArrayList<>();
            for (MySQLIndex idx : indexes) {
                String name = idx.getIndexName();
                if (!name.equals("PRIMARY") && !name.equals("`PRIMARY`")) {
                    nonPrimaryIndexes.add(idx);
                }
            }

            Collections.shuffle(nonPrimaryIndexes);

            String tblName = table.getName();
            int toDrop = indexes.size() - INDEX_PRUNE_TARGET;
            for (int i = 0; i < toDrop && i < nonPrimaryIndexes.size(); i++) {
                MySQLIndex idxToDrop = nonPrimaryIndexes.get(i);
                try {
                    globalState.executeStatement(new SQLQueryAdapter(
                            "DROP INDEX " + idxToDrop.getIndexName() + " ON " + tblName + ";",
                            dropErrors, true));
                } catch (Exception e) { }
            }

            try {
                globalState.executeStatement(new SQLQueryAdapter(
                        "ANALYZE TABLE " + tblName + ";", true));
            } catch (Exception e) { }
        }
    }
}
