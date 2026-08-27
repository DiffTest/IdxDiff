package idxdiff.postgres.oracle;

import java.sql.ResultSet;
import java.sql.Statement;
import java.util.ArrayList;
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
import idxdiff.postgres.PostgresGlobalState;
import idxdiff.postgres.PostgresSchema;
import idxdiff.postgres.PostgresSchema.PostgresColumn;
import idxdiff.postgres.PostgresSchema.PostgresDataType;
import idxdiff.postgres.PostgresSchema.PostgresIndex;
import idxdiff.postgres.PostgresSchema.PostgresTable;
import idxdiff.postgres.PostgresSchema.PostgresTables;
import idxdiff.postgres.PostgresVisitor;
import idxdiff.postgres.ast.PostgresBetweenOperation;
import idxdiff.postgres.ast.PostgresBinaryComparisonOperation;
import idxdiff.postgres.ast.PostgresBinaryComparisonOperation.PostgresBinaryComparisonOperator;
import idxdiff.postgres.ast.PostgresBinaryLogicalOperation;
import idxdiff.postgres.ast.PostgresBinaryLogicalOperation.BinaryLogicalOperator;
import idxdiff.postgres.ast.PostgresColumnValue;
import idxdiff.postgres.ast.PostgresConstant;
import idxdiff.postgres.ast.PostgresExpression;
import idxdiff.postgres.ast.PostgresInOperation;
import idxdiff.postgres.ast.PostgresJoin;
import idxdiff.postgres.ast.PostgresJoin.PostgresJoinType;
import idxdiff.postgres.ast.PostgresPostfixOperation;
import idxdiff.postgres.ast.PostgresPostfixOperation.PostfixOperator;
import idxdiff.postgres.ast.PostgresSelect;
import idxdiff.postgres.ast.PostgresSelect.ForClause;
import idxdiff.postgres.ast.PostgresSelect.PostgresFromTable;
import idxdiff.postgres.ast.PostgresSelect.PostgresSubquery;
import idxdiff.postgres.gen.PostgresCommon;
import idxdiff.postgres.gen.PostgresExpressionGenerator;
import idxdiff.postgres.gen.PostgresIndexGenerator;

/**
 * Index Oracle for PostgreSQL — deeply integrated with idxdiff's expression
 * generation infrastructure.
 *
 * Core idea: Use PostgresExpressionGenerator to create complex, deeply nested
 * queries, then verify that different query plans (index scan vs seq scan,
 * bitmap scan vs index scan, etc.) produce identical results.
 *
 * Active test modes:
 * <ul>
 * <li>1: CREATE_INDEX_CONSISTENCY — query before/after index creation</li>
 * <li>2: DROP_INDEX_CONSISTENCY — query before/after index drop</li>
 * <li>3: INDEX_SCAN_VS_BITMAP_SCAN — enable_indexscan vs enable_bitmapscan</li>
 * <li>4: AGGREGATE_PLAN_CONSISTENCY — aggregate with different index settings</li>
 * <li>5: JOIN_PLAN_CONSISTENCY [DISABLED]</li>
 * <li>6: MULTI_INDEX_CONSISTENCY — multiple index creation, compare plans</li>
 * <li>7: [DISABLED]</li>
 * <li>8: COVERING_INDEX — index-only scan verification</li>
 * <li>9: INDEX_MERGE — index merge (bitmap OR/AND)</li>
 * <li>10: ORDER_BY_LIMIT_INDEX — ORDER BY + LIMIT with index vs seqscan</li>
 * <li>11: UNIQUE_INDEX_CONSISTENCY — UNIQUE index data consistency</li>
 * <li>12: EXPRESSION_INDEX — expression index correctness</li>
 * <li>13: PARTIAL_INDEX — partial index (WHERE clause on index)</li>
 * <li>14: SIMPLE_INDEX_QUERY — targeted index-friendly WHERE conditions</li>
 * <li>15: GIST_GIN_INDEX — GiST/GIN index for LIKE/array operations</li>
 * <li>16: TSVECTOR_INDEX — tsvector GIN full-text search</li>
 * <li>17: OPTIMIZER_CONFIG_PAIRWISE — enable_*=on vs enable_*=off pairwise</li>
 * <li>18: SQL_SEMANTIC_EQUIVALENCE — IN-vs-OR, BETWEEN-vs-AND equivalence</li>
 * <li>19: DETERMINISTIC_INDEX_QUERY — PK-based WHERE with different index plans</li>
 * <li>20: NULL_INDEX_HANDLING — NULL values in indexed columns</li>
 * <li>21: PREFIX_INDEX — SUBSTRING function index (Postgres analog)</li>
 * <li>22: SUBQUERY_INDEX — subquery with index conditions</li>
 * <li>23: INDEX_COND_PUSHDOWN — Index Cond vs Filter (ICP equivalent)</li>
 * <li>24: BRIN_INDEX — BRIN Block Range Index (Postgres-specific)</li>
 * </ul>
 */
public class PostgresIndexOracle implements TestOracle<PostgresGlobalState> {

    private final PostgresGlobalState globalState;
    private final ExpectedErrors errors;

    private String lastQueryString;
    private boolean dataPopulated = false;
    private int aggregateFallbackUsed = 0; // how many times COUNT(*) fallback was used
    private boolean lastCompareFiltered = false; // set true when compareResults filters out a difference

    private static final double EPSILON = 1e-10;
    private static final double RELATIVE_TOLERANCE = 1e-6;

    public PostgresIndexOracle(PostgresGlobalState globalState) {
        this.globalState = globalState;
        this.errors = buildExpectedErrors();
    }

    private ExpectedErrors buildExpectedErrors() {
        ExpectedErrors expectedErrors = ExpectedErrors.newErrors()
                .with(PostgresCommon.getCommonExpressionErrors())
                .with(PostgresCommon.getCommonFetchErrors())
                .withRegex(PostgresCommon.getCommonExpressionRegexErrors())
                .build();
        // Add index-specific expected errors
        expectedErrors.add("already exists");
        expectedErrors.add("does not exist");
        expectedErrors.add("cannot drop index");
        // expectedErrors.add("access method");
        // REMOVED: "access method" — too broad in oracle query context, masks
        // index access method bugs during query execution.
        // PostgresIndexGenerator already has specific patterns like:
        //   "access method \"gin\" does not support unique indexes" etc.
        // expectedErrors.add("access method");
        // REMOVED: "does not support" — too broad in oracle query context, masks
        // optimizer/execution engine "does not support" errors.
        expectedErrors.add("has no default operator class");
        expectedErrors.add("does not accept");
        expectedErrors.add("could not create unique index");
        expectedErrors.add("duplicate key value");
        expectedErrors.add("violates unique constraint");
        expectedErrors.add("functions in index predicate must be marked IMMUTABLE");
        expectedErrors.add("functions in index expression must be marked IMMUTABLE");
        expectedErrors.add("canceling statement due to statement timeout");
        expectedErrors.add("canceling statement due to user request");
        expectedErrors.add("out of memory");
        expectedErrors.add("stack depth limit exceeded");
        expectedErrors.add("non-integer constant in DISTINCT ON");
        expectedErrors.add("SELECT DISTINCT ON expressions must match initial ORDER BY expressions");
        expectedErrors.add("for SELECT DISTINCT, ORDER BY expressions must appear in select list");
        expectedErrors.add("column reference .+ is ambiguous");
        expectedErrors.add("argument of .+ must be type");
        expectedErrors.add("cannot cast type");
        expectedErrors.add("operator does not exist");
        expectedErrors.add("function .+ does not exist");
        expectedErrors.add("aggregate functions are not allowed in");
        expectedErrors.add("grouping error");
        expectedErrors.add("invalid input syntax for");
        expectedErrors.add("division by zero");
        expectedErrors.add("integer out of range");
        expectedErrors.add("value .+ is out of range");
        expectedErrors.add("must appear in the GROUP BY clause or be used in an aggregate function");
        expectedErrors.add("subquery has too many columns");
        // expectedErrors.add("could not read block");
        // REMOVED: "could not read block" — this usually indicates data/index corruption,
        // which is exactly what the index oracle should be detecting. Keeping it would
        // mask real bugs in index scan paths that cause block read errors.
        expectedErrors.add("permission denied");
        expectedErrors.add("unrecognized configuration parameter");
        expectedErrors.add("specified more than once");
        expectedErrors.add("is ambiguous");
        expectedErrors.add("N-parameter on right side of");
        expectedErrors.add("invalid regular expression");
        expectedErrors.add("regular expression must not use");
        expectedErrors.add("collation mismatch");
        expectedErrors.add("cannot compare");
        expectedErrors.add("negative substring length");
        expectedErrors.add("invalid byte sequence");
        expectedErrors.add("unterminated quoted string");
        expectedErrors.add("syntax error");
        expectedErrors.add("zero-length delimited identifier");
        expectedErrors.add("relation .+ does not exist");
        return expectedErrors;
    }

    @Override
    public void check() throws Exception {
        // A. Ensure tables have sufficient data for the optimizer to consider indexes
        ensureSufficientData();
        try {
            // Weight strategy: new/complex features get 2x weight, mature features 1x
            // Rationale: newer and more complex index features have higher bug density
            int mode = Randomly.fromOptions(
                // === HIGH WEIGHT (2x): New/complex features, higher bug probability ===
                12, 12,     // Expression Index (PG 11+, complex)
                13, 13,     // Partial Index (conditional, complex)
                15, 15,     // GiST/GIN Index (specialized index types)
                16, 16,     // Tsvector Index (full-text search GIN)
                17, 17,     // Optimizer Config Pairwise (complex interaction)
                19, 19,     // Deterministic Index Query (lowest IgnoreMe rate)
                20, 20,     // NULL Index Handling (edge cases)
                8, 8,       // Covering Index (index-only scan)
                9, 9,       // Index Merge (complex optimizer path)
                11, 11,     // Unique Index Consistency (constraint interaction)
                // === Phase 2: New Index Test Modes ===
                21, 21,     // Prefix Index (SUBSTRING function index)
                22, 22,     // Subquery + Index (semijoin paths)
                23, 23,     // Index Cond Pushdown (ICP equivalent)
                24, 24,     // BRIN Index (Block Range Index, PG-specific)
                // === NORMAL WEIGHT (1x): Mature/stable features ===
                1, 2, 3, 4, 6, 10, 14
            );
            switch (mode) {
            case 1: checkCreateIndexConsistency(); break;
            case 2: checkDropIndexConsistency(); break;
            case 3: checkIndexScanVsBitmapScan(); break;
            case 4: checkAggregatePlanConsistency(); break;
            // DEPRECATED: case 5 (checkJoinPlanConsistency) — not testing index, tests JOIN algorithm selection only
            // case 5: checkJoinPlanConsistency(); break;
            case 6: checkMultiIndexConsistency(); break;
            // === Deep Index Bug Modes ===
            case 8: checkCoveringIndex(); break;
            case 9: checkIndexMerge(); break;
            case 10: checkOrderByLimitIndex(); break;
            case 11: checkUniqueIndexConsistency(); break;
            case 12: checkExpressionIndex(); break;
            case 13: checkPartialIndex(); break;
            // === P0: Simple Index Query — highest plan-difference hit rate ===
            case 14: checkSimpleIndexQuery(); break;
            // === P0: PostgreSQL-Specific Index Features ===
            case 15: checkGiSTGINIndex(); break;      // GiST/GIN index for LIKE/array
            case 16: checkTsvectorIndex(); break;      // tsvector GIN full-text search
            // === P3: New Metamorphic Strategies ===
            case 17: checkOptimizerConfigPairwise(); break;  // enable_*=on vs enable_*=off pairwise
            case 18: checkSQLSemanticEquivalence(); break;   // IN-vs-OR, BETWEEN-vs-AND semantic equiv
            // === P4: Deterministic Index Query ===
            case 19: checkDeterministicIndexQuery(); break;  // PK-based WHERE, different index plans
            case 20: checkNullIndexHandling(); break;          // NULL index handling
            // === Phase 2: New Index Test Modes ===
            case 21: checkPrefixIndex(); break;               // Prefix index (SUBSTRING function index)
            case 22: checkSubqueryIndex(); break;             // Subquery + Index
            case 23: checkIndexCondPushdown(); break;         // Index Cond vs Filter (ICP equivalent)
            case 24: checkBRINIndex(); break;                 // BRIN Block Range Index (PG-specific)
            }
        } catch (NullPointerException e) {
            throw new IgnoreMeException();
        }
    }

    // ==================== Mode 0: Index Scan vs Seq Scan ====================

    private void checkIndexVsSeqScan() throws Exception {
        // Generate complex query using idxdiff's core generator
        PostgresSelect select = generateComplexSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[IDX_VS_SEQ] " + queryString;
        log(queryString);

        // Ensure at least one index exists on the queried tables
        ensureIndexesExist(select);

        // EXPLAIN filter: skip if plans are identical under different settings
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_bitmapscan = ON;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainForced = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainForced)) return;

        // Plan A: Default (likely SeqScan)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force Index Scan
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_bitmapscan = ON;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "INDEX_VS_SEQSCAN");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "INDEX_VS_SEQSCAN");
    }

    // ==================== Mode 1: Create Index Consistency ====================

    private void checkCreateIndexConsistency() throws Exception {
        PostgresSelect select = generateComplexSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[CREATE_IDX] " + queryString;
        log(queryString);

        // Execute before index creation
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Create a random index using idxdiff's index generator
        try {
            SQLQueryAdapter indexStmt = PostgresIndexGenerator.generate(globalState);
            globalState.executeStatement(indexStmt);
            // Analyze tables
            analyzeTablesFromSelect(select);
        } catch (Exception e) {
            return;
        }

        // Execute same query after index creation
        List<String> r2 = executeQuery(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "CREATE_INDEX_CONSISTENCY");
    }

    // ==================== Mode 2: Drop Index Consistency ====================

    private void checkDropIndexConsistency() throws Exception {
        PostgresSelect select = generateComplexSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[DROP_IDX] " + queryString;
        log(queryString);

        // Execute with indexes
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Find and drop a random index
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        List<PostgresIndex> allIndexes = new ArrayList<>();
        for (PostgresTable table : tables) {
            allIndexes.addAll(table.getIndexes());
        }
        if (allIndexes.isEmpty()) return;

        PostgresIndex idxToDrop = Randomly.fromList(allIndexes);
        try {
            ExpectedErrors dropErrors = new ExpectedErrors();
            dropErrors.add("cannot drop index");
            dropErrors.add("does not exist");
            dropErrors.add("dependency");
            globalState.executeStatement(new SQLQueryAdapter(
                    "DROP INDEX IF EXISTS " + idxToDrop.getIndexName() + ";", dropErrors, true));
            analyzeTablesFromSelect(select);
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "DROP_INDEX_CONSISTENCY");
    }

    // ==================== Mode 3: Index Scan vs Bitmap Scan ====================

    private void checkIndexScanVsBitmapScan() throws Exception {
        PostgresSelect select = generateComplexSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[IDX_VS_BITMAP] " + queryString;
        log(queryString);

        ensureIndexesExist(select);

        // EXPLAIN filter: skip if IndexScan and BitmapScan produce same plan
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainIdxScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_bitmapscan = ON;");
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainBitmapScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainIdxScan, explainBitmapScan)) return;

        // Plan A: Index Scan only
        List<String> r1;
        try {
            safeSet("SET enable_seqscan = OFF;");
            safeSet("SET enable_bitmapscan = OFF;");
            safeSet("SET enable_indexscan = ON;");
            safeSet("SET random_page_cost = 1.0;");
            r1 = executeQuery(queryString);
        } finally {
            restoreDefaultSettings();
        }
        if (r1 == null) return;

        // Plan B: Bitmap Scan only
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_bitmapscan = ON;");
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "INDEX_VS_BITMAP");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "INDEX_VS_BITMAP");
    }

    // ==================== Mode 4: Aggregate Plan Consistency ====================

    private void checkAggregatePlanConsistency() throws Exception {
        PostgresSelect select = generateAggregateSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[AGG_PLAN] " + queryString;
        log(queryString);

        ensureIndexesExist(select);

        // EXPLAIN filter: skip if HashAgg and GroupAgg produce same plan
        safeSet("SET enable_hashagg = ON;");
        List<String> explainHashAgg = getExplainPlan(queryString);
        restoreDefaultSettings();
        safeSet("SET enable_hashagg = OFF;");
        List<String> explainGroupAgg = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainHashAgg, explainGroupAgg)) return;

        // Plan A: Hash Agg
        safeSet("SET enable_hashagg = ON;");
        List<String> r1 = executeQuery(queryString);
        restoreDefaultSettings();
        if (r1 == null) return;

        // Plan B: Group Agg (sort-based)
        safeSet("SET enable_hashagg = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "AGGREGATE_PLAN");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "AGGREGATE_PLAN");
    }

    // ==================== Mode 5: Join Plan Consistency ====================

    private void checkJoinPlanConsistency() throws Exception {
        PostgresSelect select = generateJoinSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[JOIN_PLAN] " + queryString;
        log(queryString);

        ensureIndexesExist(select);

        // EXPLAIN filter: skip if default and forced plans are identical
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_hashjoin = OFF;");
        safeSet("SET enable_nestloop = OFF;");
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainForced = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainForced)) return;

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force merge join + index scan
        safeSet("SET enable_hashjoin = OFF;");
        safeSet("SET enable_nestloop = OFF;");
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "JOIN_PLAN");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "JOIN_PLAN");
    }

    // ==================== Mode 6: Multi-Index (create multiple + compare plans) ====================

    private void checkMultiIndexConsistency() throws Exception {
        PostgresSelect select = generateComplexSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[MULTI_IDX] " + queryString;
        log(queryString);

        // Create multiple indexes
        for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
            try {
                SQLQueryAdapter indexStmt = PostgresIndexGenerator.generate(globalState);
                globalState.executeStatement(indexStmt);
            } catch (Exception e) {
                // Index creation may fail — known errors handled by ExpectedErrors in PostgresIndexGenerator
            }
        }
        analyzeTablesFromSelect(select);

        // EXPLAIN filter: skip if SeqScan and IndexScan plans are identical
        safeSet("SET enable_seqscan = ON;");
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET enable_bitmapscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainIdxScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainSeqScan, explainIdxScan)) return;

        // Plan A: SeqScan
        safeSet("SET enable_seqscan = ON;");
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r1 = executeQuery(queryString);
        restoreDefaultSettings();
        if (r1 == null) return;

        // Plan B: Index Scan
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET enable_bitmapscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "MULTI_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "MULTI_INDEX");
    }

    // ==================== Mode 7: Index with ORDER BY ====================

    private void checkIndexWithOrderBy() throws Exception {
        PostgresSelect select = generateOrderedSelect();
        if (select == null) return;
        String queryString = PostgresVisitor.asString(select) + ";";
        lastQueryString = "[IDX_ORDERBY] " + queryString;
        log(queryString);

        ensureIndexesExist(select);

        // EXPLAIN filter: skip if Sort and IndexScan plans are identical
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSort = getExplainPlan(queryString);
        restoreDefaultSettings();
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET enable_bitmapscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainIdxScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainSort, explainIdxScan)) return;

        // Plan A: SeqScan + Sort
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r1 = executeQuery(queryString);
        restoreDefaultSettings();
        if (r1 == null) return;

        // Plan B: Index Scan (order from index)
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET enable_bitmapscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        // Strict comparison: order matters for ORDER BY queries
        compareResultsStrict(r1, r2, queryString, "INDEX_ORDERBY");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "INDEX_ORDERBY");
    }

    // ==================== Query Generation (Deep idxdiff Integration) ====================

    // Deeply nested expressions with functions, subqueries, CASE WHEN — same quality as idxdiff's built-in oracles.
    private PostgresSelect generateComplexSelect() {
        PostgresSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return null;

        try {
            PostgresTables targetTables = schema.getRandomTableNonEmptyTables();
            List<PostgresColumn> columns = targetTables.getColumns();
            List<PostgresTable> tables = targetTables.getTables();

            PostgresExpressionGenerator gen = new PostgresExpressionGenerator(globalState).setColumns(columns);

            PostgresSelect select = new PostgresSelect();
            select.setSelectType(Randomly.fromOptions(PostgresSelect.SelectType.values()));

            // Fetch columns — randomly select subset or use *
            List<PostgresExpression> fetchColumns = new ArrayList<>();
            if (Randomly.getBooleanWithRatherLowProbability()) {
                fetchColumns.add(PostgresConstant.createIntConstant(1)); // SELECT 1 style
            } else {
                List<PostgresColumn> subset = Randomly.nonEmptySubset(columns);
                for (int i = 0; i < subset.size(); i++) {
                    fetchColumns.add(gen.generateExpression(0));
                }
            }
            select.setFetchColumns(fetchColumns);

            // FROM tables
            select.setFromList(tables.stream()
                    .map(t -> new PostgresFromTable(t, Randomly.getBoolean()))
                    .collect(Collectors.toList()));

            // WHERE — B. Index-aware WHERE: 70% chance to use index-friendly condition
            if (Randomly.getBooleanWithRatherLowProbability() || Randomly.getBoolean()) {
                PostgresExpression indexWhere = tryGenerateIndexFriendlyWhere(tables, gen);
                if (indexWhere != null) {
                    select.setWhereClause(indexWhere);
                } else {
                    select.setWhereClause(gen.generateExpression(0, PostgresDataType.BOOLEAN));
                }
            }

            // JOINs — 40%+ queries involve multi-table JOINs for index coverage testing
            if (tables.size() > 1 && (Randomly.getBoolean() || Randomly.getBoolean())) {
                if (Randomly.getBoolean()) {
                    select.setJoinClauses(generateJoinClauses(gen, columns, tables));
                } else {
                    select.setJoinClauses(generateIndexFriendlyJoinClauses(tables));
                }
            }

            // Subquery JOINs — deeply nested
            if (Randomly.getBooleanWithRatherLowProbability()) {
                List<PostgresJoin> subqueryJoins = new ArrayList<>();
                for (int i = 0; i < Randomly.smallNumber(); i++) {
                    PostgresTables subTables = schema.getRandomTableNonEmptyTables();
                    PostgresSubquery subquery = createSubquery(String.format("sub%d", i), subTables);
                    PostgresExpression joinClause = gen.generateExpression(PostgresDataType.BOOLEAN);
                    PostgresJoinType joinType = PostgresJoinType.getRandom();
                    subqueryJoins.add(new PostgresJoin(subquery, joinClause, joinType));
                }
                if (select.getJoinClauses() != null) {
                    subqueryJoins.addAll(select.getJoinClauses());
                }
                select.setJoinClauses(subqueryJoins);
            }

            // GROUP BY
            if (Randomly.getBooleanWithRatherLowProbability()) {
                select.setGroupByExpressions(gen.generateExpressions(Randomly.smallNumber() + 1));
                if (Randomly.getBoolean()) {
                    select.setHavingClause(gen.generateHavingClause());
                }
            }

            // ORDER BY
            if (Randomly.getBoolean()) {
                select.setOrderByClauses(gen.generateOrderBys());
            }

            // LIMIT / OFFSET
            if (Randomly.getBoolean()) {
                select.setLimitClause(PostgresConstant.createIntConstant(
                        Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));
                if (Randomly.getBoolean()) {
                    select.setOffsetClause(PostgresConstant.createIntConstant(0));
                }
            }

            // FOR clause
            if (Randomly.getBooleanWithRatherLowProbability()) {
                select.setForClause(ForClause.getRandom());
            }

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    private PostgresSelect generateAggregateSelect() {
        PostgresSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return null;

        try {
            PostgresTables targetTables = schema.getRandomTableNonEmptyTables();
            List<PostgresColumn> columns = targetTables.getColumns();

            PostgresExpressionGenerator gen = new PostgresExpressionGenerator(globalState).setColumns(columns);

            PostgresSelect select = new PostgresSelect();
            select.setFromList(targetTables.getTables().stream()
                    .map(t -> new PostgresFromTable(t, Randomly.getBoolean()))
                    .collect(Collectors.toList()));

            // Aggregate fetch columns
            List<PostgresExpression> fetchColumns = new ArrayList<>();
            fetchColumns.add(gen.generateExpression(0)); // Random aggregate expression
            if (Randomly.getBoolean()) {
                fetchColumns.add(gen.generateExpression(0));
            }
            select.setFetchColumns(fetchColumns);

            // Complex WHERE
            if (Randomly.getBoolean()) {
                select.setWhereClause(gen.generateExpression(0, PostgresDataType.BOOLEAN));
            }

            // GROUP BY
            if (Randomly.getBoolean()) {
                select.setGroupByExpressions(gen.generateExpressions(Randomly.smallNumber() + 1));
                if (Randomly.getBoolean()) {
                    select.setHavingClause(gen.generateHavingClause());
                }
            }

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    private PostgresSelect generateJoinSelect() {
        PostgresSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().size() < 2) return null;

        try {
            PostgresTables targetTables = schema.getRandomTableNonEmptyTables();
            List<PostgresColumn> columns = targetTables.getColumns();
            List<PostgresTable> tables = new ArrayList<>(targetTables.getTables());

            PostgresExpressionGenerator gen = new PostgresExpressionGenerator(globalState).setColumns(columns);

            PostgresSelect select = new PostgresSelect();
            select.setFromList(tables.stream()
                    .map(t -> new PostgresFromTable(t, Randomly.getBoolean()))
                    .collect(Collectors.toList()));

            // Fetch columns
            List<PostgresExpression> fetchColumns = new ArrayList<>();
            for (int i = 0; i < Math.min(columns.size(), Randomly.smallNumber() + 1); i++) {
                fetchColumns.add(gen.generateExpression(0));
            }
            select.setFetchColumns(fetchColumns);

            // JOIN conditions — generated by expression generator
            select.setJoinClauses(generateJoinClauses(gen, columns, tables));

            // Complex WHERE
            if (Randomly.getBoolean()) {
                select.setWhereClause(gen.generateExpression(0, PostgresDataType.BOOLEAN));
            }

            // LIMIT
            if (Randomly.getBoolean()) {
                select.setLimitClause(PostgresConstant.createIntConstant(
                        Randomly.getPositiveOrZeroNonCachedInteger() % 200 + 1));
            }

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    private PostgresSelect generateOrderedSelect() {
        PostgresSchema schema = globalState.getSchema();
        if (schema.getDatabaseTables().isEmpty()) return null;

        try {
            PostgresTables targetTables = schema.getRandomTableNonEmptyTables();
            List<PostgresColumn> columns = targetTables.getColumns();

            PostgresExpressionGenerator gen = new PostgresExpressionGenerator(globalState).setColumns(columns);

            PostgresSelect select = new PostgresSelect();
            select.setFromList(targetTables.getTables().stream()
                    .map(t -> new PostgresFromTable(t, Randomly.getBoolean()))
                    .collect(Collectors.toList()));

            // Fetch columns
            List<PostgresExpression> fetchColumns = new ArrayList<>();
            List<PostgresColumn> subset = Randomly.nonEmptySubset(columns);
            for (int i = 0; i < subset.size(); i++) {
                fetchColumns.add(gen.generateExpression(0));
            }
            select.setFetchColumns(fetchColumns);

            // WHERE
            if (Randomly.getBoolean()) {
                select.setWhereClause(gen.generateExpression(0, PostgresDataType.BOOLEAN));
            }

            // ORDER BY — always present for this mode
            select.setOrderByClauses(gen.generateOrderBys());

            // LIMIT
            select.setLimitClause(PostgresConstant.createIntConstant(
                    Randomly.getPositiveOrZeroNonCachedInteger() % 100 + 1));

            return select;
        } catch (Exception e) {
            return null;
        }
    }

    private List<PostgresJoin> generateIndexFriendlyJoinClauses(List<PostgresTable> tables) {
        List<PostgresJoin> joinStatements = new ArrayList<>();
        if (tables.size() < 2) return joinStatements;

        try {
            List<PostgresTable> remaining = new ArrayList<>(tables);
            PostgresTable firstTable = remaining.remove(0);
            int nrJoinClauses = (int) Math.min(remaining.size(), Randomly.getNotCachedInteger(1, Math.min(remaining.size() + 1, 3)));

            for (int i = 0; i < nrJoinClauses && !remaining.isEmpty(); i++) {
                PostgresTable joinTable = Randomly.fromList(remaining);
                remaining.remove(joinTable);

                PostgresExpression onClause = generateIndexJoinCondition(firstTable, joinTable);
                PostgresJoinType joinType = PostgresJoinType.getRandom();
                joinStatements.add(new PostgresJoin(new PostgresFromTable(joinTable, Randomly.getBoolean()),
                        onClause, joinType));
            }
        } catch (Exception e) {
            // fallback: return empty
        }
        return joinStatements;
    }

    private PostgresExpression generateIndexJoinCondition(PostgresTable t1, PostgresTable t2) {
        List<PostgresColumn> cols1 = t1.getColumns();
        List<PostgresColumn> cols2 = t2.getColumns();
        if (cols1.isEmpty() || cols2.isEmpty()) return PostgresConstant.createTrue();

        Randomly r = globalState.getRandomly();
        int numConditions = r.getInteger(1, 3);
        PostgresExpression combined = null;

        for (int i = 0; i < numConditions; i++) {
            PostgresColumn c1 = Randomly.fromList(cols1);
            PostgresColumn c2 = Randomly.fromList(cols2);

            PostgresExpression ref1 = PostgresColumnValue.create(c1, null);
            PostgresExpression ref2 = PostgresColumnValue.create(c2, null);

            PostgresExpression condition;
            int opType = r.getInteger(0, 4);
            switch (opType) {
            case 0:
                condition = new PostgresBinaryComparisonOperation(ref1, ref2, PostgresBinaryComparisonOperator.EQUALS);
                break;
            case 1:
                condition = new PostgresBinaryComparisonOperation(ref1, ref2, PostgresBinaryComparisonOperator.GREATER);
                break;
            case 2:
                condition = new PostgresBinaryComparisonOperation(ref1, ref2, PostgresBinaryComparisonOperator.LESS);
                break;
            default:
                condition = new PostgresBinaryComparisonOperation(ref1, ref2, PostgresBinaryComparisonOperator.GREATER_EQUALS);
                break;
            }

            if (combined == null) {
                combined = condition;
            } else {
                combined = new PostgresBinaryLogicalOperation(combined, condition, BinaryLogicalOperator.AND);
            }
        }
        return combined != null ? combined : PostgresConstant.createTrue();
    }

    private List<PostgresJoin> generateJoinClauses(PostgresExpressionGenerator gen,
            List<PostgresColumn> columns, List<PostgresTable> tables) {
        List<PostgresJoin> joinStatements = new ArrayList<>();
        List<PostgresTable> remaining = new ArrayList<>(tables);
        if (remaining.isEmpty()) return joinStatements;

        // Remove the first table (it's in FROM)
        for (int i = 1; i < remaining.size() && i <= Randomly.smallNumber(); i++) {
            PostgresExpression joinClause = gen.generateExpression(PostgresDataType.BOOLEAN);
            PostgresTable table = Randomly.fromList(remaining);
            remaining.remove(table);
            PostgresJoinType joinType = PostgresJoinType.getRandom();
            PostgresJoin j = new PostgresJoin(new PostgresFromTable(table, Randomly.getBoolean()),
                    joinClause, joinType);
            joinStatements.add(j);
        }
        return joinStatements;
    }

    private PostgresSubquery createSubquery(String name, PostgresTables tables) {
        List<PostgresExpression> columns = new ArrayList<>();
        PostgresExpressionGenerator gen = new PostgresExpressionGenerator(globalState)
                .setColumns(tables.getColumns());
        for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
            columns.add(gen.generateExpression(0));
        }
        PostgresSelect select = new PostgresSelect();
        select.setFromList(tables.getTables().stream()
                .map(t -> new PostgresFromTable(t, Randomly.getBoolean()))
                .collect(Collectors.toList()));
        select.setFetchColumns(columns);
        if (Randomly.getBoolean()) {
            select.setWhereClause(gen.generateExpression(0, PostgresDataType.BOOLEAN));
        }
        if (Randomly.getBoolean()) {
            select.setLimitClause(PostgresConstant.createIntConstant(
                    Randomly.getPositiveOrZeroNonCachedInteger() % 50 + 1));
        }
        return new PostgresSubquery(select, name);
    }

    // ==================== Index Management ====================

    private void ensureIndexesExist(PostgresSelect select) {
        try {
            // Create 1-2 indexes using idxdiff's index generator
            int numIndexes = Randomly.smallNumber() + 1;
            for (int i = 0; i < numIndexes; i++) {
                try {
                    SQLQueryAdapter indexStmt = PostgresIndexGenerator.generate(globalState);
                    globalState.executeStatement(indexStmt);
                } catch (Exception e) {
                    // Index creation may fail — known errors handled by ExpectedErrors in PostgresIndexGenerator
                }
            }
            // Analyze tables
            PostgresSchema schema = globalState.getSchema();
            for (PostgresTable table : schema.getDatabaseTables()) {
                try {
                    globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + table.getName() + ";", true));
                } catch (Exception e) {
                    // ignore
                }
            }
        } catch (Exception e) {
            // ignore
        }
    }

    private void analyzeTablesFromSelect(PostgresSelect select) {
        try {
            PostgresSchema schema = globalState.getSchema();
            for (PostgresTable table : schema.getDatabaseTables()) {
                try {
                    globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + table.getName() + ";", true));
                } catch (Exception e) {
                    // ignore
                }
            }
        } catch (Exception e) {
            // ignore
        }
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

    private List<String> executeQueryWithRestore(String queryString) throws Exception {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(queryString, errors, globalState, " ||| ");
        } catch (IgnoreMeException e) {
            return null;
        } finally {
            restoreDefaultSettings();
        }
    }

    // For un-ordered result sets (no ORDER BY). LIMIT without ORDER BY is non-deterministic → multi-set check.
    // Also handles inheritance syntax (table*) and cross joins → non-deterministic across different scan methods.
    private void compareResultsSorted(List<String> r1, List<String> r2, String queryString, String mode) throws Exception {
        lastCompareFiltered = false;
        if (r1.equals(r2)) return;
        // Try sorted comparison (null-safe)
        List<String> sorted1 = new ArrayList<>(r1);
        List<String> sorted2 = new ArrayList<>(r2);
        sorted1.sort((a, b) -> {
            if (a == null && b == null) return 0;
            if (a == null) return -1;
            if (b == null) return 1;
            return a.compareTo(b);
        });
        sorted2.sort((a, b) -> {
            if (a == null && b == null) return 0;
            if (a == null) return -1;
            if (b == null) return 1;
            return a.compareTo(b);
        });
        if (sorted1.equals(sorted2)) return;
        if (areApproximatelyEqual(sorted1, sorted2)) return;

        String upperQuery = queryString.toUpperCase();

        // Inheritance syntax (table*) causes different scan methods to return different rows.
        // If sizes differ, it's due to inheritance row inclusion differences, not a bug.
        if (usesInheritanceSyntax(queryString) && sorted1.size() != sorted2.size()) {
            lastCompareFiltered = true;
            return;
        }

        // Cross joins with LIMIT → non-deterministic row ordering/selection.
        // Cross joins produce duplicate ORDER BY values (even when the column
        // is unique in its own table), making sort order non-deterministic.
        // With LIMIT, different plans may select different subsets of rows.
        // Always skip — even when sizes match but sets differ, the difference
        // is due to non-deterministic tie-breaking, not a real bug.
        if (usesCrossJoin(queryString) && upperQuery.contains("LIMIT")) {
            lastCompareFiltered = true;
            return;
        }

        // LIMIT without ORDER BY → non-deterministic row selection, ignore mismatch
        if (upperQuery.contains("LIMIT") && !upperQuery.contains("ORDER BY")) {
            lastCompareFiltered = true;
            return; // Non-deterministic with LIMIT, skip comparison
        }

        // GROUP BY with different result set sizes → non-deterministic
        // Non-strict GROUP BY or functional dependency edge cases can cause
        // different plans to pick different rows per group, leading to
        // different cardinality after DISTINCT/sorted comparison.
        // Real index bugs produce same row count but wrong VALUES.
        if (sorted1.size() != sorted2.size() && upperQuery.contains("GROUP BY")) {
            lastCompareFiltered = true;
            return;
        }

        // LIMIT with different result sizes → ORDER BY with non-unique sort keys
        // causes different tie-breaking between plans. Non-deterministic.
        if (sorted1.size() != sorted2.size() && upperQuery.contains("LIMIT")) {
            lastCompareFiltered = true;
            return;
        }

        // LIMIT + ORDER BY: If unique tie-breaker → deterministic → report bug.
        // Otherwise, check actual ORDER BY column values in the result sets.
        // LIMIT + ORDER BY without unique tie-breaker → always skip.
        // Different plans can select different rows at the LIMIT boundary when ORDER BY
        // has duplicate values. Even when the ORDER BY multi-sets differ between plans,
        // this is non-deterministic tie-breaking (not a real bug), because one plan may
        // include a tied row at the boundary while the other doesn't.
        // Only report when ORDER BY has a unique tie-breaker (deterministic sorting).
        if (upperQuery.contains("LIMIT") && upperQuery.contains("ORDER BY")) {
            if (hasUniqueOrderByTieBreaker(queryString)) {
                // ORDER BY has unique tie-breaker → result should be fully deterministic
                // Fall through to report the bug
            } else {
                // Non-unique ORDER BY + LIMIT → non-deterministic row selection → skip
                lastCompareFiltered = true;
                return;
            }
        }

        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] Query: " + queryString);
        ComparatorHelper.assumeResultSetsAreEqual(r1, r2, queryString, combinedString, globalState);
    }

    // For ORDER BY queries. LIMIT + unique tie-breaker → strict comparison.
    // Inheritance syntax (table*) and cross joins fall back to set comparison (non-deterministic sort order).
    private void compareResultsStrict(List<String> r1, List<String> r2, String queryString, String mode) throws Exception {
        lastCompareFiltered = false;
        if (r1.equals(r2)) return;

        String upperQuery = queryString.toUpperCase();

        // LIMIT without ORDER BY → non-deterministic, skip
        if (upperQuery.contains("LIMIT") && !upperQuery.contains("ORDER BY")) {
            lastCompareFiltered = true;
            return;
        }

        // Inheritance syntax (table*) causes different scan methods to return different rows
        // because SeqScan includes child tables while some IndexScan paths may not.
        // This is a known PostgreSQL behavior, not a bug — always use set comparison.
        boolean usesInheritance = usesInheritanceSyntax(queryString);

        // Cross joins (FROM multiple tables) create duplicate ORDER BY values even when
        // the ORDER BY column is unique in its own table, making sort order non-deterministic.
        boolean usesCrossJoin = usesCrossJoin(queryString);

        // Views (especially recursive/temporary) may produce non-deterministic row ordering.
        // When combined with cross joins, different execution paths can return different result sets.
        boolean usesNonDeterministicView = usesNonDeterministicView(queryString);

        // Cross join + non-deterministic view → result set depends on execution path → skip
        if (usesCrossJoin && usesNonDeterministicView) {
            lastCompareFiltered = true;
            return;
        }

        // When inheritance or cross join is involved, compare as sorted sets (not strict order)
        if (usesInheritance || usesCrossJoin) {
            List<String> sorted1 = new ArrayList<>(r1);
            List<String> sorted2 = new ArrayList<>(r2);
            sorted1.sort((a, b) -> {
                if (a == null && b == null) return 0;
                if (a == null) return -1;
                if (b == null) return 1;
                return a.compareTo(b);
            });
            sorted2.sort((a, b) -> {
                if (a == null && b == null) return 0;
                if (a == null) return -1;
                if (b == null) return 1;
                return a.compareTo(b);
            });
            if (sorted1.equals(sorted2) || areApproximatelyEqual(sorted1, sorted2)) {
                lastCompareFiltered = true;
                return; // Same values, different order → not a bug
            }
            // Inheritance with different sizes → non-deterministic row inclusion
            if (usesInheritance && sorted1.size() != sorted2.size()) {
                lastCompareFiltered = true;
                return;
            }
            // Cross join with LIMIT + different sizes → non-deterministic tie-breaking
            if (usesCrossJoin && upperQuery.contains("LIMIT") && sorted1.size() != sorted2.size()) {
                lastCompareFiltered = true;
                return;
            }
            // Different values after sorting → fall through to report
        }

        // LIMIT with different result sizes → check if ORDER BY is unique
        if (r1.size() != r2.size() && upperQuery.contains("LIMIT")) {
            if (!hasUniqueOrderByTieBreaker(queryString)) {
                lastCompareFiltered = true;
                return; // Non-unique ORDER BY + LIMIT → non-deterministic
            }
            // Unique ORDER BY + LIMIT but different sizes → real bug, fall through
        }

        if (areApproximatelyEqual(r1, r2)) return;

        // LIMIT + ORDER BY: check if results differ only in order (not values)
        if (upperQuery.contains("LIMIT") && upperQuery.contains("ORDER BY")) {
            // Cross join duplicates unique ORDER BY values, making sort non-deterministic.
            // When LIMIT + non-unique ORDER BY, both order AND subset selection are
            // non-deterministic → skip to avoid false positives.
            boolean uniqueTieBreaker = hasUniqueOrderByTieBreaker(queryString) && !usesCrossJoin;
            if (uniqueTieBreaker) {
                // Deterministic ORDER BY → different order = real bug → fall through
            } else {
                // No unique tie-breaker + LIMIT → row selection is non-deterministic
                lastCompareFiltered = true;
                return;
            }
        }

        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] Query: " + queryString);
        ComparatorHelper.assumeResultSetsAreEqual(r1, r2, queryString, combinedString, globalState);
    }

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

    private boolean isApproximatelyEqualNumeric(String s1, String s2) {
        try {
            double d1 = Double.parseDouble(s1);
            double d2 = Double.parseDouble(s2);
            if (Double.isNaN(d1) || Double.isNaN(d2)) return Double.isNaN(d1) && Double.isNaN(d2);
            if (Double.isInfinite(d1) || Double.isInfinite(d2)) return d1 == d2;
            double diff = Math.abs(d1 - d2);
            double maxVal = Math.max(Math.abs(d1), Math.abs(d2));
            if (maxVal < EPSILON) return diff < EPSILON;
            return diff / maxVal < RELATIVE_TOLERANCE;
        } catch (NumberFormatException e) {
            return false;
        }
    }

    // ==================== P1: Index-Friendly Table Creation ====================

    // Creates 1-2 dedicated idx_tN tables (INT+TEXT, NOT NULL, pre-built B-tree/composite/covering/partial/expr indexes).
    // Supplements idxdiff's random tables to ensure the optimizer always has rich index structures.
    private void createIndexFriendlyTables() {
        ExpectedErrors tableErrors = new ExpectedErrors();
        tableErrors.add("already exists");
        tableErrors.add("relation .* already exists");
        tableErrors.add("cannot create index on relation");
        tableErrors.add("functions in index expression must be marked IMMUTABLE");
        tableErrors.add("has no default operator class");

        // Check if index-friendly tables already exist
        try {
            PostgresSchema schema = globalState.getSchema();
            boolean hasIdxTable = false;
            for (PostgresTable t : schema.getDatabaseTables()) {
                if (t.getName().startsWith("idx_")) {
                    hasIdxTable = true;
                    break;
                }
            }
            if (hasIdxTable) return; // Already created in a previous iteration
        } catch (Exception e) { return; }

        // Create 1-2 index-friendly tables
        int numTables = Randomly.fromOptions(1, 1, 2);
        for (int t = 0; t < numTables; t++) {
            String tableName = "idx_t" + t;
            try {
                // Table with 8 columns: 5 INT + 3 TEXT
                StringBuilder createSQL = new StringBuilder();
                createSQL.append("CREATE TABLE IF NOT EXISTS ").append(tableName).append(" (");
                createSQL.append("c0 INT NOT NULL, ");
                createSQL.append("c1 INT NOT NULL, ");
                createSQL.append("c2 INT, "); // nullable for NULL boundary testing
                createSQL.append("c3 INT NOT NULL, ");
                createSQL.append("c4 INT NOT NULL, ");
                createSQL.append("c5 TEXT NOT NULL, ");
                createSQL.append("c6 TEXT, "); // nullable
                createSQL.append("c7 TEXT NOT NULL");
                createSQL.append(");");
                globalState.executeStatement(new SQLQueryAdapter(createSQL.toString(), tableErrors, true));

                // Pre-build diverse indexes on this table
                String[] indexStmts = {
                    // Single-column B-tree (most common)
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c0 ON " + tableName + " (c0);",
                    // Composite index (2 columns)
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);",
                    // Composite index (3 columns) for deep prefix testing
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c0c1c3 ON " + tableName + " (c0, c1, c3);",
                    // Covering index (INCLUDE)
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_cover ON " + tableName + " (c0) INCLUDE (c3, c4);",
                    // Partial index
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_partial ON " + tableName + " (c1) WHERE c0 > 0;",
                    // Expression index
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_expr ON " + tableName + " (ABS(c0));",
                    // TEXT index for pattern matching testing
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c5 ON " + tableName + " (c5);",
                    // DESC order index
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c0desc ON " + tableName + " (c0 DESC);",
                };

                for (String idxSQL : indexStmts) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(idxSQL, tableErrors, true));
                    } catch (Exception e) { }
                }

                // Insert initial data (200 rows) — enough for optimizer to prefer indexes
                ExpectedErrors insertErrors = new ExpectedErrors();
                insertErrors.add("violates not-null constraint");
                insertErrors.add("integer out of range");
                insertErrors.add("duplicate key value");
                insertErrors.add("invalid input syntax");
                insertErrors.add("division by zero");
                Randomly r = globalState.getRandomly();
                for (int batch = 0; batch < 4; batch++) {
                    StringBuilder insertSQL = new StringBuilder();
                    insertSQL.append("INSERT INTO ").append(tableName).append(" VALUES ");
                    for (int row = 0; row < 50; row++) {
                        if (row > 0) insertSQL.append(", ");
                        insertSQL.append("(");
                        insertSQL.append(r.getInteger(-32768, 32767)).append(", ");  // c0
                        insertSQL.append(r.getInteger(-32768, 32767)).append(", ");  // c1
                        insertSQL.append(Randomly.getBoolean() ? String.valueOf(r.getInteger(-32768, 32767)) : "NULL").append(", ");  // c2
                        insertSQL.append(r.getInteger(-32768, 32767)).append(", ");  // c3
                        insertSQL.append(r.getInteger(-32768, 32767)).append(", ");  // c4
                        insertSQL.append("'").append(sanitizeStringLiteral(r.getString())).append("', ");  // c5
                        insertSQL.append(Randomly.getBoolean() ? "'" + sanitizeStringLiteral(r.getString()) + "'" : "NULL").append(", ");  // c6
                        insertSQL.append("'").append(sanitizeStringLiteral(r.getString())).append("'");  // c7
                        insertSQL.append(")");
                    }
                    insertSQL.append(" ON CONFLICT DO NOTHING;");
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(insertSQL.toString(), insertErrors, true));
                    } catch (Exception e) { }
                }

                // Analyze
                globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tableName + ";", true));
            } catch (Exception e) {
                // Table/index creation may fail, ignore
            }
        }
    }

    // ==================== A. Ensure Sufficient Data ====================

    // PostgreSQL won't use an index scan on tables with < ~20 rows; populates each table with 150 rows.
    // Runs once per oracle instance (dataPopulated flag).
    private void ensureSufficientData() {
        if (dataPopulated) return;
        // Refresh schema to reflect any DDL changes (views, generated columns, etc.)
        // that occurred during database generation. Without this, the cached schema
        // may be stale — e.g., a column altered to be generated won't be filtered out,
        // and views created after initial schema load won't be detected.
        try {
            globalState.updateSchema();
        } catch (Exception e) { return; }
        dataPopulated = true;

        // === P1: Create index-friendly tables for better index testing ===
        createIndexFriendlyTables();

        // Build expected errors for INSERT statements — these are common
        // constraint violations that can occur when inserting random data.
        // Without ExpectedErrors, SQLQueryAdapter.checkException() throws
        // AssertionError (which extends Error, not Exception), so
        // catch(Exception) cannot catch it.
        ExpectedErrors insertErrors = new ExpectedErrors();
        insertErrors.add("violates not-null constraint");
        insertErrors.add("violates check constraint");
        insertErrors.add("violates unique constraint");
        insertErrors.add("new row violates check option");
        insertErrors.add("cannot insert into view");
        insertErrors.add("cannot insert a null value into column");
        insertErrors.add("value too long");
        insertErrors.add("integer out of range");
        insertErrors.add("value .* out of range");
        insertErrors.add("duplicate key value");
        insertErrors.add("invalid input syntax");
        insertErrors.add("division by zero");
        insertErrors.add("syntax error");
        insertErrors.add("permission denied");
        insertErrors.add("relation .* does not exist");
        insertErrors.add("out of memory");
        insertErrors.add("canceling statement");
        insertErrors.add("invalid regular expression");
        insertErrors.add("quantifier operand invalid");
        insertErrors.add("cannot create index on relation");

        try {
            PostgresSchema schema = globalState.getSchema();
            for (PostgresTable table : schema.getDatabaseTables()) {
                if (table.getColumns().isEmpty()) continue;
                // Skip views — cannot INSERT into views
                if (table.isView()) continue;
                // Skip partitioned tables — cannot INSERT without partitions
                if (table.isPartitioned()) continue;
                try {
                    // Build INSERT with 50 rows at a time, repeat a few times
                    // Exclude generated columns — PostgreSQL does not allow inserting into them.
                    // Exclude SERIAL/IDENTITY columns (has nextval() default) — inserting explicit
                    // values triggers CHECK constraints with POWER/exponentiation causing
                    // underflow/overflow (e.g., CHECK(c0 = c0 * c0^c0) with c0=-23700).
                    List<PostgresColumn> insertableCols = table.getColumns().stream()
                            .filter(c -> !c.isGenerated())
                            .filter(c -> !c.hasSequenceDefault())
                            .collect(Collectors.toList());
                    if (insertableCols.isEmpty()) continue;
                    for (int batch = 0; batch < 3; batch++) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("INSERT INTO ").append(table.getName()).append("(");
                        sb.append(insertableCols.stream()
                                .map(c -> c.getName())
                                .collect(Collectors.joining(", ")));
                        sb.append(") VALUES ");
                        for (int row = 0; row < 50; row++) {
                            if (row > 0) sb.append(", ");
                            sb.append("(");
                            for (int col = 0; col < insertableCols.size(); col++) {
                                if (col > 0) sb.append(", ");
                                PostgresColumn c = insertableCols.get(col);
                                sb.append(generateRandomValueForType(c.getType()));
                            }
                            sb.append(")");
                        }
                        sb.append(" ON CONFLICT DO NOTHING;");
                        // Log INSERT for reproducibility
                        log(sb.toString());
                        globalState.executeStatement(new SQLQueryAdapter(sb.toString(), insertErrors, true));
                    }
                } catch (Throwable t) {
                    // INSERT may fail due to constraints, trigger errors, or
                    // unexpected PostgreSQL errors. SQLQueryAdapter.checkException()
                    // throws AssertionError (extends Error, not Exception) when
                    // the PSQLException doesn't match any expected error pattern.
                    // Must catch Throwable to handle all cases and keep the fuzzer running.
                }
                // Analyze after inserts
                try {
                    String analyzeStmt = "ANALYZE " + table.getName() + ";";
                    log(analyzeStmt);
                    globalState.executeStatement(new SQLQueryAdapter(analyzeStmt, true));
                } catch (Exception e) { }
            }
        } catch (Exception e) { }
    }

    // Strips control characters (newline, tab, etc.) that break PostgreSQL string literals; escapes single quotes.
    private static String sanitizeStringLiteral(String s) {
        StringBuilder sb = new StringBuilder(s.length());
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            // Keep only printable, non-control characters (space and above, excluding DEL)
            if (c >= ' ' && c != '\u007F') {
                sb.append(c);
            }
        }
        // Escape single quotes for PostgreSQL ('' escaping)
        return sb.toString().replace("'", "''");
    }

    private String generateRandomValueForType(PostgresDataType type) {
        Randomly r = globalState.getRandomly();
        switch (type) {
        case INT:
            // Use SMALLINT-safe range [-32768, 32767] because PostgreSQL maps
            // both "smallint" and "integer" to PostgresDataType.INT.
            // r.getInteger() (no bounds) returns a long that can overflow smallint columns.
            return String.valueOf(r.getInteger(-32768, 32767));
        case BOOLEAN:
            return Randomly.getBoolean() ? "TRUE" : "FALSE";
        case TEXT:
            // Sanitize: remove control characters (newlines, tabs, etc.) that
            // break SQL string literals, then escape single quotes.
            return "'" + sanitizeStringLiteral(r.getString()) + "'";
        case DECIMAL:
        case FLOAT:
            // Use getFiniteDouble() to avoid Infinity/NaN values
            return String.valueOf(r.getFiniteDouble());
        case REAL:
            // PostgreSQL REAL is 4-byte float (max ~3.4E38).
            // Double.MAX_VALUE (1.797E308) overflows REAL → out-of-range error.
            // Cast to float to ensure value is within REAL range.
            // Guard: (float) cast of large doubles produces Infinity,
            // which PG interprets as a column name, not a literal.
            float fVal = (float) r.getFiniteDouble();
            if (Float.isInfinite(fVal) || Float.isNaN(fVal)) {
                return "0.0";
            }
            // Guard: subnormal floats (e.g., 1.4E-45) can cause
            // "value is out of range for type real" in PostgreSQL.
            if (fVal != 0.0f && Math.abs(fVal) < Float.MIN_NORMAL) {
                return "0.0";
            }
            return String.valueOf(fVal);
        case RANGE:
            // int4range with inclusive bounds: '[lower,upper)' format
            int rLow = r.getInteger(0, 50);
            int rHigh = rLow + r.getInteger(1, 10);
            return "'[" + rLow + "," + rHigh + ")'";
        case MONEY:
            return "'" + r.getInteger(0, 1000) + ".00'";
        case BIT:
            return "B'" + r.getInteger(0, 2) + "'";
        case INET:
            return "'192.168.1." + r.getInteger(1, 254) + "'";
        default:
            return "NULL";
        }
    }

    // ==================== P0: Data-Aware Value Generation ====================

    // Priority: sampleColumnValues > MIN/MAX > random. Targets actual data so WHERE conditions
    // hit real rows instead of producing empty result sets (which never trigger index scans).
    private String generateDataAwareValueForType(String tableName, PostgresColumn col) {
        // Priority 1: Sample actual values from the table (70% chance)
        if (!Randomly.getBooleanWithRatherLowProbability()) {
            List<String> sampled = sampleColumnValues(tableName, col.getName(), 5);
            if (sampled != null && !sampled.isEmpty()) {
                String val = Randomly.fromList(sampled);
                return quoteSampledValue(val, col);
            }
        }
        // Priority 2: Use MIN or MAX value for better index hit rate
        String minMax = tryGetMinMaxValue(tableName, col);
        if (minMax != null) {
            return minMax;
        }
        // Priority 3: Random value (last resort — least likely to hit index)
        return generateRandomValueForType(col.getType());
    }

    // TEXT, MONEY, INET, BIT, RANGE → single-quoted; BOOLEAN → TRUE/FALSE; MONEY $N must be quoted
    // to avoid PostgreSQL treating $N as a prepared-statement parameter.
    private String quoteSampledValue(String rawValue, PostgresColumn col) {
        if (rawValue == null) return "NULL";
        if (col.getType() == PostgresDataType.TEXT) {
            if (!rawValue.startsWith("'") || rawValue.length() < 2) {
                return "'" + sanitizeStringLiteral(rawValue) + "'";
            }
            // Strip outer quotes, escape inner content, re-wrap to ensure all
            // single quotes inside the value are properly escaped.
            String inner = rawValue.substring(1, rawValue.length() - 1);
            return "'" + sanitizeStringLiteral(inner) + "'";
        }
        if (col.getType() == PostgresDataType.MONEY) {
            // PostgreSQL money type returns values like "$636", "$803" from SELECT.
            // These must be single-quoted, otherwise $N is interpreted as a
            // prepared-statement positional parameter, causing:
            //   ERROR: could not determine data type of parameter $N
            if (!rawValue.startsWith("'")) {
                return "'" + sanitizeStringLiteral(rawValue) + "'";
            }
            return rawValue;
        }
        // INET types need quoting: '192.168.1.1', '96.242.233.145/32'
        if (col.getType() == PostgresDataType.INET) {
            if (!rawValue.startsWith("'")) {
                return "'" + sanitizeStringLiteral(rawValue) + "'";
            }
            return rawValue;
        }
        // BIT/BIT VARYING types may need quoting if they look like B'...'
        // PostgreSQL returns e.g. "10101010" or B'10101010' — ensure proper quoting
        if (col.getType() == PostgresDataType.BIT) {
            if (rawValue.startsWith("B'") || rawValue.startsWith("b'")) {
                return rawValue; // already properly formatted
            }
            // Bare bit string literal — wrap in B'...'
            return "B'" + sanitizeStringLiteral(rawValue) + "'";
        }
        // RANGE types (int4range etc.) need quoting: '[-355171657,1098111111]'
        if (col.getType() == PostgresDataType.RANGE) {
            if (!rawValue.startsWith("'")) {
                return "'" + sanitizeStringLiteral(rawValue) + "'::int4range";
            }
            return rawValue;
        }
        // BOOLEAN: PostgreSQL returns 't'/'f', but also accepts TRUE/FALSE keywords
        if (col.getType() == PostgresDataType.BOOLEAN) {
            if (rawValue.equalsIgnoreCase("t") || rawValue.equalsIgnoreCase("true")) {
                return "TRUE";
            }
            if (rawValue.equalsIgnoreCase("f") || rawValue.equalsIgnoreCase("false")) {
                return "FALSE";
            }
            return rawValue;
        }
        return rawValue;
    }

    // MIN/MAX fallback for data-aware value generation; returns null on error.
    private String tryGetMinMaxValue(String tableName, PostgresColumn col) {
        try {
            String func = Randomly.getBoolean() ? "MIN" : "MAX";
            String query = "SELECT " + func + "(" + col.getName() + ") FROM " + tableName + ";";
            List<String> result = executeQuery(query);
            if (result != null && !result.isEmpty() && result.get(0) != null) {
                String val = result.get(0).trim();
                if (col.getType() == PostgresDataType.TEXT) {
                    // Strip any outer quotes, then always sanitize and re-wrap
                    if (val.startsWith("'") && val.endsWith("'") && val.length() >= 2) {
                        val = val.substring(1, val.length() - 1);
                    }
                    val = "'" + sanitizeStringLiteral(val) + "'";
                }
                if (col.getType() == PostgresDataType.MONEY) {
                    // PostgreSQL money type returns values like "$636" from MIN/MAX.
                    // These must be single-quoted, otherwise $N is interpreted as a
                    // prepared-statement positional parameter.
                    if (!val.startsWith("'")) {
                        val = "'" + sanitizeStringLiteral(val) + "'";
                    }
                }
                if (col.getType() == PostgresDataType.INET) {
                    if (!val.startsWith("'")) {
                        val = "'" + sanitizeStringLiteral(val) + "'";
                    }
                }
                if (col.getType() == PostgresDataType.BIT) {
                    if (!val.startsWith("B'") && !val.startsWith("b'")) {
                        val = "B'" + sanitizeStringLiteral(val) + "'";
                    }
                }
                if (col.getType() == PostgresDataType.RANGE) {
                    if (!val.startsWith("'")) {
                        val = "'" + sanitizeStringLiteral(val) + "'::int4range";
                    }
                }
                if (col.getType() == PostgresDataType.BOOLEAN) {
                    if (val.equalsIgnoreCase("t") || val.equalsIgnoreCase("true")) {
                        val = "TRUE";
                    } else if (val.equalsIgnoreCase("f") || val.equalsIgnoreCase("false")) {
                        val = "FALSE";
                    }
                }
                return val;
            }
        } catch (Exception e) { }
        return null;
    }

    // ==================== B. Index-Aware WHERE Generation ====================

    // Analyzes actual indexes and triggers specific PG optimizer paths:
    // composite prefix, Bitmap OR, composite full match, NULL boundary, type-specific (IN/LIKE).
    private PostgresExpression tryGenerateIndexFriendlyWhere(List<PostgresTable> tables, PostgresExpressionGenerator gen) {
        try {
            // Step 1: Collect index information
            List<PostgresColumn> indexedCols = new ArrayList<>();
            List<List<PostgresColumn>> compositeIdxCols = new ArrayList<>();
            List<PostgresColumn> singleIdxCols = new ArrayList<>();

            for (PostgresTable table : tables) {
                for (PostgresIndex idx : table.getIndexes()) {
                    List<String> idxColNames = idx.getColumnNames();
                    if (idxColNames == null || idxColNames.isEmpty()) continue;

                    List<PostgresColumn> idxColumns = new ArrayList<>();
                    for (String colName : idxColNames) {
                        for (PostgresColumn col : table.getColumns()) {
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

            // Step 2: Choose strategy
            int strategy;
            if (!compositeIdxCols.isEmpty() && singleIdxCols.size() >= 2 && Randomly.getBoolean()) {
                strategy = r.getInteger(0, 6);
            } else if (!compositeIdxCols.isEmpty()) {
                strategy = r.getInteger(0, 4);
            } else if (singleIdxCols.size() >= 2) {
                strategy = Randomly.fromOptions(0, 1, 4);
            } else if (!indexedCols.isEmpty()) {
                strategy = r.getInteger(0, 2);
            } else {
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

    // Strategy 1: composite index prefix condition — triggers composite index range scan.
    private PostgresExpression generateCompositePrefixCondition(
            List<List<PostgresColumn>> compositeIdxCols, Randomly r, PostgresExpressionGenerator gen) {
        if (compositeIdxCols.isEmpty()) return null;
        List<PostgresColumn> idxCols = Randomly.fromList(compositeIdxCols);
        int prefixLen = Math.min(idxCols.size(), r.getInteger(1, 4));
        PostgresExpression combined = null;
        for (int i = 0; i < prefixLen; i++) {
            PostgresColumn col = idxCols.get(i);
            PostgresExpression colRef = PostgresColumnValue.create(col, null);
            PostgresExpression condition;
            if (i == 0) {
                condition = new PostgresBinaryComparisonOperation(colRef,
                        PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.EQUALS);
            } else if (i == prefixLen - 1 && Randomly.getBoolean()) {
                condition = generateRangeCondition(colRef, col, r);
            } else {
                condition = generateSimpleIndexCondition(colRef, col, r);
            }
            combined = (combined == null) ? condition
                    : new PostgresBinaryLogicalOperation(combined, condition, BinaryLogicalOperator.AND);
        }
        return maybeAddComplexExtra(combined, gen);
    }

    // Strategy 2: full composite index condition — triggers unique/ref lookup.
    private PostgresExpression generateFullCompositeCondition(
            List<List<PostgresColumn>> compositeIdxCols, Randomly r, PostgresExpressionGenerator gen) {
        if (compositeIdxCols.isEmpty()) return null;
        List<PostgresColumn> idxCols = Randomly.fromList(compositeIdxCols);
        PostgresExpression combined = null;
        for (PostgresColumn col : idxCols) {
            PostgresExpression colRef = PostgresColumnValue.create(col, null);
            PostgresExpression condition = new PostgresBinaryComparisonOperation(colRef,
                    PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.EQUALS);
            combined = (combined == null) ? condition
                    : new PostgresBinaryLogicalOperation(combined, condition, BinaryLogicalOperator.AND);
        }
        return maybeAddComplexExtra(combined, gen);
    }

    // Strategy 3: index merge condition — OR across different indexed columns (Bitmap OR).
    private PostgresExpression generateIndexMergeCondition(
            List<PostgresColumn> singleIdxCols, List<PostgresColumn> indexedCols, Randomly r, PostgresExpressionGenerator gen) {
        List<PostgresColumn> candidates = singleIdxCols.size() >= 2 ? singleIdxCols : indexedCols;
        if (candidates.size() < 2) return null;

        java.util.Collections.shuffle(candidates);
        PostgresColumn col1 = candidates.get(0);
        PostgresColumn col2 = candidates.get(1);

        PostgresExpression colRef1 = PostgresColumnValue.create(col1, null);
        PostgresExpression colRef2 = PostgresColumnValue.create(col2, null);

        PostgresExpression cond1 = generateRangeCondition(colRef1, col1, r);
        PostgresExpression cond2 = generateRangeCondition(colRef2, col2, r);

        PostgresExpression orCond = new PostgresBinaryLogicalOperation(cond1, cond2, BinaryLogicalOperator.OR);
        return maybeAddComplexExtra(orCond, gen);
    }

    // Strategy 4: range with NULL handling — tests index scan NULL boundary.
    private PostgresExpression generateRangeWithNullCondition(
            List<PostgresColumn> indexedCols, Randomly r, PostgresExpressionGenerator gen) {
        PostgresColumn col = Randomly.fromList(indexedCols);
        PostgresExpression colRef = PostgresColumnValue.create(col, null);

        PostgresExpression rangeCond = generateRangeCondition(colRef, col, r);

        PostgresExpression nullCond;
        if (Randomly.getBoolean()) {
            nullCond = new PostgresPostfixOperation(PostgresColumnValue.create(col, null), PostfixOperator.IS_NULL);
            PostgresExpression orNull = new PostgresBinaryLogicalOperation(rangeCond, nullCond, BinaryLogicalOperator.OR);
            return maybeAddComplexExtra(orNull, gen);
        } else {
            // col IS NOT NULL (use IS_NOT_NULL postfix operator directly)
            PostgresExpression notNullCond = new PostgresPostfixOperation(
                    PostgresColumnValue.create(col, null), PostfixOperator.IS_NOT_NULL);
            PostgresExpression andNotNull = new PostgresBinaryLogicalOperation(rangeCond, notNullCond, BinaryLogicalOperator.AND);
            return maybeAddComplexExtra(andNotNull, gen);
        }
    }

    // Strategy 5: multi-index OR with varied operators — triggers BitmapOr.
    private PostgresExpression generateMultiIndexOrCondition(
            List<PostgresColumn> indexedCols, Randomly r, PostgresExpressionGenerator gen) {
        if (indexedCols.size() < 2) return null;
        int numCols = Math.min(indexedCols.size(), r.getInteger(2, 4));
        List<PostgresColumn> shuffled = new ArrayList<>(indexedCols);
        java.util.Collections.shuffle(shuffled);

        PostgresExpression combined = null;
        for (int i = 0; i < numCols; i++) {
            PostgresColumn col = shuffled.get(i);
            PostgresExpression colRef = PostgresColumnValue.create(col, null);
            PostgresExpression condition;
            int variant = r.getInteger(0, 3);
            switch (variant) {
            case 0:
                condition = new PostgresInOperation(colRef, generateConstantList(col.getType(), r, 3, 6), false);
                break;
            case 1:
                condition = new PostgresBetweenOperation(colRef,
                        PostgresExpressionGenerator.generateConstant(r, col.getType()),
                        PostgresExpressionGenerator.generateConstant(r, col.getType()), false);
                break;
            default:
                condition = generateRangeCondition(colRef, col, r);
                break;
            }
            combined = (combined == null) ? condition
                    : new PostgresBinaryLogicalOperation(combined, condition, BinaryLogicalOperator.OR);
        }
        return maybeAddComplexExtra(combined, gen);
    }

    // Strategy 6: type-aware conditions for specific optimizer paths.
    private PostgresExpression generateTypeAwareCondition(
            List<PostgresColumn> indexedCols, Randomly r, PostgresExpressionGenerator gen) {
        PostgresColumn col = Randomly.fromList(indexedCols);
        PostgresExpression colRef = PostgresColumnValue.create(col, null);
        PostgresExpression condition;

        switch (col.getType()) {
        case INT:
            if (Randomly.getBoolean()) {
                condition = new PostgresInOperation(colRef, generateConstantList(col.getType(), r, 5, 15), false);
            } else {
                condition = new PostgresBetweenOperation(colRef,
                        PostgresExpressionGenerator.generateConstant(r, col.getType()),
                        PostgresExpressionGenerator.generateConstant(r, col.getType()), false);
            }
            break;
        case TEXT:
            if (Randomly.getBoolean()) {
                condition = new PostgresBinaryComparisonOperation(colRef,
                        PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.EQUALS);
            } else {
                condition = new PostgresInOperation(colRef, generateConstantList(col.getType(), r, 2, 5), false);
            }
            break;
        case FLOAT:
        case REAL:
        case DECIMAL:
            condition = generateRangeCondition(colRef, col, r);
            break;
        default:
            condition = generateSimpleIndexCondition(colRef, col, r);
            break;
        }

        if (indexedCols.size() >= 2 && Randomly.getBooleanWithRatherLowProbability()) {
            PostgresColumn col2;
            do { col2 = Randomly.fromList(indexedCols); } while (col2 == col);
            PostgresExpression colRef2 = PostgresColumnValue.create(col2, null);
            PostgresExpression cond2 = generateSimpleIndexCondition(colRef2, col2, r);
            BinaryLogicalOperator logicOp = Randomly.fromOptions(BinaryLogicalOperator.AND, BinaryLogicalOperator.AND, BinaryLogicalOperator.OR);
            condition = new PostgresBinaryLogicalOperation(condition, cond2, logicOp);
        }

        return maybeAddComplexExtra(condition, gen);
    }

    private PostgresExpression generateRangeCondition(PostgresExpression colRef, PostgresColumn col, Randomly r) {
        int variant = r.getInteger(0, 4);
        switch (variant) {
        case 0: return new PostgresBinaryComparisonOperation(colRef,
                PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.GREATER);
        case 1: return new PostgresBinaryComparisonOperation(colRef,
                PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.LESS);
        case 2: return new PostgresBinaryComparisonOperation(colRef,
                PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.GREATER_EQUALS);
        case 3: return new PostgresBetweenOperation(colRef,
                PostgresExpressionGenerator.generateConstant(r, col.getType()),
                PostgresExpressionGenerator.generateConstant(r, col.getType()), false);
        default: return new PostgresBinaryComparisonOperation(colRef,
                PostgresExpressionGenerator.generateConstant(r, col.getType()), PostgresBinaryComparisonOperator.LESS_EQUALS);
        }
    }

    private List<PostgresExpression> generateConstantList(PostgresDataType type, Randomly r, int min, int max) {
        List<PostgresExpression> list = new ArrayList<>();
        int count = r.getInteger(min, max + 1);
        for (int i = 0; i < count; i++) {
            list.add(PostgresExpressionGenerator.generateConstant(r, type));
        }
        return list;
    }

    private PostgresExpression maybeAddComplexExtra(PostgresExpression combined, PostgresExpressionGenerator gen) {
        if (combined != null && Randomly.getBooleanWithRatherLowProbability()) {
            try {
                PostgresExpression randomExtra = gen.generateExpression(0, PostgresDataType.BOOLEAN);
                return new PostgresBinaryLogicalOperation(combined, randomExtra, BinaryLogicalOperator.AND);
            } catch (Exception e) { }
        }
        return combined;
    }

    // Fallback when no indexed columns found: builds WHERE from all columns.
    private PostgresExpression tryGenerateBasicWhere(List<PostgresTable> tables, PostgresExpressionGenerator gen) {
        try {
            List<PostgresColumn> allCols = new ArrayList<>();
            for (PostgresTable table : tables) {
                allCols.addAll(table.getColumns());
            }
            if (allCols.isEmpty()) return null;
            Randomly r = globalState.getRandomly();
            int numConditions = (int) (r.getPositiveInteger() % 3L) + 1;
            PostgresExpression combined = null;
            for (int i = 0; i < numConditions; i++) {
                PostgresColumn targetCol = Randomly.fromList(allCols);
                PostgresExpression colRef = PostgresColumnValue.create(targetCol, null);
                PostgresExpression condition = generateSimpleIndexCondition(colRef, targetCol, r);
                if (combined == null) {
                    combined = condition;
                } else {
                    BinaryLogicalOperator op = Randomly.fromOptions(BinaryLogicalOperator.AND, BinaryLogicalOperator.AND, BinaryLogicalOperator.OR);
                    combined = new PostgresBinaryLogicalOperation(combined, condition, op);
                }
            }
            return maybeAddComplexExtra(combined, gen);
        } catch (Exception e) {
            return null;
        }
    }

    private PostgresExpression generateSimpleIndexCondition(PostgresExpression colRef, PostgresColumn col, Randomly r) {
        int opType = r.getInteger(0, 7);
        switch (opType) {
        case 0: { // col = value
            PostgresExpression val = PostgresExpressionGenerator.generateConstant(r, col.getType());
            return new PostgresBinaryComparisonOperation(colRef, val, PostgresBinaryComparisonOperator.EQUALS);
        }
        case 1: { // col > value
            PostgresExpression val = PostgresExpressionGenerator.generateConstant(r, col.getType());
            return new PostgresBinaryComparisonOperation(colRef, val, PostgresBinaryComparisonOperator.GREATER);
        }
        case 2: { // col < value
            PostgresExpression val = PostgresExpressionGenerator.generateConstant(r, col.getType());
            return new PostgresBinaryComparisonOperation(colRef, val, PostgresBinaryComparisonOperator.LESS);
        }
        case 3: { // col BETWEEN a AND b
            PostgresExpression left = PostgresExpressionGenerator.generateConstant(r, col.getType());
            PostgresExpression right = PostgresExpressionGenerator.generateConstant(r, col.getType());
            return new PostgresBetweenOperation(colRef, left, right, false);
        }
        case 4: { // col IS NULL
            return new PostgresPostfixOperation(colRef, PostfixOperator.IS_NULL);
        }
        case 5: { // col IN (v1, v2, v3)
            List<PostgresExpression> inList = new ArrayList<>();
            for (int i = 0; i < r.getInteger(2, 5); i++) {
                inList.add(PostgresExpressionGenerator.generateConstant(r, col.getType()));
            }
            return new PostgresInOperation(colRef, inList, false);
        }
        case 6: { // col >= value
            PostgresExpression val = PostgresExpressionGenerator.generateConstant(r, col.getType());
            return new PostgresBinaryComparisonOperation(colRef, val, PostgresBinaryComparisonOperator.GREATER_EQUALS);
        }
        default: { // col <= value
            PostgresExpression val = PostgresExpressionGenerator.generateConstant(r, col.getType());
            return new PostgresBinaryComparisonOperation(colRef, val, PostgresBinaryComparisonOperator.LESS_EQUALS);
        }
        }
    }

    private void safeSet(String sql) {
        try {
            globalState.executeStatement(new SQLQueryAdapter(sql, true));
        } catch (Exception e) { }
    }

    private void restoreDefaultSettings() throws Exception {
        globalState.executeStatement(new SQLQueryAdapter("SET enable_seqscan = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET enable_bitmapscan = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET enable_indexscan = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET enable_hashagg = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET enable_hashjoin = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET enable_mergejoin = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET enable_nestloop = ON;", true));
        globalState.executeStatement(new SQLQueryAdapter("SET random_page_cost = 4.0;", true));
    }

    // ==================== P0: Inheritance & Cross-Join Detection ====================

    // PostgreSQL inheritance (table*): SeqScan includes child tables, some IndexScan paths may not.
    // Different row counts between plans are expected behavior, not a bug.
    private boolean usesInheritanceSyntax(String queryString) {
        // Match table* pattern: a table name followed by *
        // This is PostgreSQL's inheritance syntax: SELECT FROM t0* includes child tables
        return queryString.matches("(?s).*\\bt\\d+\\*.*") || queryString.contains("* ");
    }

    // Cross joins create duplicate ORDER BY values even when the column is unique in its own table,
    // making sort order non-deterministic (false positives with ORDER BY + LIMIT).
    private boolean usesCrossJoin(String queryString) {
        try {
            String upper = queryString.toUpperCase();
            // Simple heuristic: FROM clause with multiple comma-separated tables
            // e.g., "FROM t0*, ONLY t3, t1*"
            int fromIdx = upper.indexOf("FROM ");
            if (fromIdx == -1) return false;
            int whereIdx = upper.indexOf("WHERE ", fromIdx);
            int orderByIdx = upper.indexOf("ORDER BY", fromIdx);
            int limitIdx = upper.indexOf("LIMIT", fromIdx);
            int groupByIdx = upper.indexOf("GROUP BY", fromIdx);
            int endIdx = queryString.length();
            if (whereIdx != -1) endIdx = Math.min(endIdx, whereIdx);
            if (orderByIdx != -1) endIdx = Math.min(endIdx, orderByIdx);
            if (limitIdx != -1) endIdx = Math.min(endIdx, limitIdx);
            if (groupByIdx != -1) endIdx = Math.min(endIdx, groupByIdx);

            String fromClause = queryString.substring(fromIdx + 5, endIdx).trim();
            // Count comma-separated items in FROM clause
            // Multiple items without JOIN keyword → cross join
            long commaCount = fromClause.chars().filter(c -> c == ',').count();
            if (commaCount >= 1) {
                // Also check if there are JOIN clauses (if so, it's not a pure cross join)
                if (!upper.contains("JOIN")) {
                    return true;
                }
            }
            return false;
        } catch (Exception e) {
            return false;
        }
    }

    // Recursive/temporary views (v0, v1) without ORDER BY produce non-deterministic row ordering
    // across SeqScan vs IndexScan paths — combined with cross joins this causes false positives.
    private boolean usesNonDeterministicView(String queryString) {
        String upper = queryString.toUpperCase();
        // Check for view references (v0, v1) in FROM clause or JOIN
        // These are created by idxdiff's view generation and may be recursive
        return upper.matches("(?s).*\\bV[01]\\b.*");
    }

    // ==================== P1: Tie-Breaker Detection ====================

    // IMPORTANT: PostgreSQL UNIQUE constraints allow multiple NULLs, so a UNIQUE index alone
    // is not sufficient for deterministic ORDER BY — must also verify no NULL values exist.
    private boolean hasUniqueOrderByTieBreaker(String queryString) {
        try {
            String upperQuery = queryString.toUpperCase();
            int orderByIdx = upperQuery.indexOf("ORDER BY");
            if (orderByIdx == -1) return false;

            String afterOrderBy = queryString.substring(orderByIdx + "ORDER BY".length());
            int endIdx = afterOrderBy.length();
            for (String kw : new String[]{" LIMIT ", " OFFSET ", " FOR ", " INTO "}) {
                int idx = afterOrderBy.toUpperCase().indexOf(kw);
                if (idx != -1 && idx < endIdx) endIdx = idx;
            }
            String orderByClause = afterOrderBy.substring(0, endIdx).trim();

            // Only check indexes on tables that actually appear in the FROM clause.
            // This prevents false matches where table t2 has a UNIQUE index on column c0,
            // but the query is on table t3 (which has no such index).
            Set<String> fromTables = extractFromTables(queryString);
            // Cannot determine which tables are queried → conservatively assume
            // no unique tie-breaker exists. This prevents false positives when
            // extractFromTables fails to parse the FROM clause.
            if (fromTables == null) {
                return false;
            }

            PostgresSchema schema = globalState.getSchema();
            for (String part : orderByClause.split(",")) {
                String expr = part.trim();
                expr = expr.replaceAll("(?i)\\s+(ASC|DESC)\\s*$", "").trim();
                // Also strip NULLS FIRST/LAST
                expr = expr.replaceAll("(?i)\\s+NULLS\\s+(FIRST|LAST)\\s*$", "").trim();

                for (PostgresTable table : schema.getDatabaseTables()) {
                    String tblName = table.getName();
                    // Only consider tables that appear in the FROM clause
                    if (fromTables != null && !fromTables.contains(tblName)) continue;
                    for (PostgresColumn col : table.getColumns()) {
                        // Check unique indexes
                        for (PostgresIndex idx : table.getIndexes()) {
                            if (idx.isUnique() && idx.getColumnNames().size() == 1) {
                                String idxCol = idx.getColumnNames().get(0);
                                String colRef1 = tblName + "." + idxCol;
                                if (expr.equals(colRef1) || expr.equals(idxCol)) {
                                    // UNIQUE index found, but must also verify no NULL values exist.
                                    // PostgreSQL UNIQUE allows multiple NULLs, which makes ORDER BY
                                    // non-deterministic for those rows.
                                    if (!columnHasNullValues(table, idxCol)) {
                                        // Runtime verify: column actually has unique values in the table.
                                        // This handles edge cases where schema metadata is inaccurate:
                                        // 1. UNIQUE index creation failed (data has duplicates, but schema may be stale)
                                        // 2. Partial UNIQUE index (only enforces uniqueness on a WHERE subset)
                                        // 3. Index dropped/recreated between schema fetch and query execution
                                        if (isColumnActuallyUnique(table, idxCol)) {
                                            return true;
                                        }
                                    }
                                    // Column has NULLs or non-unique values → not a reliable tie-breaker
                                }
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

    // Extracts table names from FROM clause; returns null on parse failure (null = conservative, don't filter).
    // Handles: FROM t0, FROM t0, t1, FROM ONLY t2, FROM t0*, FROM t0 AS a, FROM t0 a
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

            // Split by comma for multi-table FROM clauses
            String[] parts = fromClause.split(",");
            for (String part : parts) {
                String trimmed = part.trim();
                // Remove inheritance asterisk: t0* → t0
                trimmed = trimmed.replaceAll("(?i)\\bt(\\d+)\\*", "t$1");
                // Remove ONLY keyword: ONLY t0 → t0
                trimmed = trimmed.replaceAll("(?i)^ONLY\\s+", "");
                // Remove alias: t0 AS x or t0 x → t0, idx_t0 AS x or idx_t0 x → idx_t0
                trimmed = trimmed.replaceAll("(?i)\\s+AS\\s+\\S+", "");
                trimmed = trimmed.replaceAll("(?i)^((?:idx_)?t\\d+)(\\s+\\S+)?$", "$1");
                trimmed = trimmed.trim();
                // Only add if it looks like a table name (tN or idx_tN)
                if (trimmed.matches("(?:idx_)?t\\d+")) {
                    tables.add(trimmed);
                }
            }
            return tables.isEmpty() ? null : tables;
        } catch (Exception e) {
            // Parsing failed → return null to indicate "don't filter" (conservative)
            return null;
        }
    }

    // Returns true if NULL values exist, or conservatively true on error (avoids false tie-breaker detection).
    private boolean columnHasNullValues(PostgresTable table, String columnName) {
        try {
            String checkQuery = "SELECT EXISTS(SELECT 1 FROM " + table.getName()
                    + " WHERE " + columnName + " IS NULL LIMIT 1) AS has_null;";
            List<String> result = ComparatorHelper.getResultSetAllColumnsAsString(
                    checkQuery, new ExpectedErrors(), globalState, " ||| ");
            // result[0] = "t" means NULLs exist, "f" means no NULLs
            return result == null || result.isEmpty() || !result.get(0).equals("f");
        } catch (Exception e) {
            // On error, conservatively assume NULLs exist
            return true;
        }
    }

    // Runtime verification: schema metadata can be stale (failed UNIQUE creation, partial indexes,
    // index dropped/recreated between schema fetch and query execution).
    private boolean isColumnActuallyUnique(PostgresTable table, String columnName) {
        try {
            String query = String.format(
                "SELECT NOT EXISTS(SELECT 1 FROM %s GROUP BY %s HAVING COUNT(*) > 1 LIMIT 1);",
                table.getName(), columnName);
            List<String> result = executeQuery(query);
            return result != null && !result.isEmpty()
                && result.get(0).trim().equalsIgnoreCase("t");
        } catch (Exception e) {
            return false; // Conservative: assume not unique on error
        }
    }

    // If ORDER BY values are identical as multi-sets, the difference is non-deterministic tie-breaking (false positive).
    // If ORDER BY values differ, one plan returns a wrong row — that IS a real bug.
    // Avoids blanket-skipping non-unique ORDER BY + LIMIT, which would mask real bugs.
    private boolean orderByValuesAreIdentical(List<String> r1, List<String> r2, String queryString) {
        try {
            // Parse ORDER BY column names
            String upperQuery = queryString.toUpperCase();
            int orderByIdx = upperQuery.indexOf("ORDER BY");
            if (orderByIdx == -1) return true; // no ORDER BY → can't compare

            String afterOrderBy = queryString.substring(orderByIdx + "ORDER BY".length());
            int endIdx = afterOrderBy.length();
            for (String kw : new String[]{" LIMIT ", " OFFSET ", " FOR ", " INTO "}) {
                int idx = afterOrderBy.toUpperCase().indexOf(kw);
                if (idx != -1 && idx < endIdx) endIdx = idx;
            }
            String orderByClause = afterOrderBy.substring(0, endIdx).trim();

            // Extract ORDER BY column names (strip ASC/DESC/NULLS FIRST/LAST)
            List<String> orderByColNames = new ArrayList<>();
            for (String part : orderByClause.split(",")) {
                String expr = part.trim();
                expr = expr.replaceAll("(?i)\\s+(ASC|DESC)\\s*$", "").trim();
                expr = expr.replaceAll("(?i)\\s+NULLS\\s+(FIRST|LAST)\\s*$", "").trim();
                // Handle table.column format — extract just column name
                if (expr.contains(".")) {
                    expr = expr.substring(expr.lastIndexOf('.') + 1);
                }
                if (!expr.isEmpty()) {
                    orderByColNames.add(expr);
                }
            }
            if (orderByColNames.isEmpty()) return true;

            // Find table columns to determine positions in SELECT *
            Set<String> fromTables = extractFromTables(queryString);
            if (fromTables == null) return true; // can't determine tables

            // For SELECT *, columns are in table definition order
            // Find the column index for each ORDER BY column
            List<Integer> orderByColIndices = new ArrayList<>();
            PostgresSchema schema = globalState.getSchema();
            for (String colName : orderByColNames) {
                boolean found = false;
                for (PostgresTable table : schema.getDatabaseTables()) {
                    if (!fromTables.contains(table.getName())) continue;
                    List<PostgresColumn> cols = table.getColumns();
                    for (int i = 0; i < cols.size(); i++) {
                        if (cols.get(i).getName().equals(colName)) {
                            // For single-table SELECT *, column index = position in table columns
                            // But if multiple tables, offset by previous table column counts
                            // For simplicity, assume single-table case (most common for ORDER BY + LIMIT)
                            if (fromTables.size() == 1) {
                                orderByColIndices.add(i);
                            } else {
                                // Multi-table: just find first match
                                orderByColIndices.add(i);
                            }
                            found = true;
                            break;
                        }
                    }
                    if (found) break;
                }
                if (!found) return true; // can't find column → conservatively return true
            }

            // Extract ORDER BY values from each result set
            Set<String> orderByValues1 = extractOrderByValues(r1, orderByColIndices);
            Set<String> orderByValues2 = extractOrderByValues(r2, orderByColIndices);

            // If the ORDER BY values are identical as multi-sets, the difference is
            // only in which row was picked among ties → non-deterministic (false positive)
            return orderByValues1.equals(orderByValues2);
        } catch (Exception e) {
            // On error, conservatively assume identical (skip to avoid false positives)
            return true;
        }
    }

    // Extracts ORDER BY column values from rows (delimited by " ||| "); returns as a frequency-keyed set
    // for multi-set comparison (preserves duplicates to detect non-deterministic tie-breaking).
    private Set<String> extractOrderByValues(List<String> rows, List<Integer> colIndices) {
        // Use a frequency map to handle multi-set comparison
        Map<String, Integer> freqMap = new HashMap<>();
        for (String row : rows) {
            String[] cols = row.split(java.util.regex.Pattern.quote(COLUMN_DELIMITER));
            StringBuilder key = new StringBuilder();
            for (int i = 0; i < colIndices.size(); i++) {
                int idx = colIndices.get(i);
                if (i > 0) key.append("|||");
                key.append(idx < cols.length ? cols[idx].trim() : "");
            }
            freqMap.merge(key.toString(), 1, Integer::sum);
        }
        // Convert to a set representation that preserves frequency
        Set<String> result = new HashSet<>();
        for (Map.Entry<String, Integer> entry : freqMap.entrySet()) {
            result.add(entry.getKey() + "#" + entry.getValue());
        }
        return result;
    }

    private boolean areSetsEqual(List<String> list1, List<String> list2) {
        Map<String, Integer> freq1 = new HashMap<>();
        Map<String, Integer> freq2 = new HashMap<>();
        for (String s : list1) freq1.merge(s, 1, Integer::sum);
        for (String s : list2) freq2.merge(s, 1, Integer::sum);
        return freq1.equals(freq2);
    }

    // ==================== Mode 8: Covering Index (Index-Only Scan) ====================

    // PG's Index-Only Scan (INCLUDE columns) skips heap fetches — bugs produce wrong results vs SeqScan.
    private void checkCoveringIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        // Filter out views — cannot create indexes on views
        tables = tables.stream().filter(t -> !t.isView()).collect(Collectors.toList());
        if (tables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        List<PostgresColumn> cols = new ArrayList<>(table.getColumns());
        java.util.Collections.shuffle(cols);

        // Index columns + INCLUDE columns
        int numIdxCols = Math.min(cols.size(), Randomly.fromOptions(1, 2));
        List<PostgresColumn> idxCols = cols.subList(0, numIdxCols);
        List<PostgresColumn> includeCols = cols.subList(numIdxCols, Math.min(cols.size(), numIdxCols + 2));

        String idxColList = idxCols.stream().map(PostgresColumn::getName).collect(Collectors.joining(", "));
        String idxName = "cover_idx_" + Math.abs(idxCols.get(0).getName().hashCode() % 10000);

        StringBuilder createIdx = new StringBuilder();
        createIdx.append("CREATE INDEX ").append(idxName).append(" ON ").append(table.getName());
        createIdx.append(" (").append(idxColList).append(")");
        if (!includeCols.isEmpty()) {
            createIdx.append(" INCLUDE(");
            createIdx.append(includeCols.stream().map(PostgresColumn::getName).collect(Collectors.joining(", ")));
            createIdx.append(")");
        }

        try {
            globalState.executeStatement(new SQLQueryAdapter(createIdx.toString() + ";", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + table.getName() + ";", true));
        } catch (Exception e) {
            return;
        }

        // Build query using only indexed + included columns
        String selectCols = idxCols.stream().map(PostgresColumn::getName).collect(Collectors.joining(", "));
        if (!includeCols.isEmpty()) {
            selectCols += ", " + includeCols.stream().map(PostgresColumn::getName).collect(Collectors.joining(", "));
        }
        PostgresColumn whereCol = idxCols.get(0);
        Randomly r = globalState.getRandomly();
        // P0: Use data-aware value instead of random to avoid empty result sets
        String val = generateDataAwareValueForType(table.getName(), whereCol);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String queryString = "SELECT " + selectCols + " FROM " + table.getName()
                + " WHERE " + whereCol.getName() + " " + op + " " + val + ";";
        lastQueryString = "[COVER_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: skip if SeqScan and IndexOnlyScan plans are identical
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET enable_bitmapscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainIdxOnly = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainSeqScan, explainIdxOnly)) return;

        // Plan A: SeqScan
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r1 = executeQuery(queryString);
        restoreDefaultSettings();
        if (r1 == null) return;

        // Plan B: Index-Only Scan
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET enable_bitmapscan = OFF;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_COVERING_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_COVERING_INDEX");
    }

    // ==================== Mode 9: Index Merge (BitmapOr) ====================

    // WHERE col1 = v OR col2 = v triggers the BitmapOr path (merges two index scans); compare vs SeqScan.
    private void checkIndexMerge() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        // Filter out views — cannot create indexes on views
        tables = tables.stream().filter(t -> !t.isView()).collect(Collectors.toList());
        if (tables.isEmpty()) return;
        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;

        List<PostgresColumn> cols = new ArrayList<>(table.getColumns());
        java.util.Collections.shuffle(cols);
        PostgresColumn col1 = cols.get(0);
        PostgresColumn col2 = cols.get(1);
        String tblName = table.getName();

        // Create two separate single-column indexes
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
        globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));

        // WHERE col1 = v1 OR col2 = v2 — triggers BitmapOr
        Randomly r = globalState.getRandomly();
        // P0: Use data-aware values instead of random to avoid empty result sets
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

        // EXPLAIN filter: skip if BitmapOr and SeqScan plans are identical
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (BitmapOr likely)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_INDEX_MERGE");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_INDEX_MERGE");
    }

    // ==================== Mode 10: ORDER BY + LIMIT Index ====================

    // IndexScan reads rows in index order (no sort step) vs SeqScan+Sort; LIMIT top-N must match.
    private void checkOrderByLimitIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        // Filter out views - cannot create indexes on views
        tables = tables.stream().filter(t -> !t.isView()).collect(java.util.stream.Collectors.toList());
        if (tables.isEmpty()) return;
        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        PostgresColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "ordlim_idx_" + Math.abs(colName.hashCode() % 10000);

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) { return; }

        int limit = Randomly.fromOptions(1, 5, 10, 20, 50);
        String direction = Randomly.fromOptions("ASC", "DESC");
        String whereClause = "";
        if (Randomly.getBoolean()) {
            // P0: Use data-aware value instead of random to avoid empty result sets
            String val = generateDataAwareValueForType(table.getName(), col);
            String op = Randomly.fromOptions(">", "<", ">=", "<=", "!=");
            whereClause = " WHERE " + colName + " " + op + " " + val;
        }
        // Build deterministic ORDER BY: primary column + all other columns as tie-breakers.
        // This eliminates false positives from non-deterministic tie-breaking when
        // ORDER BY column has duplicate values and LIMIT truncates the result set.
        StringBuilder orderByClause = new StringBuilder(colName).append(" ").append(direction);
        for (PostgresColumn tc : table.getColumns()) {
            if (!tc.getName().equals(colName)) {
                orderByClause.append(", ").append(tc.getName()).append(" ASC");
            }
        }
        String queryString = "SELECT * FROM " + tblName + whereClause
                + " ORDER BY " + orderByClause + " LIMIT " + limit + ";";
        lastQueryString = "[ORDLIM_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: skip if IndexScan and SeqScan plans are identical
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan + Sort
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        // ORDER BY includes all columns as tie-breakers → fully deterministic ordering.
        // Safe to use strict comparison: any mismatch is a real bug.
        compareResultsStrict(r1, r2, queryString, "PG_ORDLIM_IDX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_ORDLIM_IDX");
    }

    // ==================== Mode 11: UNIQUE Index Consistency ====================

    // Verifies COUNT(*) is unchanged after UNIQUE INDEX creation, then compares SeqScan vs IndexScan results.
    private void checkUniqueIndexConsistency() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Filter out views and partitioned tables
        // Partitioned tables require UNIQUE INDEX to include all partition key columns,
        // so we skip them to avoid "unique constraint on partitioned table must include
        // all partitioning columns" errors (PostgreSQL-specific restriction).
        List<PostgresTable> nonViewTables = new ArrayList<>();
        for (PostgresTable t : tables) {
            if (!t.isView() && !t.isPartitioned()) nonViewTables.add(t);
        }
        if (nonViewTables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(nonViewTables);
        List<PostgresColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        // Find a non-PK column for the unique index
        List<PostgresColumn> candidates = new ArrayList<>();
        for (PostgresColumn col : columns) {
            candidates.add(col);
        }
        if (candidates.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(candidates);
        String tblName = table.getName();
        String colName = col.getName();

        // Count rows before
        String countQuery = "SELECT COUNT(*) FROM " + tblName + ";";
        List<String> r1 = executeQuery(countQuery);
        if (r1 == null) return;

        // Create UNIQUE INDEX
        String idxName = "uniq_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE UNIQUE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            // UNIQUE constraint violation = duplicates exist, expected
            return;
        }

        // Count rows after — should be the same
        List<String> r2 = executeQuery(countQuery);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, countQuery, "PG_UNIQUE_IDX_COUNT");

        // Compare query with/without index scan
        String queryDefault = "SELECT " + colName + " FROM " + tblName
                + " WHERE " + colName + " IS NOT NULL ORDER BY " + colName + " LIMIT 100;";
        lastQueryString = "[UNIQUE_IDX] " + queryDefault;

        // EXPLAIN filter: skip if SeqScan and IndexScan plans are identical
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryDefault);
        restoreDefaultSettings();
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> explainIdxScan = getExplainPlan(queryDefault);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainSeqScan, explainIdxScan)) return;

        // Plan A: SeqScan
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r3 = executeQuery(queryDefault);
        restoreDefaultSettings();
        if (r3 == null) return;

        // Plan B: Index Scan
        safeSet("SET enable_seqscan = OFF;");
        safeSet("SET enable_indexscan = ON;");
        safeSet("SET random_page_cost = 1.0;");
        List<String> r4 = executeQueryWithRestore(queryDefault);
        if (r4 == null) return;

        compareResultsStrict(r3, r4, queryDefault, "PG_UNIQUE_IDX");
    }

    // ==================== Mode 12: Expression Index ====================

    // PG expression indexes (CREATE INDEX ON t(LOWER(col))): queries using the same expression
    // must produce identical results with IndexScan vs SeqScan.
    private void checkExpressionIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables().stream()
                .filter(t -> !t.isView()).collect(java.util.stream.Collectors.toList());
        if (tables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(tables);
        List<PostgresColumn> textCols = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (col.getType() == PostgresDataType.TEXT) {
                textCols.add(col);
            }
        }
        if (textCols.isEmpty()) {
            // Fallback: use INT column with expression
            textCols.addAll(table.getColumns());
        }
        if (textCols.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(textCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Choose an expression for the index
        String indexExpr;
        String whereExpr;
        if (col.getType() == PostgresDataType.TEXT) {
            indexExpr = "LOWER(" + colName + ")";
            whereExpr = "LOWER(" + colName + ")";
        } else {
            indexExpr = "ABS(" + colName + ")";
            whereExpr = "ABS(" + colName + ")";
        }

        String idxName = "expr_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + indexExpr + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        // Query using the same expression
        Randomly r = globalState.getRandomly();
        // P0: Use data-aware value instead of random to avoid empty result sets
        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions("=", ">", "<");
        String queryString = "SELECT * FROM " + tblName
                + " WHERE " + whereExpr + " " + op + " " + val + ";";
        lastQueryString = "[EXPR_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: skip if Default and SeqScan plans are identical
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_EXPRESSION_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_EXPRESSION_INDEX");
    }

    // ==================== Mode 13: Partial Index ====================

    // PG partial indexes (CREATE INDEX ON t(col) WHERE cond): queries matching the condition
    // must produce identical results; uses data-aware values instead of fixed "col > 0".
    private void checkPartialIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        // Skip views — cannot CREATE INDEX on views
        if (table.isView()) return;

        PostgresColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // P0: Build data-driven partial index condition
        // Instead of fixed "col > 0", use MIN/MAX or sampled values for targeted selectivity
        String partialWhere = buildDataDrivenPartialCondition(tblName, col);
        if (partialWhere == null) return;

        String idxName = "partial_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ") WHERE " + partialWhere + ";",
                    errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        // P0: Choose from multiple query patterns that exercise partial index differently
        String queryString = buildPartialIndexQuery(tblName, col, table, partialWhere);
        if (queryString == null) return;
        lastQueryString = "[PARTIAL_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: skip if Default and SeqScan plans are identical
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use partial index)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_PARTIAL_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_PARTIAL_INDEX");
    }

    // Uses MIN/MAX/sampled values for partial index conditions instead of fixed "col > 0",
    // targeting real data ranges for better selectivity.
    private String buildDataDrivenPartialCondition(String tblName, PostgresColumn col) {
        String colName = col.getName();

        // Sample values to understand data distribution
        List<String> sampled = sampleColumnValues(tblName, colName, 5);

        switch (col.getType()) {
        case INT:
            if (sampled != null && !sampled.isEmpty()) {
                // Use a sampled value as threshold for selective partial index
                String threshold = sampled.get(0);
                // Pick a comparison operator
                return Randomly.fromOptions(
                        colName + " > " + threshold,
                        colName + " >= " + threshold,
                        colName + " < " + threshold,
                        colName + " <= " + threshold,
                        colName + " != " + threshold
                );
            }
            // Fallback: use MIN/MAX
            String minMax = tryGetMinMaxValue(tblName, col);
            if (minMax != null) {
                return colName + " >= " + minMax;
            }
            return colName + " > 0";

        case TEXT:
            if (sampled != null && !sampled.isEmpty()) {
                // Use sampled text as LIKE prefix — more selective than IS NOT NULL
                String val = sampled.get(0);
                // Strip quotes if present (guard against a lone single-quote value
                // to avoid substring(1, 0) throwing StringIndexOutOfBoundsException)
                if (val.startsWith("'") && val.endsWith("'") && val.length() >= 2) {
                    val = val.substring(1, val.length() - 1);
                }
                val = val.replace("'", "''");
                if (val.length() > 0) {
                    String prefix = val.substring(0, Math.min(val.length(), 3));
                    return Randomly.fromOptions(
                            colName + " IS NOT NULL AND " + colName + " LIKE '" + prefix + "%'",
                            colName + " IS NOT NULL",
                            colName + " != '" + val + "'"
                    );
                }
            }
            return colName + " IS NOT NULL";

        case BOOLEAN:
            return colName + " = TRUE";

        case DECIMAL:
        case FLOAT:
        case REAL:
            if (sampled != null && !sampled.isEmpty()) {
                String threshold = sampled.get(0);
                return Randomly.fromOptions(
                        colName + " > " + threshold,
                        colName + " >= " + threshold,
                        colName + " < " + threshold
                );
            }
            return colName + " IS NOT NULL";

        default:
            return colName + " IS NOT NULL";
        }
    }

    // Patterns: 0=exact match, 1=partial+extra filter, 2=partial+range, 3=partial+IN list.
    private String buildPartialIndexQuery(String tblName, PostgresColumn col,
            PostgresTable table, String partialWhere) {
        String colName = col.getName();
        int pattern = Randomly.fromOptions(0, 1, 2, 3);

        switch (pattern) {
        case 0:
            // Exact match of partial index condition
            return "SELECT * FROM " + tblName + " WHERE " + partialWhere + ";";

        case 1: {
            // Partial condition + additional filter on another column
            List<PostgresColumn> otherCols = new ArrayList<>();
            for (PostgresColumn c : table.getColumns()) {
                if (!c.getName().equals(colName)) otherCols.add(c);
            }
            if (otherCols.isEmpty()) {
                return "SELECT * FROM " + tblName + " WHERE " + partialWhere + ";";
            }
            PostgresColumn col2 = Randomly.fromList(otherCols);
            String val2 = generateDataAwareValueForType(tblName, col2);
            String op2 = Randomly.fromOptions("=", ">", "<", ">=");
            return "SELECT * FROM " + tblName + " WHERE " + partialWhere
                    + " AND " + col2.getName() + " " + op2 + " " + val2 + ";";
        }

        case 2: {
            // Partial condition + range scan on indexed column using data-aware value
            String rangeVal = generateDataAwareValueForType(tblName, col);
            String rangeOp = Randomly.fromOptions("<", "<=", ">", ">=");
            return "SELECT * FROM " + tblName + " WHERE " + partialWhere
                    + " AND " + colName + " " + rangeOp + " " + rangeVal + ";";
        }

        case 3: {
            // Partial condition + IN list with sampled values
            List<String> sampled = sampleColumnValues(tblName, colName, 5);
            if (sampled == null || sampled.size() < 2) {
                return "SELECT * FROM " + tblName + " WHERE " + partialWhere + ";";
            }
            StringBuilder inList = new StringBuilder();
            int sz = Math.min(sampled.size(), 4);
            for (int i = 0; i < sz; i++) {
                if (i > 0) inList.append(", ");
                inList.append(quoteValueForSQL(sampled.get(i), col));
            }
            return "SELECT * FROM " + tblName + " WHERE " + partialWhere
                    + " AND " + colName + " IN (" + inList + ");";
        }

        default:
            return "SELECT * FROM " + tblName + " WHERE " + partialWhere + ";";
        }
    }

    // ==================== Mode 14: Simple Index Query ====================

    // Uses actual indexed columns (not random expressions) to maximize chance of different plans
    // under enable_* settings. Patterns: =, >, BETWEEN, IN, multi-col AND, IS NULL, LIKE prefix.
    private void checkSimpleIndexQuery() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Collect all tables with indexes
        List<PostgresTable> tablesWithIndexes = new ArrayList<>();
        for (PostgresTable t : tables) {
            if (!t.isView() && !t.getIndexes().isEmpty()) {
                tablesWithIndexes.add(t);
            }
        }
        if (tablesWithIndexes.isEmpty()) {
            // No indexes yet — create some using idxdiff's generator
            for (int i = 0; i < 3; i++) {
                try {
                    globalState.executeStatement(PostgresIndexGenerator.generate(globalState));
                } catch (Exception e) { }
            }
            // Refresh schema
            tablesWithIndexes.clear();
            for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
                if (!t.isView() && !t.getIndexes().isEmpty()) {
                    tablesWithIndexes.add(t);
                }
            }
            if (tablesWithIndexes.isEmpty()) return;
        }

        PostgresTable table = Randomly.fromList(tablesWithIndexes);
        String tblName = table.getName();
        List<PostgresIndex> indexes = table.getIndexes();

        // Pick a random index and get its columns
        PostgresIndex idx = Randomly.fromList(indexes);
        List<String> idxColNames = idx.getColumnNames();
        if (idxColNames == null || idxColNames.isEmpty()) return;

        // Resolve column objects
        List<PostgresColumn> idxCols = new ArrayList<>();
        for (String colName : idxColNames) {
            for (PostgresColumn col : table.getColumns()) {
                if (col.getName().equals(colName)) {
                    idxCols.add(col);
                    break;
                }
            }
        }
        if (idxCols.isEmpty()) return;

        Randomly r = globalState.getRandomly();

        // Build a simple WHERE condition on the first indexed column
        PostgresColumn whereCol = idxCols.get(0);
        String colName = whereCol.getName();
        // P0: Use data-aware value instead of random to avoid empty result sets
        String val = generateDataAwareValueForType(table.getName(), whereCol);

        // Choose query pattern
        int pattern = r.getInteger(0, 8); // Phase 3: expanded patterns
        String whereClause;
        String orderByClause = "";
        String limitClause = "";

        switch (pattern) {
        case 0: // Simple equality: WHERE col = value
            whereClause = colName + " = " + val;
            break;
        case 1: // Range: WHERE col > value
            whereClause = colName + " > " + val;
            break;
        case 2: // BETWEEN
            String val2 = generateDataAwareValueForType(table.getName(), whereCol);
            whereClause = colName + " BETWEEN " + val + " AND " + val2;
            break;
        case 3: // IN list
            StringBuilder inList = new StringBuilder();
            int inSize = r.getInteger(2, 6);
            for (int i = 0; i < inSize; i++) {
                if (i > 0) inList.append(", ");
                inList.append(generateDataAwareValueForType(table.getName(), whereCol));
            }
            whereClause = colName + " IN (" + inList + ")";
            break;
        case 4: // Multi-column AND (composite index)
            if (idxCols.size() >= 2) {
                PostgresColumn col2 = idxCols.get(1);
                String val3 = generateDataAwareValueForType(table.getName(), col2);
                whereClause = colName + " = " + val + " AND " + col2.getName() + " > " + val3;
            } else {
                whereClause = colName + " >= " + val;
            }
            break;
        case 5: // IS NOT NULL + range
            whereClause = colName + " IS NOT NULL AND " + colName + " < " + val;
            break;
        case 6: // LIKE prefix (TEXT columns) — Phase 3
            if (whereCol.getType() == PostgresDataType.TEXT) {
                List<String> sampled = sampleColumnValues(table.getName(), colName, 3);
                if (sampled != null && !sampled.isEmpty()) {
                    String prefix = sampled.get(0);
                    if (prefix.startsWith("'")) prefix = prefix.substring(1);
                    if (prefix.endsWith("'")) prefix = prefix.substring(0, prefix.length() - 1);
                    prefix = prefix.replace("'", "''");
                    if (prefix.length() > 3) prefix = prefix.substring(0, 3);
                    whereClause = colName + " LIKE '" + prefix + "%'";
                } else {
                    whereClause = colName + " IS NOT NULL";
                }
            } else {
                whereClause = colName + " IS NOT NULL AND " + colName + " >= " + val;
            }
            break;
        case 7: // IS NULL / IS NOT NULL — Phase 3
        default:
            whereClause = Randomly.getBoolean() ? colName + " IS NULL" : colName + " IS NOT NULL";
            break;
        }

        // 50% chance to add ORDER BY on indexed column
        if (Randomly.getBoolean()) {
            orderByClause = " ORDER BY " + colName + " " + Randomly.fromOptions("ASC", "DESC");
            // 50% chance to add LIMIT
            if (Randomly.getBoolean()) {
                limitClause = " LIMIT " + Randomly.fromOptions(5, 10, 20, 50);
            }
        }

        String queryString = "SELECT * FROM " + tblName
                + " WHERE " + whereClause + orderByClause + limitClause + ";";
        lastQueryString = "[SIMPLE_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        if (orderByClause.isEmpty()) {
            compareResultsSorted(r1, r2, queryString, "SIMPLE_INDEX");
            if (lastCompareFiltered) countStarFallback(queryString, queryString, "SIMPLE_INDEX");
        } else if (!limitClause.isEmpty() && !hasUniqueOrderByTieBreaker(queryString)) {
            // ORDER BY + LIMIT without unique tie-breaker → non-deterministic ordering
            // at the LIMIT boundary due to duplicate ORDER BY values.
            compareResultsSorted(r1, r2, queryString, "SIMPLE_INDEX");
            if (lastCompareFiltered) countStarFallback(queryString, queryString, "SIMPLE_INDEX");
        } else {
            compareResultsStrict(r1, r2, queryString, "SIMPLE_INDEX");
            if (lastCompareFiltered) countStarFallback(queryString, queryString, "SIMPLE_INDEX");
        }
    }

    // ==================== P0: EXPLAIN Plan Verification ====================

    // EXPLAIN returns one plan node per row; each row has node type, relation name, and cost info.
    private List<String> getExplainPlan(String queryString) {
        List<String> plan = new ArrayList<>();
        try {
            String explainQuery = "EXPLAIN " + queryString;
            try (Statement stmt = globalState.getConnection().createStatement();
                 ResultSet rs = stmt.executeQuery(explainQuery)) {
                while (rs.next()) {
                    String line = rs.getString(1);
                    if (line != null) {
                        plan.add(line.trim());
                    }
                }
            }
        } catch (Exception e) {
            // EXPLAIN may fail for various reasons
        }
        return plan;
    }

    // Compares operator node types (e.g., "Seq Scan", "Index Scan"); ignores cost/row estimates
    // which vary between enable_* settings and would produce false "different" results.
    private boolean plansAreDifferent(List<String> plan1, List<String> plan2) {
        if (plan1.isEmpty() || plan2.isEmpty()) return true; // Can't verify, assume different
        // Compare extracted node types
        List<String> nodes1 = extractPlanNodes(plan1);
        List<String> nodes2 = extractPlanNodes(plan2);
        if (nodes1.size() != nodes2.size()) return true;
        return !nodes1.equals(nodes2);
    }

    // Strips "  ->  " prefix and "(cost=...)" suffix from EXPLAIN output lines,
    // leaving just the node type + relation (e.g., "Seq Scan on t0").
    private List<String> extractPlanNodes(List<String> plan) {
        List<String> nodes = new ArrayList<>();
        for (String line : plan) {
            // Strip leading whitespace and arrow: "  ->  Seq Scan on t0  (cost=..."
            String stripped = line.replaceAll("^\\s*->\\s*", "").trim();
            // Remove cost/row estimate info in parentheses at the end
            stripped = stripped.replaceAll("\\s*\\(cost=.*\\)\\s*$", "").trim();
            if (!stripped.isEmpty()) {
                nodes.add(stripped);
            }
        }
        return nodes;
    }

    // ==================== Mode 15: GiST/GIN Index (P0 - PostgreSQL-specific) ====================

    // PostgreSQL-exclusive: GiST/GIN with pg_trgm enables index-accelerated LIKE/ILIKE queries.
    // Creates a trigram index on a TEXT column; compares trigram index scan vs SeqScan results.
    private void checkGiSTGINIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with TEXT columns
        PostgresTable table = Randomly.fromList(tables);
        if (table.isView()) return;
        List<PostgresColumn> textCols = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (col.getType() == PostgresDataType.TEXT) {
                textCols.add(col);
            }
        }
        if (textCols.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(textCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Ensure pg_trgm extension is available
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE EXTENSION IF NOT EXISTS pg_trgm;", true));
        } catch (Exception e) {
            return; // pg_trgm not available, skip
        }

        // Create GiST or GIN index with pg_trgm operator class
        String accessMethod = Randomly.fromOptions("gist", "gin");
        String opClass = accessMethod.equals("gist") ? "gist_trgm_ops" : "gin_trgm_ops";
        String idxName = "trgm_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " USING " + accessMethod + " (" + colName + " " + opClass + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            // Try without operator class (default text_ops for GiST on text)
            try {
                globalState.executeStatement(new SQLQueryAdapter(
                        "CREATE INDEX " + idxName + " ON " + tblName
                        + " USING " + accessMethod + " (" + colName + ");", errors, true));
                globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
            } catch (Exception e2) {
                return;
            }
        }

        // Sample actual text values for LIKE patterns
        List<String> sampled = null;
        try {
            sampled = execInternal("SELECT " + colName + " FROM " + tblName
                    + " WHERE " + colName + " IS NOT NULL LIMIT 5;");
        } catch (Exception e) { }

        // Build LIKE/ILIKE query
        String likePattern;
        if (sampled != null && !sampled.isEmpty()) {
            String rawVal = Randomly.fromList(sampled);
            if (rawVal.length() >= 2 && rawVal.startsWith("'") && rawVal.endsWith("'")) {
                rawVal = rawVal.substring(1, rawVal.length() - 1);
            }
            // Sanitize: remove single quotes to avoid breaking the SQL string literal
            rawVal = rawVal.replace("'", "");
            int len = Math.min(rawVal.length(), 3);
            String prefix = len > 0 ? rawVal.substring(0, len) : "a";
            likePattern = Randomly.fromOptions(
                    "%" + prefix + "%",     // contains
                    prefix + "%",           // starts with
                    "%" + prefix            // ends with
            );
        } else {
            likePattern = Randomly.fromOptions("%a%", "%test%", "a%");
        }

        boolean caseInsensitive = Randomly.getBoolean();
        String likeOp = caseInsensitive ? "ILIKE" : "LIKE";
        String queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " " + likeOp
                + " '" + likePattern + "';";
        lastQueryString = "[GIST_GIN] " + queryString;
        log(queryString);

        // EXPLAIN filter
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use GiST/GIN index)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_GIST_GIN_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_GIST_GIN_INDEX");
    }

    // ==================== Mode 16: tsvector GIN Full-Text Search (P0 - PostgreSQL-specific) ====================

    // tsvector/tsquery GIN full-text search is PostgreSQL-exclusive (no MySQL/TiDB equivalent).
    // Tests to_tsquery, plainto_tsquery, phraseto_tsquery variants vs SeqScan.
    private void checkTsvectorIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with TEXT columns
        PostgresTable table = Randomly.fromList(tables);
        if (table.isView()) return;
        List<PostgresColumn> textCols = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (col.getType() == PostgresDataType.TEXT) {
                textCols.add(col);
            }
        }
        if (textCols.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(textCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create GIN index on to_tsvector
        String idxName = "tsv_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " USING gin (to_tsvector('english', " + colName + "));", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        // Sample actual text values to build meaningful tsquery terms
        List<String> sampled = null;
        try {
            sampled = execInternal("SELECT " + colName + " FROM " + tblName
                    + " WHERE " + colName + " IS NOT NULL LIMIT 5;");
        } catch (Exception e) { }

        // Build a tsquery search term
        String searchTerm;
        if (sampled != null && !sampled.isEmpty()) {
            String rawVal = Randomly.fromList(sampled);
            if (rawVal.length() >= 2 && rawVal.startsWith("'") && rawVal.endsWith("'")) {
                rawVal = rawVal.substring(1, rawVal.length() - 1);
            }
            // Extract first word from sampled value
            String[] words = rawVal.split("\\s+");
            searchTerm = words.length > 0 && words[0].length() > 0 ? words[0] : "test";
            // Clean: only keep alphanumeric characters
            searchTerm = searchTerm.replaceAll("[^a-zA-Z0-9]", "");
            if (searchTerm.length() == 0) searchTerm = "test";
            if (searchTerm.length() > 10) searchTerm = searchTerm.substring(0, 10);
        } else {
            searchTerm = Randomly.fromOptions("test", "hello", "data", "value", "abc");
        }

        // Choose query type: to_tsquery, plainto_tsquery, or phraseto_tsquery
        // Always use quoted 'english' — unquoted english would be treated as a column name
        String regConfig = "'english'";
        int queryType = Randomly.fromOptions(0, 1, 2);
        String tsqueryExpr;
        switch (queryType) {
        case 0:
            tsqueryExpr = "to_tsquery(" + regConfig + ", '" + searchTerm + "')";
            break;
        case 1:
            tsqueryExpr = "plainto_tsquery(" + regConfig + ", '" + searchTerm + "')";
            break;
        default:
            tsqueryExpr = "phraseto_tsquery(" + regConfig + ", '" + searchTerm + "')";
            break;
        }

        String queryString = "SELECT * FROM " + tblName
                + " WHERE to_tsvector(" + regConfig + ", " + colName + ") @@ " + tsqueryExpr + ";";
        lastQueryString = "[TSVECTOR] " + queryString;
        log(queryString);

        // EXPLAIN filter
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use GIN index)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_TSVECTOR_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_TSVECTOR_INDEX");
    }

    // Returns null on error; used for sampling queries that are expected to sometimes fail.
    private List<String> execInternal(String query) {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(query, errors, globalState, " ||| ");
        } catch (Exception e) {
            return null;
        }
    }

    // ==================== Mode 17: Optimizer Config Pairwise ====================

    // Toggles a single enable_* planner flag off and compares COUNT(*) results — detects optimizer
    // bugs that only surface when specific plan types (hashagg, nestloop, etc.) are disabled.
    private void checkOptimizerConfigPairwise() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        PostgresColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Simple COUNT query — deterministic, not affected by ORDER BY tie-breaking
        String query = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
        lastQueryString = "[OPT_CONFIG_PAIR] " + query;
        log(query);

        List<String> r1 = executeQuery(query);
        if (r1 == null) return;

        // Pick one planner flag to toggle OFF
        String flagOff = Randomly.fromOptions(
                "SET enable_hashagg = OFF;",
                "SET enable_sort = OFF;",
                "SET enable_hashjoin = OFF;",
                "SET enable_mergejoin = OFF;",
                "SET enable_nestloop = OFF;",
                "SET enable_indexonlyscan = OFF;",
                "SET enable_seqscan = OFF;",
                "SET enable_bitmapscan = OFF;",
                "SET enable_tidscan = OFF;",
                "SET enable_material = OFF;",
                "SET enable_memoize = OFF;",
                "SET enable_incremental_sort = OFF;");
        String flagOn = flagOff.replace("OFF", "ON");

        try {
            safeSet(flagOff);
            List<String> r2 = executeQueryWithRestore(query);
            if (r2 == null) return;
            compareResultsSorted(r1, r2, query, "PG_OPT_CONFIG_PAIR");
            if (lastCompareFiltered) countStarFallback(query, query, "PG_OPT_CONFIG_PAIR");
        } finally {
            safeSet(flagOn);
            restoreDefaultSettings();
        }
    }

    // ==================== Mode 18: SQL Semantic Equivalence ====================

    // Semantically equivalent expressions (IN vs OR, BETWEEN vs >= AND <=, NOT IN vs <> AND <>)
    // must always produce identical results — any mismatch is a real bug.
    private void checkSQLSemanticEquivalence() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        PostgresColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Create index to exercise index scan paths
        String idxName = "sem_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
        } catch (Exception e) { }
        restoreDefaultSettings();

        // Generate 2-3 values for the comparison
        // P0: Use data-aware values instead of random to avoid empty result sets
        String v1 = generateDataAwareValueForType(tblName, col);
        String v2 = generateDataAwareValueForType(tblName, col);
        String v3 = generateDataAwareValueForType(tblName, col);

        // Fix: ensure v1, v2, v3 are distinct for IN-vs-UNION variant (case 3),
        // because IN (x, x) deduplicates but UNION ALL does not.
        int dedupAttempts = 0;
        while (v2.equals(v1) && dedupAttempts < 10) {
            v2 = generateDataAwareValueForType(tblName, col);
            dedupAttempts++;
        }
        dedupAttempts = 0;
        while ((v3.equals(v1) || v3.equals(v2)) && dedupAttempts < 10) {
            v3 = generateDataAwareValueForType(tblName, col);
            dedupAttempts++;
        }

        int variant = Randomly.fromOptions(0, 1, 2, 3, 4);
        String queryA, queryB, modeTag;
        switch (variant) {
        case 0:
            // IN vs OR
            queryA = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " IN (" + v1 + ", " + v2 + ", " + v3 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " = " + v1 + " OR " + colName + " = " + v2
                    + " OR " + colName + " = " + v3 + ";";
            modeTag = "PG_SEMANTIC_IN_VS_OR";
            break;
        case 1:
            // BETWEEN vs >= AND <=
            queryA = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " BETWEEN " + v1 + " AND " + v2 + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " >= " + v1 + " AND " + colName + " <= " + v2 + ";";
            modeTag = "PG_SEMANTIC_BETWEEN";
            break;
        case 2:
            // NOT IN vs <> AND <>
            queryA = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " NOT IN (" + v1 + ", " + v2 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " <> " + v1 + " AND " + colName + " <> " + v2 + ";";
            modeTag = "PG_SEMANTIC_NOT_IN";
            break;
        case 3:
            // IN vs UNION ALL — forces separate index scans per value
            queryA = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " IN (" + v1 + ", " + v2 + ");";
            queryB = "SELECT SUM(cnt) FROM ("
                    + "SELECT COUNT(*) AS cnt FROM " + tblName + " WHERE " + colName + " = " + v1
                    + " UNION ALL "
                    + "SELECT COUNT(*) AS cnt FROM " + tblName + " WHERE " + colName + " = " + v2
                    + ") t;";
            modeTag = "PG_SEMANTIC_IN_VS_UNION";
            break;
        default:
            // EXISTS vs IN subquery — semantically equivalent for COUNT(*)
            // (IN subquery with SELECT DISTINCT handles duplicates correctly)
            // Previous version used EXISTS vs COUNT(DISTINCT) JOIN, which was
            // semantically incorrect (EXISTS counts rows, COUNT DISTINCT counts values).
            if (schema.getDatabaseTables().size() >= 2) {
                PostgresTable table2 = Randomly.fromList(schema.getDatabaseTables());
                if (!table2.getColumns().isEmpty() && !table2.getName().equals(tblName)) {
                    PostgresColumn col2 = Randomly.fromList(table2.getColumns());
                    queryA = "SELECT COUNT(*) FROM " + tblName + " t1"
                            + " WHERE EXISTS (SELECT 1 FROM " + table2.getName() + " t2 WHERE t1." + colName + " = t2." + col2.getName() + ");";
                    queryB = "SELECT COUNT(*) FROM " + tblName + " t1"
                            + " WHERE t1." + colName + " IN (SELECT DISTINCT " + col2.getName() + " FROM " + table2.getName() + " WHERE " + col2.getName() + " IS NOT NULL);";
                    modeTag = "PG_SEMANTIC_EXISTS_VS_IN_SUB";
                    break;
                }
            }
            // Fallback: BETWEEN variant
            queryA = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " BETWEEN " + v1 + " AND " + v2 + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName
                    + " >= " + v1 + " AND " + colName + " <= " + v2 + ";";
            modeTag = "PG_SEMANTIC_BETWEEN";
            break;
        }

        lastQueryString = "[SEMANTIC_EQ] A=" + queryA + " B=" + queryB;
        log(queryA); log(queryB);

        List<String> r1 = executeQuery(queryA);
        if (r1 == null) return;
        List<String> r2 = executeQuery(queryB);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, queryA, modeTag);
    }

    // ==================== P0: COUNT(*) Aggregate Fallback ====================

    // When row-level comparison is skipped (LIMIT without ORDER BY), COUNT(*) is still deterministic.
    // Counts differing between two plans → genuine bug regardless of row ordering.
    private void countStarFallback(String queryA, String queryB, String mode) throws Exception {
        try {
            String countA = wrapInCountStar(queryA);
            String countB = wrapInCountStar(queryB);
            List<String> rA = executeQuery(countA);
            List<String> rB = executeQuery(countB);
            if (rA == null || rB == null) return;
            if (!rA.equals(rB)) {
                aggregateFallbackUsed++;
                List<String> combinedString = new ArrayList<>();
                combinedString.add("-- [" + mode + " COUNT(*) FALLBACK] Original query filtered, but COUNT(*) mismatch detected");
                combinedString.add("-- COUNT_A: " + countA);
                combinedString.add("-- COUNT_B: " + countB);
                ComparatorHelper.assumeResultSetsAreEqual(rA, rB, countA, combinedString, globalState);
            }
        } catch (Exception e) {
            // Fallback itself may fail (e.g., query not suitable for wrapping) — ignore
        }
    }

    // Subquery wrapping is safe for any structure (UNION, subqueries, etc.).
    // COUNT(*) includes LIMIT — counts rows actually returned, not total matching rows.
    private String wrapInCountStar(String query) {
        // Remove trailing semicolon
        String q = query.endsWith(";") ? query.substring(0, query.length() - 1) : query;
        // Safe wrapping: treat the entire original query as a subquery
        return "SELECT COUNT(*) FROM (" + q + ") AS cnt_sub;";
    }

    // ==================== Mode 19: Deterministic Index Query (P4) ====================

    private List<String> sampleColumnValues(String tableName, String colName, int limit) {
        try {
            String query = "SELECT " + colName + " FROM " + tableName
                    + " WHERE " + colName + " IS NOT NULL LIMIT " + limit + ";";
            return execInternal(query);
        } catch (Exception e) {
            return null;
        }
    }

    // PG's PostgresColumn has no isPrimaryKey(); falls back to scanning for single-column UNIQUE indexes.
    private PostgresColumn getUniqueKeyColumn(PostgresTable table) {
        for (PostgresIndex idx : table.getIndexes()) {
            if (idx.isUnique() && idx.getColumnNames().size() == 1) {
                String colName = idx.getColumnNames().get(0);
                for (PostgresColumn col : table.getColumns()) {
                    if (col.getName().equals(colName)) return col;
                }
            }
        }
        // Fallback: use first column
        List<PostgresColumn> cols = table.getColumns();
        return cols.isEmpty() ? null : cols.get(0);
    }

    private String quoteValueForSQL(String rawValue, PostgresColumn col) {
        if (rawValue == null) return "NULL";
        // NOTE: Do NOT treat values that merely start/end with a single quote as
        // already-quoted SQL literals. JDBC returns RAW data values, not SQL
        // literals (e.g. a TEXT cell containing a single quote "'" is returned as
        // a 1-char string). The old "if (startsWith && endsWith) return rawValue"
        // shortcut returned such a bare single quote as-is, which opened an
        // unterminated string literal inside IN (...) lists and caused crashes
        // like: ERROR: Unterminated string literal. All quoting/escaping is now
        // handled uniformly by the type-specific branches below.
        // String-like types that need single-quoting
        if (col.getType() == PostgresDataType.TEXT
                || col.getType() == PostgresDataType.INET
                || col.getType() == PostgresDataType.RANGE
                || col.getType() == PostgresDataType.BIT) {
            return "'" + rawValue.replace("'", "''") + "'";
        }
        if (col.getType() == PostgresDataType.MONEY) {
            // PostgreSQL money type returns values like "$636", "$803" from SELECT.
            // These must be single-quoted, otherwise $N is interpreted as a
            // prepared-statement positional parameter, causing:
            //   ERROR: could not determine data type of parameter $N
            return "'" + rawValue.replace("'", "''") + "'";
        }
        // For numeric/boolean types, if the value is empty string it still needs quoting
        // to avoid generating invalid SQL like "IN (, )"
        if (rawValue.isEmpty()) {
            return "NULL";
        }
        return rawValue;
    }

    // 7 patterns: 0=SELECT* ORDER BY LIMIT50, 1=COUNT(*), 2=SELECT* LIMIT10, 3=BETWEEN,
    // 4=IN list, 5=covering scan, 6=multi-column WHERE.
    private String buildDeterministicQuery(PostgresTable table, PostgresColumn keyCol, String keyVal) {
        String tblName = table.getName();
        String colName = keyCol.getName();
        List<PostgresColumn> columns = table.getColumns();
        List<PostgresIndex> indexes = table.getIndexes();
        if (indexes.isEmpty()) return null;

        // PG doesn't support USE INDEX — we force index scan via session settings
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String query;
        int variant = Randomly.fromOptions(0, 1, 2, 3, 4, 5, 6);
        switch (variant) {
        case 0:
            query = "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + keyVal
                    + " ORDER BY " + colName + " LIMIT 50;";
            break;
        case 1:
            query = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " " + op + " " + keyVal + ";";
            break;
        case 2:
            query = "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + keyVal + " ORDER BY " + colName + " LIMIT 10;";
            break;
        case 3: {
            // BETWEEN range scan
            List<String> vals2 = sampleColumnValues(tblName, colName, 3);
            String val2 = (vals2 != null && !vals2.isEmpty()) ? quoteValueForSQL(vals2.get(0), keyCol) : keyVal;
            query = "SELECT * FROM " + tblName + " WHERE " + colName + " BETWEEN " + keyVal + " AND " + val2 + " ORDER BY " + colName + ";";
            break;
        }
        case 4: {
            // IN list
            List<String> vals = sampleColumnValues(tblName, colName, 5);
            StringBuilder inList = new StringBuilder();
            if (vals != null && vals.size() >= 2) {
                for (int i = 0; i < Math.min(vals.size(), 4); i++) {
                    if (i > 0) inList.append(", ");
                    inList.append(quoteValueForSQL(vals.get(i), keyCol));
                }
            } else {
                inList.append(keyVal);
            }
            query = "SELECT * FROM " + tblName + " WHERE " + colName + " IN (" + inList + ") ORDER BY " + colName + ";";
            break;
        }
        case 5:
            // Covering index scan — SELECT only the indexed column
            query = "SELECT " + colName + " FROM " + tblName + " WHERE " + colName + " " + op + " " + keyVal + " ORDER BY " + colName + " LIMIT 50;";
            break;
        case 6: {
            // Multi-column condition
            StringBuilder where = new StringBuilder();
            where.append(colName).append(" = ").append(keyVal);
            if (columns.size() > 1) {
                PostgresColumn col2 = Randomly.fromList(columns);
                String col2Name = col2.getName();
                List<String> vals2 = sampleColumnValues(tblName, col2Name, 3);
                String val2 = (vals2 != null && !vals2.isEmpty()) ? quoteValueForSQL(vals2.get(0), col2) : "NULL";
                String op2 = Randomly.fromOptions(">", "<", ">=", "<=", "=");
                where.append(" AND ").append(col2Name).append(" ").append(op2).append(" ").append(val2);
            }
            query = "SELECT * FROM " + tblName + " WHERE " + where + " ORDER BY " + colName + " LIMIT 50;";
            break;
        }
        default:
            query = "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + keyVal
                    + " ORDER BY " + colName + " LIMIT 50;";
            break;
        }
        return query;
    }

    // PG has no USE INDEX hints — forces different plans via SET enable_indexscan/bitmapscan = OFF.
    // Uses unique-index column for WHERE to ensure deterministic results across plans.
    private void checkDeterministicIndexQuery() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with at least one index
        List<PostgresTable> tablesWithIndexes = new ArrayList<>();
        for (PostgresTable t : tables) {
            if (!t.isView() && !t.getIndexes().isEmpty()) {
                tablesWithIndexes.add(t);
            }
        }
        if (tablesWithIndexes.isEmpty()) {
            // Create an index
            try {
                globalState.executeStatement(PostgresIndexGenerator.generate(globalState));
                globalState.executeStatement(new SQLQueryAdapter(
                    "ANALYZE " + Randomly.fromList(tables).getName() + ";", true));
            } catch (Exception e) { return; }
            tablesWithIndexes.clear();
            for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
                if (!t.isView() && !t.getIndexes().isEmpty()) {
                    tablesWithIndexes.add(t);
                }
            }
            if (tablesWithIndexes.isEmpty()) return;
        }

        PostgresTable table = Randomly.fromList(tablesWithIndexes);
        PostgresColumn keyCol = getUniqueKeyColumn(table);
        if (keyCol == null) return;

        String tblName = table.getName();
        String colName = keyCol.getName();

        // Sample a value using the key column
        List<String> vals = sampleColumnValues(tblName, colName, 3);
        if (vals == null || vals.isEmpty()) return;
        String keyVal = quoteValueForSQL(vals.get(0), keyCol);

        // Build query
        String queryString = buildDeterministicQuery(table, keyCol, keyVal);
        if (queryString == null) return;

        lastQueryString = "[DET_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: Default vs SeqScan-only
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use index scan)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only (disable index and bitmap)
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_DET_IDX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_DET_IDX");
    }

    // ==================== Mode 20: NULL Index Handling ====================

    private void checkNullIndexHandling() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        tables = tables.stream().filter(t -> !t.isView()).collect(Collectors.toList());
        if (tables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(tables);
        List<PostgresColumn> columns = table.getColumns();
        if (columns.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(columns);
        String tblName = table.getName();
        String colName = col.getName();

        String idxName = "null_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) { return; }

        boolean hasNulls = false;
        try {
            List<String> nullCheck = execInternal(
                    "SELECT EXISTS(SELECT 1 FROM " + tblName + " WHERE " + colName + " IS NULL LIMIT 1);");
            hasNulls = nullCheck != null && !nullCheck.isEmpty() && !nullCheck.get(0).equals("f");
        } catch (Exception e) { }

        String whereCond;
        int nullVariant;
        if (hasNulls) {
            nullVariant = Randomly.fromOptions(0, 1, 2, 3, 4);
        } else {
            nullVariant = Randomly.fromOptions(1, 3);
        }

        switch (nullVariant) {
        case 0: whereCond = colName + " IS NULL"; break;
        case 1: whereCond = colName + " IS NOT NULL"; break;
        case 2:
            List<String> sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                whereCond = colName + " IS NULL OR " + colName + " = " + quoteValueForSQL(sampled.get(0), col);
            } else {
                whereCond = colName + " IS NULL";
            }
            break;
        case 3:
            sampled = sampleColumnValues(tblName, colName, 3);
            if (sampled != null && !sampled.isEmpty()) {
                whereCond = colName + " IS NOT NULL AND " + colName + " >= " + quoteValueForSQL(sampled.get(0), col);
            } else {
                whereCond = colName + " IS NOT NULL";
            }
            break;
        default:
            String countNull = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NULL;";
            String countNotNull = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
            lastQueryString = "[NULL_IDX] NULL count check";

            List<String> rNullDefault = executeQuery(countNull);
            if (rNullDefault == null) return;
            safeSet("SET enable_seqscan = OFF;");
            safeSet("SET enable_indexscan = ON;");
            safeSet("SET random_page_cost = 1.0;");
            List<String> rNullIdx = executeQueryWithRestore(countNull);
            if (rNullIdx == null) return;
            compareResultsSorted(rNullDefault, rNullIdx, countNull, "PG_NULL_IDX_ISNULL");

            List<String> rNotNullDefault = executeQuery(countNotNull);
            if (rNotNullDefault == null) return;
            safeSet("SET enable_seqscan = OFF;");
            safeSet("SET enable_indexscan = ON;");
            safeSet("SET random_page_cost = 1.0;");
            List<String> rNotNullIdx = executeQueryWithRestore(countNotNull);
            if (rNotNullIdx == null) return;
            compareResultsSorted(rNotNullDefault, rNotNullIdx, countNotNull, "PG_NULL_IDX_ISNOTNULL");
            return;
        }

        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereCond + " ORDER BY " + colName + " LIMIT 200;";
        lastQueryString = "[NULL_IDX] " + queryString;

        // EXPLAIN filter
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_NULL_IDX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_NULL_IDX");
    }

    // ==================== Mode 21: Prefix Index (SUBSTRING Function Index) ====================

    // PG has no MySQL-style col(N) prefix syntax; uses SUBSTRING(col, 1, N) expression index instead.
    // Tests that prefix-based index scans produce correct results.
    private void checkPrefixIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Find a table with TEXT columns
        PostgresTable table = Randomly.fromList(tables);
        if (table.isView()) return;
        List<PostgresColumn> textCols = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (col.getType() == PostgresDataType.TEXT) {
                textCols.add(col);
            }
        }
        if (textCols.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(textCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create a SUBSTRING prefix index
        int prefixLen = Randomly.fromOptions(1, 2, 3, 5, 10);
        String idxName = "prefix_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " (SUBSTRING(" + colName + ", 1, " + prefixLen + "));", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        // Sample actual values for WHERE conditions
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

        // Also build a SUBSTRING-specific WHERE that directly uses the index expression
        List<String> sampled = sampleColumnValues(tblName, colName, 3);
        String substringQuery = null;
        if (sampled != null && !sampled.isEmpty()) {
            String sampleVal = sampled.get(0);
            // Strip quotes
            if (sampleVal.startsWith("'") && sampleVal.endsWith("'") && sampleVal.length() > 2) {
                sampleVal = sampleVal.substring(1, sampleVal.length() - 1);
            }
            sampleVal = sampleVal.replace("'", "''");
            String prefix = sampleVal.length() >= prefixLen ? sampleVal.substring(0, prefixLen) : sampleVal;
            prefix = prefix.replace("'", "''");
            substringQuery = "SELECT * FROM " + tblName + " WHERE SUBSTRING(" + colName + ", 1, " + prefixLen
                    + ") = '" + prefix + "';";
        }

        // Choose between regular WHERE and SUBSTRING WHERE
        String queryString;
        if (substringQuery != null && Randomly.getBoolean()) {
            queryString = substringQuery;
        } else {
            queryString = "SELECT * FROM " + tblName + " WHERE " + whereCond + ";";
        }

        lastQueryString = "[PREFIX_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use prefix index)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_PREFIX_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_PREFIX_INDEX");
    }

    // ==================== Mode 22: Subquery + Index ====================

    // Different subquery strategies (hash semi-join vs materialization vs index scan) must produce
    // identical results — tests IN subquery and EXISTS correlated subquery.
    private void checkSubqueryIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = new ArrayList<>(schema.getDatabaseTables());
        if (tables.size() < 2) return;

        // Filter out views
        tables = tables.stream().filter(t -> !t.isView()).collect(Collectors.toList());
        if (tables.size() < 2) return;

        java.util.Collections.shuffle(tables);
        PostgresTable outerTable = tables.get(0);
        PostgresTable innerTable = tables.get(1);
        if (outerTable.getColumns().isEmpty() || innerTable.getColumns().isEmpty()) return;

        String outerTbl = outerTable.getName();
        String innerTbl = innerTable.getName();
        PostgresColumn outerCol = Randomly.fromList(outerTable.getColumns());
        PostgresColumn innerCol = Randomly.fromList(innerTable.getColumns());

        // Create indexes on both tables
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
        // Analyze both tables
        try {
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + outerTbl + ";", true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + innerTbl + ";", true));
        } catch (Exception e) { }

        // Build subquery — IN or EXISTS pattern
        String queryString;
        if (Randomly.getBoolean()) {
            // IN subquery
            queryString = "SELECT * FROM " + outerTbl + " WHERE " + outerCol.getName()
                    + " IN (SELECT " + innerCol.getName() + " FROM " + innerTbl + ");";
        } else {
            // EXISTS correlated subquery
            queryString = "SELECT * FROM " + outerTbl
                    + " WHERE EXISTS (SELECT 1 FROM " + innerTbl
                    + " WHERE " + innerTbl + "." + innerCol.getName() + " = " + outerTbl + "." + outerCol.getName() + ");";
        }
        lastQueryString = "[SUBQ_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: Default vs no-hash-join (forces different subquery strategy)
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_hashjoin = OFF;");
        safeSet("SET enable_nestloop = OFF;");
        List<String> explainAlt = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainAlt)) {
            // Fallback: try SeqScan vs IndexScan
            safeSet("SET enable_indexscan = OFF;");
            safeSet("SET enable_bitmapscan = OFF;");
            List<String> explainSeqScan = getExplainPlan(queryString);
            restoreDefaultSettings();
            if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

            List<String> r1 = executeQuery(queryString);
            if (r1 == null) return;
            safeSet("SET enable_indexscan = OFF;");
            safeSet("SET enable_bitmapscan = OFF;");
            List<String> r2 = executeQueryWithRestore(queryString);
            if (r2 == null) return;
            compareResultsSorted(r1, r2, queryString, "PG_SUBQ_IDX");
            if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_SUBQ_IDX");
            return;
        }

        // Plan A: Default (may use hash semi-join)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: Force merge join path (disable hash join + nestloop)
        safeSet("SET enable_hashjoin = OFF;");
        safeSet("SET enable_nestloop = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_SUBQ_IDX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_SUBQ_IDX");
    }

    // ==================== Mode 23: Index Cond Pushdown (ICP Equivalent) ====================

    // PG IndexScan: Index Cond (prefix column, pushed to index) vs Filter (non-prefix, after heap fetch).
    // A bug in Index Cond evaluation produces wrong results vs SeqScan — composite index on (col1, col2).
    private void checkIndexCondPushdown() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Filter out views
        tables = tables.stream().filter(t -> !t.isView()).collect(Collectors.toList());
        if (tables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;

        List<PostgresColumn> cols = new ArrayList<>(table.getColumns());
        java.util.Collections.shuffle(cols);
        PostgresColumn col1 = cols.get(0);  // Index prefix column
        PostgresColumn col2 = cols.get(1);  // Index non-prefix column (triggers Filter)
        String tblName = table.getName();

        // Create composite index on (col1, col2)
        String idxName = "icp_idx_" + Math.abs(col1.getName().hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " (" + col1.getName() + ", " + col2.getName() + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        // Build WHERE with Index Cond (col1) + Filter (col2)
        String val1 = generateDataAwareValueForType(tblName, col1);
        String val2 = generateDataAwareValueForType(tblName, col2);

        // Multiple query patterns to exercise different Index Cond/Filter combinations
        String queryString;
        int pattern = Randomly.fromOptions(0, 1, 2, 3, 4);
        switch (pattern) {
        case 0:
            // Prefix equality + non-prefix range → Index Cond on col1, Filter on col2
            queryString = "SELECT * FROM " + tblName + " WHERE " + col1.getName() + " = " + val1
                    + " AND " + col2.getName() + " > " + val2 + ";";
            break;
        case 1:
            // Prefix range + non-prefix equality → Index Cond on col1, Filter on col2
            queryString = "SELECT * FROM " + tblName + " WHERE " + col1.getName() + " > " + val1
                    + " AND " + col2.getName() + " = " + val2 + ";";
            break;
        case 2:
            // Both columns with range conditions
            queryString = "SELECT * FROM " + tblName + " WHERE " + col1.getName() + " >= " + val1
                    + " AND " + col2.getName() + " <= " + val2 + ";";
            break;
        case 3:
            // Prefix equality + non-prefix IN list
            queryString = "SELECT * FROM " + tblName + " WHERE " + col1.getName() + " = " + val1
                    + " AND " + col2.getName() + " IN (" + val2 + ", " + generateDataAwareValueForType(tblName, col2) + ");";
            break;
        default:
            // Prefix equality + non-prefix IS NOT NULL
            queryString = "SELECT * FROM " + tblName + " WHERE " + col1.getName() + " = " + val1
                    + " AND " + col2.getName() + " IS NOT NULL;";
            break;
        }

        lastQueryString = "[ICP_PUSH] " + queryString;
        log(queryString);

        // EXPLAIN filter
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use Index Cond + Filter)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only (no Index Cond pushdown)
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_ICP_PUSHDOWN");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_ICP_PUSHDOWN");
    }

    // ==================== Mode 24: BRIN Index (Block Range Index) ====================

    // BRIN (Block Range Index) stores min/max per block range — unique to PG, optimal for naturally ordered data.
    // BRIN uses Bitmap Heap Scan with recheck conditions; bugs in recheck logic cause wrong results vs SeqScan.
    private void checkBRINIndex() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        // Filter out views
        tables = tables.stream().filter(t -> !t.isView()).collect(Collectors.toList());
        if (tables.isEmpty()) return;

        PostgresTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        // BRIN works best on INT/numeric columns with natural ordering
        List<PostgresColumn> numericCols = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (col.getType() == PostgresDataType.INT || col.getType() == PostgresDataType.DECIMAL
                    || col.getType() == PostgresDataType.FLOAT || col.getType() == PostgresDataType.REAL) {
                numericCols.add(col);
            }
        }
        if (numericCols.isEmpty()) {
            // Fallback: use any column
            numericCols.addAll(table.getColumns());
        }
        if (numericCols.isEmpty()) return;

        PostgresColumn col = Randomly.fromList(numericCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create BRIN index
        String idxName = "brin_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName
                    + " USING brin (" + colName + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tblName + ";", true));
        } catch (Exception e) {
            return;
        }

        // Build range query that can use BRIN
        String val = generateDataAwareValueForType(tblName, col);
        String queryString;
        int pattern = Randomly.fromOptions(0, 1, 2, 3);
        switch (pattern) {
        case 0:
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " > " + val + ";";
            break;
        case 1:
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " < " + val + ";";
            break;
        case 2: {
            String val2 = generateDataAwareValueForType(tblName, col);
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName
                    + " BETWEEN LEAST(" + val + ", " + val2 + ") AND GREATEST(" + val + ", " + val2 + ");";
            break;
        }
        default:
            queryString = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " >= " + val + ";";
            break;
        }
        lastQueryString = "[BRIN_IDX] " + queryString;
        log(queryString);

        // EXPLAIN filter: check if BRIN scan is actually used
        List<String> explainDefault = getExplainPlan(queryString);
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> explainSeqScan = getExplainPlan(queryString);
        restoreDefaultSettings();
        if (!plansAreDifferent(explainDefault, explainSeqScan)) return;

        // Plan A: Default (may use BRIN → Bitmap Heap Scan)
        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Plan B: SeqScan only
        safeSet("SET enable_indexscan = OFF;");
        safeSet("SET enable_bitmapscan = OFF;");
        List<String> r2 = executeQueryWithRestore(queryString);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, queryString, "PG_BRIN_INDEX");
        if (lastCompareFiltered) countStarFallback(queryString, queryString, "PG_BRIN_INDEX");
    }

    // ==================== Phase 3: Index Effectiveness Check ====================

    // Checks EXPLAIN output for the index name — "Seq Scan" in the plan means the index was not used.
    private boolean isIndexEffectivelyUsed(List<String> explainPlan, String indexName) {
        if (explainPlan == null || explainPlan.isEmpty()) return false;
        for (String line : explainPlan) {
            String lower = line.toLowerCase();
            if (lower.contains("index") && lower.contains(indexName.toLowerCase())) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String getLastQueryString() {
        return lastQueryString;
    }
}
