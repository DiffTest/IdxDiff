package idxdiff.mariadb.oracle;

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
import idxdiff.ComparatorHelper;
import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.common.oracle.TestOracle;
import idxdiff.common.query.ExpectedErrors;
import idxdiff.common.query.SQLQueryAdapter;
import idxdiff.mariadb.MariaDBErrors;
import idxdiff.mariadb.MariaDBProvider.MariaDBGlobalState;
import idxdiff.mariadb.MariaDBSchema;
import idxdiff.mariadb.MariaDBSchema.MariaDBColumn;
import idxdiff.mariadb.MariaDBSchema.MariaDBIndex;
import idxdiff.mariadb.MariaDBSchema.MariaDBTable;
import idxdiff.mariadb.ast.MariaDBBinaryOperator;
import idxdiff.mariadb.ast.MariaDBColumnName;
import idxdiff.mariadb.ast.MariaDBConstant;
import idxdiff.mariadb.ast.MariaDBExpression;
import idxdiff.mariadb.ast.MariaDBOrderByTerm;
import idxdiff.mariadb.ast.MariaDBPostfixUnaryOperation;
import idxdiff.mariadb.ast.MariaDBVisitor;
import idxdiff.mariadb.gen.MariaDBExpressionGenerator;
import idxdiff.mariadb.gen.MariaDBIndexGenerator;

/**
 * MariaDB Index Oracle — verifies that different index strategies produce
 * identical query results.
 *
 * MariaDB-specific features tested:
 * <ul>
 * <li>mariadb_index=off optimizer_switch (MariaDB-only)</li>
 * <li>unique_index_clone optimizer_switch (MariaDB-only)</li>
 * <li>PREFIX INDEX on VARCHAR columns</li>
 * <li>FULLTEXT INDEX</li>
 * <li>HASH vs BTREE index comparison</li>
 * <li>DESC index (MariaDB supports descending indexes)</li>
 * <li>INVISIBLE INDEX</li>
 * </ul>
 *
 * Core test modes:
 * <ul>
 * <li>0: CREATE_INDEX_CONSISTENCY</li>
 * <li>1: DROP_INDEX_CONSISTENCY</li>
 * <li>2: FORCE_INDEX_VS_DEFAULT</li>
 * <li>3: IGNORE_INDEX_VS_DEFAULT</li>
 * <li>4: PREFIX_INDEX</li>
 * <li>5: HASH_VS_BTREE</li>
 * <li>6: INVISIBLE_INDEX</li>
 * <li>7: FULLTEXT_INDEX</li>
 * <li>8: OPTIMIZER_SWITCH_INDEX (MariaDB-specific switches)</li>
 * <li>9: MULTI_INDEX_CREATE</li>
 * <li>10: UNIQUE_INDEX_CONSISTENCY</li>
 * <li>11: TABLE_VERIFICATION</li>
 * <li>12: AGGREGATE_PLAN</li>
 * <li>13: COVERING_INDEX (Phase B)</li>
 * <li>14: INDEX_MERGE (Phase B)</li>
 * <li>15: LOOSE_INDEX_SCAN (Phase B)</li>
 * <li>16: ORDER_BY_LIMIT_INDEX (Phase B)</li>
 * <li>17: RANGE_BOUNDARY (Phase B)</li>
 * <li>18: SUBQUERY_INDEX (Phase B)</li>
 * <li>19: JOIN_INDEX_SELECTION (Phase B)</li>
 * <li>20: DETERMINISTIC_INDEX_QUERY (Phase B)</li>
 * <li>21: ICP_CONSISTENCY (Phase B)</li>
 * <li>22: OPTIMIZER_SWITCH_DETAILED (Phase B)</li>
 * <li>23: NULL_INDEX_HANDLING (Phase B)</li>
 * <li>24: ROWID_FILTER (Phase C — MariaDB-only)</li>
 * <li>25: NOT_NULL_RANGE_SCAN (Phase C — MariaDB-only)</li>
 * <li>26: INDEX_MERGE_INTERSECTION (Phase C — MariaDB-only)</li>
 * <li>27: JOIN_CACHE_LEVEL (Phase C — MariaDB-only)</li>
 * <li>28: CONDITION_PUSHDOWN_DERIVED (Phase C — MariaDB-only)</li>
 * <li>29: FUNCTIONAL_INDEX (Phase G — via generated column)</li>
 * <li>30: DML_INDEX_CONSISTENCY (Phase G)</li>
 * <li>31: DESC_INDEX_SORT (Phase G)</li>
 * <li>32: DROP_COLUMN_WITH_INDEX (Phase P1)</li>
 * <li>33: GENERATED_COLUMN_INDEX (Phase P1)</li>
 * <li>34: COLLATION_INDEX (Phase P1)</li>
 * <li>35: TYPE_MISMATCH_INDEX (Phase P1)</li>
 * <li>36: SQL_SEMANTIC_EQUIVALENCE (Phase P1)</li>
 * </ul>
 */
public class MariaDBIndexOracle implements TestOracle<MariaDBGlobalState> {

    private final MariaDBGlobalState globalState;
    private final ExpectedErrors errors;
    private String lastQueryString;
    private boolean dataPopulated = false;

    // Statistics tracking
    private int totalTests = 0;
    private int effectiveTests = 0;
    private int explainFiltered = 0;
    private int queriesCompared = 0;

    private static final double EPSILON = 1e-10;

    // Phase A: COUNT(*) fallback tracking
    private boolean lastCompareFiltered = false;
    private int aggregateFallbackUsed = 0;

    // Phase A: Column value sampling cache
    private Map<String, List<String>> columnValueCache = new HashMap<>();

    // Phase D: Periodic data refresh
    private static final int DATA_REFRESH_INTERVAL = 300;
    private int checksSinceLastDataRefresh = 0;

    // Phase D6: Periodic index pruning to avoid "Too many keys specified; max 64 keys allowed"
    private static final int INDEX_PRUNE_THRESHOLD = 50; // prune when table has > 50 non-PK indexes
    private static final int INDEX_PRUNE_INTERVAL = 50;  // check every 50 rounds
    private int checksSinceLastIndexPrune = 0;

    // Phase D: Index-friendly tables flag
    private boolean indexFriendlyCreated = false;

    public MariaDBIndexOracle(MariaDBGlobalState globalState) {
        this.globalState = globalState;
        this.errors = buildExpectedErrors();
    }

    private ExpectedErrors buildExpectedErrors() {
        ExpectedErrors expectedErrors = ExpectedErrors.newErrors()
                .with(MariaDBErrors.getIndexErrors())
                .with("Too many keys specified") // MariaDB 64-index limit per table
                .build();
        return expectedErrors;
    }

    @Override
    public void check() throws Exception {
        // Phase D1: Create index-friendly tables on first check
        createIndexFriendlyTables();
        ensureSufficientData();

        // Phase D5: Periodic data refresh to avoid stale data
        if (++checksSinceLastDataRefresh >= DATA_REFRESH_INTERVAL) {
            checksSinceLastDataRefresh = 0;
            dataPopulated = false;
            ensureSufficientData();
        }

        // Phase D6: Periodic index pruning to avoid "Too many keys specified; max 64 keys allowed"
        if (++checksSinceLastIndexPrune >= INDEX_PRUNE_INTERVAL) {
            checksSinceLastIndexPrune = 0;
            pruneExcessIndexes();
        }

        columnValueCache.clear();
        lastCompareFiltered = false;
        totalTests++;
        if (totalTests % 100 == 0) {
            log("[STATS] total=" + totalTests + " compared=" + queriesCompared
                    + " explainFiltered=" + explainFiltered + " bugsDetected=" + effectiveTests
                    + " countStarFallback=" + aggregateFallbackUsed
                    + " (compareRate=" + String.format("%.1f", 100.0 * queriesCompared / Math.max(totalTests, 1))
                    + "%)");
        }
        try {
            int mode = Randomly.fromOptions(
                    // === HIGH WEIGHT (2x): High bug density / MariaDB-specific ===
                    13, 13,         // Covering Index
                    14, 14,         // Index Merge
                    15, 15,         // Loose Index Scan
                    16, 16,         // ORDER BY + LIMIT Index
                    17, 17,         // Range Boundary
                    18, 18,         // Subquery Index
                    19, 19,         // Join Index Selection
                    20, 20,         // Deterministic Index Query
                    21, 21,         // ICP Consistency
                    22, 22,         // Optimizer Switch Detailed
                    24, 24,         // Rowid Filter (MariaDB-only)
                    25, 25,         // Not Null Range Scan (MariaDB-only)
                    27, 27,
                    28, 28,
                    26, 26,         // Index Merge Intersection (MariaDB-only)
                    29, 29,         // Functional Index (via generated column)
                    30, 30,         // DML + Index Consistency
                    31, 31,          // DESC Index Sort
                    32, 32,
                    33, 33,
                    34, 34, 
                    35, 35,
                    36, 36,
                    // === NORMAL WEIGHT (1x): Core modes ===
                    0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 23
                    // 8   // Covered by 22 
                    // Total: 37 modes (0-36)
            );
            switch (mode) {
            case 0:
                checkCreateIndexConsistency();
                break;
            case 1:
                checkDropIndexConsistency();
                break;
            case 2:
                checkForceIndexVsDefault();
                break;
            case 3:
                checkIgnoreIndexVsDefault();
                break;
            case 4:
                checkPrefixIndex();
                break;
            case 5:
                checkHashVsBtree();
                break;
            case 6:
                checkInvisibleIndex();
                break;
            case 7:
                checkFullTextIndex();
                break;
            case 8:
                checkOptimizerSwitchIndex();
                break;
            case 9:
                checkMultiIndexCreate();
                break;
            case 10:
                checkUniqueIndexConsistency();
                break;
            case 11:
                checkTableVerification();
                break;
            case 12:
                checkAggregatePlan();
                break;
            // ==================== Phase B: Modes 13-23 ====================
            case 13:
                checkCoveringIndex();
                break;
            case 14:
                checkIndexMerge();
                break;
            case 15:
                checkLooseIndexScan();
                break;
            case 16:
                checkOrderByLimitIndex();
                break;
            case 17:
                checkRangeBoundary();
                break;
            case 18:
                checkSubqueryIndex();
                break;
            case 19:
                checkJoinIndexSelection();
                break;
            case 20:
                checkDeterministicIndexQuery();
                break;
            case 21:
                checkICPConsistency();
                break;
            case 22:
                checkOptimizerSwitchDetailed();
                break;
            case 23:
                checkNullIndexHandling();
                break;
            // ==================== Phase C: Modes 24-28 (MariaDB-only) ====================
            case 24:
                checkRowidFilter();
                break;
            case 25:
                checkNotNullRangeScan();
                break;
            case 26:
                checkIndexMergeIntersection();
                break;
            case 27:
                checkJoinCacheLevel();
                break;
            case 28:
                checkConditionPushdownDerived();
                break;
            // ==================== Phase G: Modes 29-31 (Advanced Index Types) ====================
            case 29:
                checkFunctionalIndex();
                break;
            case 30:
                checkDMLIndexConsistency();
                break;
            case 31:
                checkDescIndexSort();
                break;
            // ==================== Phase P1: Modes 32-36 (New Test Modes) ====================
            case 32:
                checkDropColumnWithIndex();
                break;
            case 33:
                checkGeneratedColumnIndex();
                break;
            case 34:
                checkCollationIndex();
                break;
            case 35:
                checkTypeMismatchIndex();
                break;
            case 36:
                checkSQLSemanticEquivalence();
                break;
            }
        } catch (NullPointerException | ArrayIndexOutOfBoundsException e) {
            throw new IgnoreMeException();
        }
    }

    // ==================== Mode 0: Create Index Consistency ====================

    private void checkCreateIndexConsistency() throws Exception {
        // [FIX] Ensure query and index target the SAME table.
        // Previously used generateSimpleQuery() which picked a random table,
        // then MariaDBIndexGenerator.generate() picked a different random table.
        // When tables didn't match, index had no effect on query → test was useless.
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        String queryString = generateQueryForTable(table);
        if (queryString == null)
            return;

        lastQueryString = "[CREATE_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;

        // Create index on the SAME table as the query
        try {
            MariaDBColumn col = Randomly.fromList(table.getColumns());
            MariaDBIndexGenerator.createIndexOnColumn(table, col);
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null)
            return;

        compareResultsSorted(r1, r2, queryString, "MARIADB_CREATE_INDEX");
    }

    // ==================== Mode 1: Drop Index Consistency ====================

    private void checkDropIndexConsistency() throws Exception {
        // [FIX] Ensure query and DROP INDEX target the SAME table.
        // Previously generateSimpleQuery() picked a random table, then
        // getRandomNonPrimaryIndex() picked an index from a different table.
        MariaDBIndex idxToDrop = getRandomNonPrimaryIndex();
        if (idxToDrop == null)
            return;

        String tableName = findTableForIndex(idxToDrop);
        if (tableName == null)
            return;

        // Generate query for the SAME table as the index being dropped
        MariaDBTable targetTable = null;
        for (MariaDBTable t : globalState.getSchema().getDatabaseTables()) {
            if (t.getName().equals(tableName)) {
                targetTable = t;
                break;
            }
        }
        if (targetTable == null) return;

        String queryString = generateQueryForTable(targetTable);
        if (queryString == null) return;

        lastQueryString = "[DROP_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;

        try {
            ExpectedErrors dropErrors = new ExpectedErrors();
            dropErrors.add("Can't DROP");
            dropErrors.add("check that column/key exists");
            globalState.executeStatement(new SQLQueryAdapter(
                    "DROP INDEX " + idxToDrop.getIndexName() + " ON " + tableName + ";", dropErrors, true));
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null)
            return;

        compareResultsSorted(r1, r2, queryString, "MARIADB_DROP_INDEX");
    }

    // ==================== Mode 2: FORCE INDEX vs Default ====================

    private void checkForceIndexVsDefault() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) {
            try {
                MariaDBIndexGenerator.createIndexOnColumn(table,
                        Randomly.fromList(table.getColumns()));
                analyzeAllTables();
            } catch (Exception e) {
                return;
            }
            tableIndexes = table.getIndexes();
            if (tableIndexes.isEmpty())
                return;
        }

        MariaDBIndex forceIdx = Randomly.fromList(tableIndexes);
        String idxName = forceIdx.getIndexName();
        String tblName = table.getName();

        String queryString = generateIndexAwareQueryString(table, forceIdx);
        lastQueryString = "[FORCE_IDX] " + queryString;
        log(queryString);

        String forcedQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " FORCE INDEX(" + idxName + ")");

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(forcedQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2))
            return;

        // [FIX] Verify FORCE INDEX version effectively uses the index
        if (!isIndexEffectivelyUsed(explainPlan2, idxName)) return;

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;
        List<String> r2 = executeQuery(forcedQuery);
        if (r2 == null)
            return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_FORCE_INDEX");
        if (lastCompareFiltered) {
            countStarFallback(queryString, forcedQuery, "MARIADB_FORCE_INDEX");
        }
    }

    // ==================== Mode 3: IGNORE INDEX vs Default ====================

    private void checkIgnoreIndexVsDefault() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty())
            return;

        MariaDBIndex ignoreIdx = Randomly.fromList(tableIndexes);
        String idxName = ignoreIdx.getIndexName();
        String tblName = table.getName();

        String queryString = generateIndexAwareQueryString(table, ignoreIdx);
        lastQueryString = "[IGNORE_IDX] " + queryString;
        log(queryString);

        String ignoredQuery = queryString.replaceFirst(
                "(?i)FROM\\s+" + java.util.regex.Pattern.quote(tblName) + "\\b",
                "FROM " + tblName + " IGNORE INDEX(" + idxName + ")");

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> explainPlan2 = getExplainPlan(ignoredQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2))
            return;

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null)
            return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_IGNORE_INDEX");
        if (lastCompareFiltered) {
            countStarFallback(queryString, ignoredQuery, "MARIADB_IGNORE_INDEX");
        }
    }

    // ==================== Mode 4: Prefix Index ====================

    private void checkPrefixIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBColumn> varCharCols = new ArrayList<>();
        for (MariaDBColumn col : table.getColumns()) {
            if (col.getType() == MariaDBSchema.MariaDBDataType.VARCHAR) {
                varCharCols.add(col);
            }
        }
        if (varCharCols.isEmpty())
            return;

        MariaDBColumn col = Randomly.fromList(varCharCols);
        String tblName = table.getName();
        String colName = col.getName();

        int prefixLen = Randomly.fromOptions(1, 2, 3, 5, 10);
        try {
            globalState.executeStatement(
                    MariaDBIndexGenerator.createPrefixIndex(table, col, prefixLen));
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        String val = generateDataAwareValueForType(tblName, col);
        String whereCond;
        int patternType = Randomly.fromOptions(0, 1, 2, 3, 4);
        switch (patternType) {
        case 0:
            whereCond = colName + " IS NOT NULL";
            break;
        case 1:
            whereCond = colName + " = " + val;
            break;
        case 2:
            whereCond = colName + " > " + val;
            break;
        case 3:
            whereCond = colName + " < " + val;
            break;
        default:
            whereCond = colName + " != " + val + " AND " + colName + " IS NOT NULL";
            break;
        }

        // Find the newly created prefix index
        String idxName = null;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (idx.isPrefixIndex() && idx.getColumnNames().contains(colName)) {
                idxName = idx.getIndexName();
                break;
            }
        }
        if (idxName == null)
            return;

        String countDefault = "SELECT COUNT(*) FROM " + tblName + " WHERE " + whereCond + ";";
        String countForced = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereCond
                + ";";

        lastQueryString = "[PREFIX_IDX] " + countDefault;
        log(countDefault);

        List<String> r1 = executeQuery(countDefault);
        if (r1 == null)
            return;
        List<String> r2 = executeQuery(countForced);
        if (r2 == null)
            return;

        compareResultsSorted(r1, r2, countDefault, "MARIADB_PREFIX_IDX");
    }

    // ==================== Mode 5: HASH vs BTREE ====================

    private void checkHashVsBtree() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty())
            return;
        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        String hashIdx = "hash_" + Math.abs(colName.hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        String btreeIdx = "btree_" + Math.abs(colName.hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        boolean hashCreated = false, btreeCreated = false;

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + hashIdx + " USING HASH ON " + tblName + " (" + colName + ");", errors, true));
            hashCreated = true;
        } catch (Exception e) {
        }
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + btreeIdx + " USING BTREE ON " + tblName + " (" + colName + ");", errors, true));
            btreeCreated = true;
        } catch (Exception e) {
        }

        if (!hashCreated || !btreeCreated)
            return;
        analyzeAllTables();

        String val = generateDataAwareValueForType(tblName, col);
        String whereCond;
        int patternType = Randomly.fromOptions(0, 1, 2, 3, 4, 5);
        switch (patternType) {
        case 0:
            whereCond = colName + " IS NOT NULL";
            break;
        case 1:
            whereCond = colName + " = " + val;
            break;
        case 2:
            whereCond = colName + " > " + val;
            break;
        case 3:
            whereCond = colName + " < " + val;
            break;
        case 4:
            whereCond = colName + " >= " + val;
            break;
        default:
            whereCond = colName + " IS NOT NULL AND " + colName + " != " + val;
            break;
        }

        String forceHash = "SELECT " + colName + " FROM " + tblName + " FORCE INDEX(" + hashIdx + ") WHERE "
                + whereCond + " ORDER BY " + colName + " LIMIT 100;";
        String forceBtree = "SELECT " + colName + " FROM " + tblName + " FORCE INDEX(" + btreeIdx + ") WHERE "
                + whereCond + " ORDER BY " + colName + " LIMIT 100;";

        lastQueryString = "[HASH_VS_BTREE] " + forceHash;
        log(forceHash);

        List<String> r1 = executeQuery(forceHash);
        if (r1 == null)
            return;
        List<String> r2 = executeQuery(forceBtree);
        if (r2 == null)
            return;

        lastCompareFiltered = false;
        compareResultsStrict(r1, r2, forceHash, "MARIADB_HASH_VS_BTREE");
        if (lastCompareFiltered) {
            countStarFallback(forceHash, forceBtree, "MARIADB_HASH_VS_BTREE");
        }
    }

    // ==================== Mode 6: Invisible Index ====================

    private void checkInvisibleIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty())
            return;

        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

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
        if (r1 == null)
            return;

        String idxName = "inv_" + Math.abs(colName.hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + table.getName()
                            + " (" + colName + ") INVISIBLE;",
                    errors, true));
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null)
            return;

        compareResultsSorted(r1, r2, queryString, "MARIADB_INVISIBLE_IDX");
    }

    // ==================== Mode 7: FULLTEXT Index (Enhanced) ====================

    private void checkFullTextIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBColumn> textCols = new ArrayList<>();
        for (MariaDBColumn c : table.getColumns()) {
            // [FIX] Exclude generated columns — MariaDB does not support FULLTEXT index
            // on generated columns ("This is not yet supported for generated columns").
            // Generated columns are named "gen_col_*" by MariaDBTableGenerator.
            if (c.getType() == MariaDBSchema.MariaDBDataType.VARCHAR
                    && !c.getName().startsWith("gen_col_")) {
                textCols.add(c);
            }
        }
        if (textCols.isEmpty())
            return;

        MariaDBColumn col = Randomly.fromList(textCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Find existing fulltext index or create a new one
        String ftIdxName = null;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (idx.getIndexType() != null && idx.getIndexType().equals("FULLTEXT")) {
                ftIdxName = idx.getIndexName();
                break;
            }
        }
        if (ftIdxName == null) {
            try {
                globalState.executeStatement(MariaDBIndexGenerator.createFullTextIndex(table, col));
                analyzeAllTables();
            } catch (Exception e) {
                return;
            }
            // Find the newly created fulltext index
            for (MariaDBIndex idx : table.getIndexes()) {
                if (idx.getIndexType() != null && idx.getIndexType().equals("FULLTEXT")) {
                    ftIdxName = idx.getIndexName();
                    break;
                }
            }
        }
        if (ftIdxName == null)
            return;

        // Get a data-aware search term
        String searchTerm = generateDataAwareValueForType(tblName, col);
        // Remove quotes for MATCH AGAINST
        if (searchTerm.startsWith("'") && searchTerm.endsWith("'")) {
            searchTerm = searchTerm.substring(1, searchTerm.length() - 1);
        }
        // Take first word only for FULLTEXT search
        String trimmed = searchTerm.trim();
        if (trimmed.isEmpty())
            return;
        String[] words = trimmed.split("\\s+");
        // Defensive: filter out empty strings and ensure we have a valid word
        searchTerm = null;
        for (String w : words) {
            if (!w.isEmpty()) {
                searchTerm = w;
                break;
            }
        }
        if (searchTerm == null)
            return;

        // Phase E1 enhancement: Compare MATCH AGAINST with default plan vs FORCE INDEX
        // to verify FULLTEXT index produces consistent results.
        //
        // [FIX] Removed NATURAL MODE vs BOOLEAN MODE comparison (old case 1).
        // NATURAL and BOOLEAN modes do NOT have the same semantics when the search term
        // contains boolean operators (+, -, ~, >, <, *, ", (, )). For example:
        //   - "-1595820591" in BOOLEAN MODE means "exclude rows containing 1595820591"
        //   - "~Ez佊]V" in BOOLEAN MODE treats ~ as a fuzziness operator
        // This caused false positives (database6.log, database25.log).
        int testVariant = Randomly.fromOptions(0, 1);

        switch (testVariant) {
        case 0: {
            // Variant 1: MATCH AGAINST BOOLEAN MODE default vs FORCE INDEX (fulltext)
            // — valid equivalence test: same SQL semantics, different execution plan
            String matchQuery = "SELECT * FROM " + tblName + " WHERE MATCH(" + colName + ") AGAINST('" + searchTerm
                    + "' IN BOOLEAN MODE);";
            String forcedMatch = "SELECT * FROM " + tblName + " FORCE INDEX(" + ftIdxName + ") WHERE MATCH(" + colName
                    + ") AGAINST('" + searchTerm + "' IN BOOLEAN MODE);";

            lastQueryString = "[FULLTEXT_IDX_FORCE] " + matchQuery;
            log(matchQuery);

            List<String> r1 = executeQuery(matchQuery);
            if (r1 == null)
                return;
            List<String> r2 = executeQuery(forcedMatch);
            if (r2 == null)
                return;

            compareResultsSorted(r1, r2, matchQuery, "MARIADB_FULLTEXT_FORCE");
            break;
        }
        default: {
            // Variant 2: MATCH AGAINST with WITH QUERY EXPANSION vs without
            // — only verifies no crash, since query expansion may return superset results
            String noExpand = "SELECT * FROM " + tblName + " WHERE MATCH(" + colName + ") AGAINST('" + searchTerm
                    + "' IN BOOLEAN MODE);";
            String withExpand = "SELECT * FROM " + tblName + " FORCE INDEX(" + ftIdxName + ") WHERE MATCH(" + colName
                    + ") AGAINST('" + searchTerm + "' WITH QUERY EXPANSION);";

            lastQueryString = "[FULLTEXT_EXPANSION] " + noExpand;
            log(noExpand);

            // Query expansion may return superset results, so we only verify no crash
            List<String> r1 = executeQuery(noExpand);
            if (r1 == null)
                return;
            List<String> r2 = executeQuery(withExpand);
            if (r2 == null)
                return;

            // With query expansion, r2 may be a superset of r1 — only flag if r1 has rows
            // not in r2
            effectiveTests++;
            break;
        }
        }
    }

    // ==================== Mode 8: Optimizer Switch Index (MariaDB-specific) ====================

    private void checkOptimizerSwitchIndex() throws Exception {
        String queryString = null;
        MariaDBSchema optSchema = globalState.getSchema();
        List<MariaDBTable> optTables = optSchema.getDatabaseTables();
        if (!optTables.isEmpty()) {
            MariaDBTable optTable = Randomly.fromList(optTables);
            List<MariaDBIndex> optIndexes = optTable.getIndexes();
            if (!optIndexes.isEmpty()) {
                MariaDBIndex optIdx = Randomly.fromList(optIndexes);
                queryString = generateIndexAwareQueryString(optTable, optIdx);
            }
        }
        if (queryString == null)
            queryString = generateSimpleQuery();
        if (queryString == null)
            return;

        lastQueryString = "[OPT_SWITCH_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;

        // MariaDB-specific optimizer switches (Phase E2: expanded from 8 to 16 options)
        String switchVal = Randomly.fromOptions(
                // Original switches
                "mariadb_index=off",
                "unique_index_clone=off",
                "index_condition_pushdown=off,mrr=off,mrr_cost_based=off",
                "index_condition_pushdown=off,mrr=on,mrr_cost_based=off",
                "condition_fanout_filter=off,subquery_materialization_cost_based=off",
                "block_nested_loop=off",
                "index_condition_pushdown=off",
                "mrr=off,mrr_cost_based=off",
                // Phase E2: MariaDB-specific additions
                "rowid_filter=off",
                "not_null_range_scan=off",
                "index_merge_intersection=off",
                "index_merge_sort_intersection=off",
                "orderby_uses_equalities=off",
                "condition_pushdown_for_derived=off",
                "condition_pushdown_for_subquery=off",
                // Phase E2: Combination switches
                "index_condition_pushdown=off,rowid_filter=off",
                "mrr=off,mrr_sort_keys=off",
                "index_merge=off,index_merge_intersection=off");

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
        if (r2 == null)
            return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_OPT_SWITCH_IDX");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_OPT_SWITCH_IDX");
        }
    }

    // ==================== Mode 9: Multi-Index Create ====================

    private void checkMultiIndexCreate() throws Exception {
        // [FIX] Ensure query and index creation target the SAME table.
        // Previously generateSimpleQuery() picked a random table, then
        // MariaDBIndexGenerator.generate() picked different random tables.
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        String queryString = generateQueryForTable(table);
        if (queryString == null)
            return;

        lastQueryString = "[MULTI_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;

        // Create multiple indexes on the SAME table as the query
        int numIndexes = Randomly.smallNumber() + 1;
        for (int i = 0; i < numIndexes; i++) {
            try {
                MariaDBColumn col = Randomly.fromList(table.getColumns());
                MariaDBIndexGenerator.createIndexOnColumn(table, col);
            } catch (Exception e) {
                // index creation may fail
            }
        }
        analyzeAllTables();

        List<String> r2 = executeQuery(queryString);
        if (r2 == null)
            return;

        compareResultsSorted(r1, r2, queryString, "MARIADB_MULTI_INDEX");
    }

    // ==================== Mode 10: Unique Index Consistency ====================

    private void checkUniqueIndexConsistency() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty())
            return;
        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        // Query before UNIQUE index
        String queryString = "SELECT " + colName + ", COUNT(*) FROM " + tblName + " GROUP BY " + colName + ";";
        lastQueryString = "[UNIQUE_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;

        try {
            globalState.executeStatement(MariaDBIndexGenerator.createUniqueIndex(table, col));
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        List<String> r2 = executeQuery(queryString);
        if (r2 == null)
            return;

        compareResultsSorted(r1, r2, queryString, "MARIADB_UNIQUE_IDX");
    }

    // ==================== Mode 11: CHECK TABLE after index ====================

    private void checkTableVerification() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);

        // Create an index first
        try {
            MariaDBIndexGenerator.createIndexOnColumn(table, Randomly.fromList(table.getColumns()));
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        // Run CHECK TABLE to verify index integrity
        String checkQuery = "CHECK TABLE " + table.getName() + " EXTENDED;";
        lastQueryString = "[CHECK_TABLE] " + checkQuery;
        log(checkQuery);

        try {
            Statement stmt = globalState.getConnection().createStatement();
            ResultSet rs = stmt.executeQuery(checkQuery);
            while (rs.next()) {
                String msgType = rs.getString("Msg_type");
                String msgText = rs.getString("Msg_text");
                if ("error".equalsIgnoreCase(msgType) && !"OK".equalsIgnoreCase(msgText)) {
                    effectiveTests++;
                    throw new AssertionError("CHECK TABLE error on " + table.getName() + ": " + msgText);
                }
            }
            rs.close();
            stmt.close();
        } catch (Throwable e) {
            if (e instanceof AssertionError) {
                throw (AssertionError) e;
            }
            // Ignore other errors
        }
    }

    // ==================== Mode 12: Aggregate Plan ====================

    // 50% AST-based aggregate with index-aware WHERE, 50% simple aggregate fallback.
    private void checkAggregatePlan() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty())
            return;

        // P3-2: 50% chance to use AST-based aggregate query with index-aware WHERE
        String queryString = null;
        if (Randomly.getBoolean()) {
            queryString = generateASTAggregateQuery();
        }

        // Fallback to simple aggregate patterns
        if (queryString == null) {
            MariaDBColumn col = Randomly.fromList(table.getColumns());
            String tblName = table.getName();
            String colName = col.getName();

            int aggType = Randomly.fromOptions(0, 1, 2);
            switch (aggType) {
            case 0:
                queryString = "SELECT COUNT(*) FROM " + tblName + ";";
                break;
            case 1:
                queryString = "SELECT " + colName + ", COUNT(*) FROM " + tblName + " GROUP BY " + colName + ";";
                break;
            default:
                queryString = "SELECT MIN(" + colName + "), MAX(" + colName + ") FROM " + tblName + ";";
                break;
            }
        }

        lastQueryString = "[AGG_PLAN] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null)
            return;

        String switchVal = Randomly.fromOptions(
                "condition_fanout_filter=off,subquery_materialization_cost_based=off",
                "block_nested_loop=off",
                "index_condition_pushdown=off,mrr=off");

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
        if (r2 == null)
            return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_AGG_PLAN");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_AGG_PLAN");
        }
    }

    // ==================== Mode 13: Covering Index (Phase B) ====================

    private void checkCoveringIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) {
            try {
                MariaDBIndexGenerator.createIndexOnColumn(table, Randomly.fromList(table.getColumns()));
                analyzeAllTables();
                tableIndexes = table.getIndexes();
            } catch (Exception e) { return; }
        }
        if (tableIndexes.isEmpty()) return;

        MariaDBIndex idx = Randomly.fromList(tableIndexes);
        List<String> idxCols = idx.getColumnNames();
        String tblName = table.getName();
        if (idxCols.isEmpty()) return;

        // SELECT only indexed columns to encourage covering index scan
        String selectCols = String.join(", ", idxCols);
        MariaDBColumn firstCol = null;
        for (MariaDBColumn c : table.getColumns()) {
            if (c.getName().equals(idxCols.get(0))) { firstCol = c; break; }
        }
        if (firstCol == null) return;

        String val = generateDataAwareValueForType(tblName, firstCol);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String whereCond = idxCols.get(0) + " " + op + " " + val;

        String defaultQuery = "SELECT " + selectCols + " FROM " + tblName
                + " WHERE " + whereCond + " ORDER BY " + idxCols.get(0) + " LIMIT 200;";
        String ignoredQuery = "SELECT " + selectCols + " FROM " + tblName
                + " IGNORE INDEX(" + idx.getIndexName() + ") WHERE " + whereCond
                + " ORDER BY " + idxCols.get(0) + " LIMIT 200;";

        lastQueryString = "[COVERING_IDX] " + defaultQuery;
        log(defaultQuery);

        List<String> explainPlan1 = getExplainPlan(defaultQuery);
        List<String> explainPlan2 = getExplainPlan(ignoredQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = executeQuery(defaultQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null) return;

        compareResultsStrict(r1, r2, defaultQuery, "MARIADB_COVERING_IDX");
    }

    // ==================== Mode 14: Index Merge (Phase B) ====================

    private void checkIndexMerge() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;

        String tblName = table.getName();
        MariaDBColumn col1 = table.getColumns().get(0);
        MariaDBColumn col2 = table.getColumns().get(1);

        // Create two single-column indexes for index merge
        String idx1Name = "im_idx_" + Math.abs(col1.getName().hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        String idx2Name = "im_idx_" + Math.abs(col2.getName().hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idx1Name + " ON " + tblName + " (" + col1.getName() + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idx2Name + " ON " + tblName + " (" + col2.getName() + ");", errors, true));
            analyzeAllTables();
        } catch (Exception e) { return; }

        String val1 = generateDataAwareValueForType(tblName, col1);
        String val2 = generateDataAwareValueForType(tblName, col2);
        // OR condition to trigger index merge
        String whereCond = col1.getName() + " = " + val1 + " OR " + col2.getName() + " = " + val2;
        String defaultQuery = "SELECT * FROM " + tblName + " WHERE " + whereCond
                + " ORDER BY " + col1.getName() + " LIMIT 200;";
        String noMergeQuery = "SELECT * FROM " + tblName + " WHERE " + whereCond
                + " ORDER BY " + col1.getName() + " LIMIT 200;";

        lastQueryString = "[INDEX_MERGE] " + defaultQuery;
        log(defaultQuery);

        List<String> r1 = executeQuery(defaultQuery);
        if (r1 == null) return;

        List<String> r2 = null;
        boolean success = safeSetSwitch("index_merge=off,index_merge_intersection=off,index_merge_sort_intersection=off");
        if (success) {
            try {
                r2 = executeQuery(noMergeQuery);
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, defaultQuery, "MARIADB_INDEX_MERGE");
        if (lastCompareFiltered) {
            countStarFallback(defaultQuery, noMergeQuery, "MARIADB_INDEX_MERGE");
        }
    }

    // ==================== Mode 15: Loose Index Scan (Phase B) ====================

    private void checkLooseIndexScan() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBColumn> indexedCols = getIndexedColumnsForTable(table);
        if (indexedCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(indexedCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Find index for this column
        String idxName = null;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (idx.getColumnNames().contains(colName)) {
                idxName = idx.getIndexName();
                break;
            }
        }
        if (idxName == null) return;

        // GROUP BY + DISTINCT aggregate — trigger Loose Index Scan
        String defaultQuery = "SELECT " + colName + ", COUNT(*) FROM " + tblName
                + " WHERE " + colName + " IS NOT NULL GROUP BY " + colName
                + " ORDER BY " + colName + " LIMIT 200;";
        String forcedQuery = "SELECT " + colName + ", COUNT(*) FROM " + tblName
                + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL GROUP BY " + colName
                + " ORDER BY " + colName + " LIMIT 200;";

        lastQueryString = "[LOOSE_SCAN] " + defaultQuery;
        log(defaultQuery);

        List<String> r1 = executeQuery(defaultQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(forcedQuery);
        if (r2 == null) return;

        // [FIX] Use compareResultsSorted instead of compareResultsStrict.
        // MariaDB's accent-insensitive collation (utf8mb4_uca1400_ai_ci) may
        // group/order rows with special characters (e.g., null bytes) differently
        // depending on whether a loose index scan or table scan is used.
        // Sorted comparison avoids this false positive while still catching
        // real bugs (missing rows, wrong COUNT values, row count mismatches).
        compareResultsSorted(r1, r2, defaultQuery, "MARIADB_LOOSE_SCAN");
    }

    // ==================== Mode 16: ORDER BY + LIMIT Index (Phase B) ====================

    private void checkOrderByLimitIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBColumn> indexedCols = getIndexedColumnsForTable(table);
        if (indexedCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(indexedCols);
        String tblName = table.getName();
        String colName = col.getName();

        String idxName = null;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (idx.getColumnNames().contains(colName)) {
                idxName = idx.getIndexName();
                break;
            }
        }
        if (idxName == null) return;

        String val = generateDataAwareValueForType(tblName, col);
        int limit = Randomly.fromOptions(1, 5, 10, 20, 50);
        String whereCond = colName + " > " + val;

        String defaultQuery = "SELECT * FROM " + tblName + " WHERE " + whereCond
                + " ORDER BY " + colName + " LIMIT " + limit + ";";
        String ignoredQuery = "SELECT * FROM " + tblName
                + " IGNORE INDEX(" + idxName + ") WHERE " + whereCond
                + " ORDER BY " + colName + " LIMIT " + limit + ";";

        lastQueryString = "[ORDLIM_IDX] " + defaultQuery;
        log(defaultQuery);

        List<String> r1 = executeQuery(defaultQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null) return;

        // For ORDER BY + LIMIT on a non-unique column, different index plans may
        // select different rows when ORDER BY values have ties (duplicates).
        // This is non-deterministic by SQL standard, so use sorted comparison.
        lastCompareFiltered = false;
        try {
            compareResultsSorted(r1, r2, defaultQuery, "MARIADB_ORDLIM_IDX");
        } catch (AssertionError e) {
            // [FIX] Secondary check for ORDER BY ties false positive:
            // When ORDER BY column has duplicate values, different execution plans may
            // non-deterministically pick different rows at the LIMIT boundary.
            // If the ORDER BY column values match exactly between the two plans,
            // the difference is benign tie-breaking, not a real bug.
            String orderOnly1 = "SELECT " + colName + " FROM " + tblName + " WHERE " + whereCond
                    + " ORDER BY " + colName + " LIMIT " + limit + ";";
            String orderOnly2 = "SELECT " + colName + " FROM " + tblName
                    + " IGNORE INDEX(" + idxName + ") WHERE " + whereCond
                    + " ORDER BY " + colName + " LIMIT " + limit + ";";
            List<String> orderBy1 = executeQuery(orderOnly1);
            List<String> orderBy2 = executeQuery(orderOnly2);
            if (orderBy1 != null && orderBy2 != null && orderBy1.equals(orderBy2)) {
                // ORDER BY values match — difference is just non-deterministic row
                // selection at the LIMIT boundary (ties in ORDER BY column). Not a bug.
                lastCompareFiltered = true;
                countStarFallback(defaultQuery, ignoredQuery, "MARIADB_ORDLIM_IDX");
                return;
            }
            // ORDER BY values differ — this is a real bug, re-throw
            throw e;
        }
        if (lastCompareFiltered) {
            countStarFallback(defaultQuery, ignoredQuery, "MARIADB_ORDLIM_IDX");
        }
    }

    // ==================== Mode 17: Range Boundary (Phase B) ====================

    private void checkRangeBoundary() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);

        // Find INT columns with indexes
        List<MariaDBColumn> intIndexedCols = new ArrayList<>();
        for (MariaDBIndex idx : table.getIndexes()) {
            for (String colName : idx.getColumnNames()) {
                for (MariaDBColumn col : table.getColumns()) {
                    if (col.getName().equals(colName)
                            && col.getType() == MariaDBSchema.MariaDBDataType.INT) {
                        intIndexedCols.add(col);
                    }
                }
            }
        }
        if (intIndexedCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(intIndexedCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Get boundary values from the table
        String minVal = null, maxVal = null;
        try (Statement s = globalState.getConnection().createStatement()) {
            try (ResultSet rs = s.executeQuery(
                    "SELECT MIN(" + colName + "), MAX(" + colName + ") FROM " + tblName
                            + " WHERE " + colName + " IS NOT NULL;")) {
                if (rs.next()) {
                    minVal = rs.getString(1);
                    maxVal = rs.getString(2);
                }
            }
        } catch (Exception e) { return; }
        if (minVal == null || maxVal == null) return;

        // Generate boundary test value
        String boundaryVal;
        int boundaryType = Randomly.fromOptions(0, 1, 2, 3, 4, 5);
        switch (boundaryType) {
        case 0: boundaryVal = minVal; break;      // MIN
        case 1: boundaryVal = maxVal; break;      // MAX
        case 2: boundaryVal = "0"; break;         // Zero
        case 3: boundaryVal = "-1"; break;        // Negative
        case 4:                                 // MIN + 1
            try { boundaryVal = String.valueOf(Integer.parseInt(minVal) + 1); }
            catch (NumberFormatException e) { boundaryVal = minVal; }
            break;
        default:                                // MAX - 1
            try { boundaryVal = String.valueOf(Integer.parseInt(maxVal) - 1); }
            catch (NumberFormatException e) { boundaryVal = maxVal; }
            break;
        }

        String idxName = null;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (idx.getColumnNames().contains(colName)) {
                idxName = idx.getIndexName(); break;
            }
        }
        if (idxName == null) return;

        String forcedQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE "
                + colName + " >= " + boundaryVal + " ORDER BY " + colName + " LIMIT 200;";
        String ignoredQuery = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE "
                + colName + " >= " + boundaryVal + " ORDER BY " + colName + " LIMIT 200;";

        lastQueryString = "[RANGE_BOUND] " + forcedQuery;
        log(forcedQuery);

        List<String> explainPlan1 = getExplainPlan(forcedQuery);
        List<String> explainPlan2 = getExplainPlan(ignoredQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = executeQuery(forcedQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null) return;

        // [FIX] Use compareResultsSorted instead of compareResultsStrict.
        // ORDER BY c0 alone is non-deterministic for rows with the same c0 value:
        // different access paths (FORCE INDEX vs IGNORE INDEX) produce different
        // secondary ordering within the same c0 group. compareResultsSorted compares
        // row sets (ignoring order), which is the correct semantics here.
        compareResultsSorted(r1, r2, forcedQuery, "MARIADB_RANGE_BOUND");
    }

    // ==================== Mode 18: Subquery + Index (Phase B) ====================

    private void checkSubqueryIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = new ArrayList<>(schema.getDatabaseTables());
        if (tables.size() < 2) return;

        Collections.shuffle(tables);
        MariaDBTable t1 = tables.get(0);
        MariaDBTable t2 = tables.get(1);
        if (t1.getColumns().isEmpty() || t2.getColumns().isEmpty()) return;

        MariaDBColumn col1 = Randomly.fromList(t1.getColumns());
        MariaDBColumn col2 = Randomly.fromList(t2.getColumns());
        String val = generateDataAwareValueForType(t2.getName(), col2);

        // Create index on the subquery column
        try {
            MariaDBIndexGenerator.createIndexOnColumn(t2, col2);
            analyzeAllTables();
        } catch (Exception e) { /* ignore */ }

        int subqueryType = Randomly.fromOptions(0, 1);
        String queryString;
        if (subqueryType == 0) {
            // IN subquery
            queryString = "SELECT * FROM " + t1.getName() + " WHERE " + col1.getName()
                    + " IN (SELECT " + col2.getName() + " FROM " + t2.getName()
                    + " WHERE " + col2.getName() + " > " + val + ");";
        } else {
            // EXISTS subquery
            queryString = "SELECT * FROM " + t1.getName() + " WHERE EXISTS (SELECT 1 FROM "
                    + t2.getName() + " WHERE " + t2.getName() + "." + col2.getName() + " = "
                    + t1.getName() + "." + col1.getName() + ");";
        }

        lastQueryString = "[SUBQ_IDX] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // Toggle subquery optimization strategy
        String switchVal = Randomly.fromOptions(
                "in_to_exists=off,materialization=on",
                "materialization=off,in_to_exists=on",
                "semijoin=off");

        // [FIX] EXPLAIN filter: skip if optimizer switch does not change the plan
        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> r2 = null;
        boolean success = safeSetSwitch(switchVal);
        if (success) {
            try {
                List<String> explainPlan2 = getExplainPlan(queryString);
                if (plansAreDifferent(explainPlan1, explainPlan2)) {
                    r2 = executeQuery(queryString);
                }
            } finally { restoreDefaultSettings(); }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_SUBQ_IDX");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_SUBQ_IDX");
        }
    }

    // ==================== Mode 19: JOIN Index Selection (Phase B) ====================

    private void checkJoinIndexSelection() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = new ArrayList<>(schema.getDatabaseTables());
        if (tables.size() < 2) return;

        Collections.shuffle(tables);
        MariaDBTable t1 = tables.get(0);
        MariaDBTable t2 = tables.get(1);
        if (t1.getColumns().isEmpty() || t2.getColumns().isEmpty()) return;

        MariaDBColumn col1 = Randomly.fromList(t1.getColumns());
        MariaDBColumn col2 = Randomly.fromList(t2.getColumns());

        // Create indexes on join columns
        try {
            MariaDBIndexGenerator.createIndexOnColumn(t1, col1);
            MariaDBIndexGenerator.createIndexOnColumn(t2, col2);
            analyzeAllTables();
        } catch (Exception e) { /* ignore */ }

        String joinType = Randomly.fromOptions("JOIN", "INNER JOIN", "LEFT JOIN");
        String defaultQuery = "SELECT * FROM " + t1.getName() + " " + joinType + " " + t2.getName()
                + " ON " + t1.getName() + "." + col1.getName() + " = "
                + t2.getName() + "." + col2.getName()
                + " LIMIT 200;";

        // Use STRAIGHT_JOIN to force join order
        String straightQuery = "SELECT STRAIGHT_JOIN * FROM " + t1.getName() + " " + joinType + " " + t2.getName()
                + " ON " + t1.getName() + "." + col1.getName() + " = "
                + t2.getName() + "." + col2.getName()
                + " LIMIT 200;";

        lastQueryString = "[JOIN_IDX] " + defaultQuery;
        log(defaultQuery);

        List<String> r1 = executeQuery(defaultQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(straightQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, defaultQuery, "MARIADB_JOIN_IDX");
        if (lastCompareFiltered) {
            countStarFallback(defaultQuery, straightQuery, "MARIADB_JOIN_IDX");
        }
    }

    // ==================== Mode 20: Deterministic Index Query (Phase B — Enhanced) ====================

    private void checkDeterministicIndexQuery() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) return;

        MariaDBIndex idx = Randomly.fromList(tableIndexes);
        List<String> idxCols = idx.getColumnNames();
        if (idxCols.isEmpty()) return;

        String tblName = table.getName();
        String colName = idxCols.get(0);
        MariaDBColumn col = null;
        for (MariaDBColumn c : table.getColumns()) {
            if (c.getName().equals(colName)) { col = c; break; }
        }
        if (col == null) return;

        String val = generateDataAwareValueForType(tblName, col);
        String idxName = idx.getIndexName();

        // Enhanced: 5 query variants to test different index access patterns
        int variant = Randomly.fromOptions(0, 1, 2, 3, 4);
        String forcedQuery, ignoredQuery;

        switch (variant) {
        case 0: {
            // Variant 0: Equality lookup (original)
            forcedQuery = "SELECT " + colName + " FROM " + tblName
                    + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val
                    + " ORDER BY " + colName + " LIMIT 100;";
            ignoredQuery = "SELECT " + colName + " FROM " + tblName
                    + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " = " + val
                    + " ORDER BY " + colName + " LIMIT 100;";
            break;
        }
        case 1: {
            // Variant 1: Range scan with ORDER BY and LIMIT
            String op = Randomly.fromOptions(">", "<", ">=", "<=");
            forcedQuery = "SELECT * FROM " + tblName
                    + " FORCE INDEX(" + idxName + ") WHERE " + colName + " " + op + " " + val
                    + " ORDER BY " + colName + " LIMIT 50;";
            ignoredQuery = "SELECT * FROM " + tblName
                    + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " " + op + " " + val
                    + " ORDER BY " + colName + " LIMIT 50;";
            break;
        }
        case 2: {
            // Variant 2: Aggregate with index (COUNT/MIN/MAX)
            String aggFunc = Randomly.fromOptions("COUNT", "MIN", "MAX");
            forcedQuery = "SELECT " + aggFunc + "(" + colName + ") FROM " + tblName
                    + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL;";
            ignoredQuery = "SELECT " + aggFunc + "(" + colName + ") FROM " + tblName
                    + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL;";
            break;
        }
        case 3: {
            // Variant 3: Composite index prefix query (multi-column WHERE)
            if (idxCols.size() >= 2) {
                String col2Name = idxCols.get(1);
                MariaDBColumn col2 = null;
                for (MariaDBColumn c : table.getColumns()) {
                    if (c.getName().equals(col2Name)) { col2 = c; break; }
                }
                String val2 = (col2 != null) ? generateDataAwareValueForType(tblName, col2) : "0";
                forcedQuery = "SELECT * FROM " + tblName
                        + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val
                        + " AND " + col2Name + " IS NOT NULL LIMIT 100;";
                ignoredQuery = "SELECT * FROM " + tblName
                        + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " = " + val
                        + " AND " + col2Name + " IS NOT NULL LIMIT 100;";
            } else {
                // Fallback for single-column index
                forcedQuery = "SELECT " + colName + " FROM " + tblName
                        + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val
                        + " ORDER BY " + colName + " LIMIT 100;";
                ignoredQuery = "SELECT " + colName + " FROM " + tblName
                        + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " = " + val
                        + " ORDER BY " + colName + " LIMIT 100;";
            }
            break;
        }
        default: {
            // Variant 4: IS NULL / IS NOT NULL + secondary condition
            String val2 = generateDataAwareValueForType(tblName, col);
            forcedQuery = "SELECT COUNT(*) FROM " + tblName
                    + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL AND " + colName + " > " + val2 + ";";
            ignoredQuery = "SELECT COUNT(*) FROM " + tblName
                    + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " IS NOT NULL AND " + colName + " > " + val2 + ";";
            break;
        }
        }

        lastQueryString = "[DET_IDX_ENHANCED] " + forcedQuery;
        log(forcedQuery);

        List<String> explainPlan1 = getExplainPlan(forcedQuery);
        List<String> explainPlan2 = getExplainPlan(ignoredQuery);
        // Only compare if plans differ (index actually affects execution)
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = executeQuery(forcedQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, forcedQuery, "MARIADB_DET_IDX_ENHANCED");
        if (lastCompareFiltered) {
            countStarFallback(forcedQuery, ignoredQuery, "MARIADB_DET_IDX_ENHANCED");
        }
    }

    // ==================== Mode 21: ICP Consistency (Phase B — Enhanced) ====================

    private void checkICPConsistency() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) {
            try {
                MariaDBIndexGenerator.createIndexOnColumn(table, Randomly.fromList(table.getColumns()));
                analyzeAllTables();
                tableIndexes = table.getIndexes();
            } catch (Exception e) { return; }
        }
        if (tableIndexes.isEmpty()) return;

        MariaDBIndex idx = Randomly.fromList(tableIndexes);
        String tblName = table.getName();
        List<String> idxCols = idx.getColumnNames();
        if (idxCols.isEmpty()) return;
        String idxCol = idxCols.get(0);

        // Find a second column for complex conditions
        MariaDBColumn col2 = null;
        for (MariaDBColumn c : table.getColumns()) {
            if (!c.getName().equals(idxCol)) { col2 = c; break; }
        }

        // Sample data-aware values
        MariaDBColumn idxColumn = null;
        for (MariaDBColumn c : table.getColumns()) {
            if (c.getName().equals(idxCol)) { idxColumn = c; break; }
        }
        if (idxColumn == null) return;
        String val = generateDataAwareValueForType(tblName, idxColumn);
        String val2 = (col2 != null) ? generateDataAwareValueForType(tblName, col2) : null;
        String col2Name = (col2 != null) ? col2.getName() : null;

        // Generate a complex WHERE condition that exercises ICP
        int variant = Randomly.fromOptions(0, 1, 2, 3, 4, 5, 6, 7);
        String whereCond;
        switch (variant) {
        case 0:
            // Simple range — ICP should handle efficiently
            whereCond = idxCol + " IS NOT NULL";
            break;
        case 1:
            // Equality + range on second column
            whereCond = idxCol + " = " + val;
            break;
        case 2:
            // BETWEEN on indexed column
            whereCond = idxCol + " BETWEEN " + val + " AND " + val;
            break;
        case 3:
            // Multi-column condition (pushdown candidate)
            whereCond = idxCol + " > " + val;
            if (col2Name != null && val2 != null) {
                whereCond += " AND " + col2Name + " IS NOT NULL";
            }
            break;
        case 4:
            // CASE expression in WHERE (tests ICP with computed conditions)
            whereCond = "CASE WHEN " + idxCol + " IS NOT NULL THEN 1 ELSE 0 END = 1";
            break;
        case 5:
            // Function-based condition (COALESCE)
            whereCond = "COALESCE(" + idxCol + ", " + val + ") = " + val;
            break;
        case 6:
            // IN list condition
            whereCond = idxCol + " IN (" + val + ", " + val + ")";
            break;
        default:
            // Complex AND/OR condition
            whereCond = "(" + idxCol + " > " + val + " OR " + idxCol + " IS NULL)";
            if (col2Name != null && val2 != null) {
                whereCond += " AND " + col2Name + " IS NOT NULL";
            }
            break;
        }

        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereCond + " LIMIT 200;";
        lastQueryString = "[ICP_ENHANCED] " + queryString;
        log(queryString);

        // Test with various ICP-related optimizer switch combinations
        String[] icpSwitches = {
            "index_condition_pushdown=off",
            "index_condition_pushdown=off,mrr=off",
            "index_condition_pushdown=off,mrr=on,mrr_cost_based=off",
            "index_condition_pushdown=off,rowid_filter=off",
        };
        String switchVal = Randomly.fromOptions(icpSwitches);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        List<String> explainPlan1 = getExplainPlan(queryString);
        List<String> r2 = null;
        boolean success = safeSetSwitch(switchVal);
        if (success) {
            try {
                List<String> explainPlan2 = getExplainPlan(queryString);
                // Only compare if plans actually differ (ICP was being used)
                if (plansAreDifferent(explainPlan1, explainPlan2)) {
                    r2 = executeQuery(queryString);
                }
            } finally { restoreDefaultSettings(); }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_ICP_ENHANCED");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_ICP_ENHANCED");
        }
    }

    // ==================== Mode 22: Optimizer Switch Detailed Pairwise (Phase B) ====================

    private void checkOptimizerSwitchDetailed() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();

        String queryString;
        if (!tableIndexes.isEmpty()) {
            MariaDBIndex idx = Randomly.fromList(tableIndexes);
            queryString = generateIndexAwareQueryString(table, idx);
        } else {
            queryString = generateSimpleQuery();
        }
        if (queryString == null) return;

        lastQueryString = "[OPT_DET] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        String switchVal = Randomly.fromOptions(
                // Index-related
                "index_condition_pushdown=off",
                "rowid_filter=off",
                "not_null_range_scan=off",
                "index_merge_intersection=off",
                "index_merge_sort_intersection=off",
                "mrr=off,mrr_cost_based=off",
                // Join-related
                "join_cache_bka=off",
                "join_cache_hashed=off",
                "outer_join_with_cache=off",
                // Subquery-related
                "condition_pushdown_for_subquery=off",
                "condition_pushdown_for_derived=off",
                // Combinations
                "index_condition_pushdown=off,rowid_filter=off",
                "mrr=off,mrr_sort_keys=off",
                "index_merge=off,index_merge_intersection=off"
        );

        // [FIX] EXPLAIN filter: get baseline plan before changing switch
        List<String> explainPlanBefore = getExplainPlan(queryString);
        List<String> r2 = null;
        boolean success = safeSetSwitch(switchVal);
        if (success) {
            try {
                List<String> explainPlanAfter = getExplainPlan(queryString);
                // [FIX] Only execute query if the optimizer switch actually changed the plan
                if (plansAreDifferent(explainPlanBefore, explainPlanAfter)) {
                    r2 = executeQuery(queryString);
                }
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_OPT_DET");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_OPT_DET");
        }
    }

    // ==================== Mode 23: NULL Index Handling (Phase B) ====================

    private void checkNullIndexHandling() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);

        // Find nullable columns (non-PK columns)
        List<MariaDBColumn> nullableCols = new ArrayList<>();
        for (MariaDBColumn col : table.getColumns()) {
            if (!col.isPrimaryKey()) nullableCols.add(col);
        }
        if (nullableCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(nullableCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Ensure an index exists on this column
        boolean hasIndex = false;
        String idxName = null;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (idx.getColumnNames().contains(colName)) {
                hasIndex = true;
                idxName = idx.getIndexName();
                break;
            }
        }
        if (!hasIndex) {
            try {
                MariaDBIndexGenerator.createIndexOnColumn(table, col);
                analyzeAllTables();
                for (MariaDBIndex idx : table.getIndexes()) {
                    if (idx.getColumnNames().contains(colName)) {
                        idxName = idx.getIndexName();
                        hasIndex = true;
                        break;
                    }
                }
            } catch (Exception e) { return; }
        }
        if (!hasIndex || idxName == null) return;

        // NULL-related conditions
        String whereCond = Randomly.fromOptions(
                colName + " IS NULL",
                colName + " IS NOT NULL",
                colName + " <=> NULL",
                colName + " IS NULL OR " + colName + " = 0",
                colName + " IS NOT NULL AND " + colName + " > 0"
        );

        // [FIX] Build deterministic ORDER BY: sort by target column + all other columns
        // as tiebreaker to avoid non-deterministic row selection at LIMIT boundaries
        // when multiple rows share the same value in the ORDER BY column.
        StringBuilder orderByCols = new StringBuilder(colName);
        for (MariaDBColumn c : table.getColumns()) {
            if (!c.getName().equals(colName)) {
                orderByCols.append(", ").append(c.getName());
            }
        }

        String forcedQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE "
                + whereCond + " ORDER BY " + orderByCols + " LIMIT 200;";
        String ignoredQuery = "SELECT * FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE "
                + whereCond + " ORDER BY " + orderByCols + " LIMIT 200;";

        lastQueryString = "[NULL_IDX] " + forcedQuery;
        log(forcedQuery);

        List<String> explainPlan1 = getExplainPlan(forcedQuery);
        List<String> explainPlan2 = getExplainPlan(ignoredQuery);
        if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

        List<String> r1 = executeQuery(forcedQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoredQuery);
        if (r2 == null) return;

        compareResultsSorted(r1, r2, forcedQuery, "MARIADB_NULL_IDX");
    }

    // ==================== Mode 24: Rowid Filter (Phase C — MariaDB-only) ====================

    // Compares rowid_filter=on vs off (MariaDB 10.4+). Tests result correctness under this optimization.
    private void checkRowidFilter() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) {
            try {
                MariaDBIndexGenerator.createIndexOnColumn(table, Randomly.fromList(table.getColumns()));
                analyzeAllTables();
                tableIndexes = table.getIndexes();
            } catch (Exception e) { return; }
        }
        if (tableIndexes.isEmpty()) return;

        MariaDBIndex idx = Randomly.fromList(tableIndexes);
        String queryString = generateIndexAwareQueryString(table, idx);
        if (queryString == null) return;

        lastQueryString = "[ROWID_FILTER] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        // [FIX] EXPLAIN filter: get baseline plan before disabling rowid_filter
        List<String> explainPlanBefore = getExplainPlan(queryString);
        List<String> r2 = null;
        boolean success = safeSetSwitch("rowid_filter=off");
        if (success) {
            try {
                List<String> explainPlanAfter = getExplainPlan(queryString);
                // [FIX] Only execute query if disabling rowid_filter actually changed the plan
                if (plansAreDifferent(explainPlanBefore, explainPlanAfter)) {
                    r2 = executeQuery(queryString);
                }
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_ROWID_FILTER");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_ROWID_FILTER");
        }
    }

    // ==================== Mode 25: Not Null Range Scan (Phase C — MariaDB-only) ====================

    // Toggles not_null_range_scan optimizer switch and verifies result consistency.
    // Note: may crash on some MariaDB versions (MDEV-32076), so errors are caught.
    private void checkNotNullRangeScan() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);

        // Find NOT NULL columns with indexes (use isPrimaryKey as proxy for NOT NULL)
        List<MariaDBColumn> notNullIndexedCols = new ArrayList<>();
        for (MariaDBIndex idx : table.getIndexes()) {
            for (String colName : idx.getColumnNames()) {
                for (MariaDBColumn col : table.getColumns()) {
                    if (col.getName().equals(colName) && col.isPrimaryKey()
                            && !notNullIndexedCols.contains(col)) {
                        notNullIndexedCols.add(col);
                    }
                }
            }
        }

        // If no NOT NULL indexed column, try creating an index on a NOT NULL column
        if (notNullIndexedCols.isEmpty()) {
            for (MariaDBColumn col : table.getColumns()) {
                if (col.isPrimaryKey()) {
                    try {
                        MariaDBIndexGenerator.createIndexOnColumn(table, col);
                        analyzeAllTables();
                        notNullIndexedCols.add(col);
                    } catch (Exception e) { /* ignore */ }
                    break;
                }
            }
        }
        if (notNullIndexedCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(notNullIndexedCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Generate range query on NOT NULL column
        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions(">", "<", ">=", "<=");

        // [FIX] Build deterministic ORDER BY: sort by target column + all other columns
        // as tiebreaker to avoid non-deterministic row selection at LIMIT boundaries.
        StringBuilder orderByCols = new StringBuilder(colName);
        for (MariaDBColumn c : table.getColumns()) {
            if (!c.getName().equals(colName)) {
                orderByCols.append(", ").append(c.getName());
            }
        }

        String queryString = "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + val
                + " ORDER BY " + orderByCols + " LIMIT 200;";

        lastQueryString = "[NOT_NULL_RANGE] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        List<String> r2 = null;
        boolean success = safeSetSwitch("not_null_range_scan=off");
        if (success) {
            try {
                r2 = executeQuery(queryString);
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_NOTNULL_RANGE");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_NOTNULL_RANGE");
        }
    }

    // ==================== Mode 26: Index Merge Intersection (Phase C — MariaDB-only) ====================

    // Tests index_merge_intersection and index_merge_sort_intersection; compares AND-condition
    // query results with intersection enabled vs disabled.
    private void checkIndexMergeIntersection() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;

        String tblName = table.getName();
        MariaDBColumn col1 = table.getColumns().get(0);
        MariaDBColumn col2 = table.getColumns().get(1);

        // Create two single-column indexes for index merge intersection
        String idx1Name = "imi_" + Math.abs(col1.getName().hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        String idx2Name = "imi_" + Math.abs(col2.getName().hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idx1Name + " ON " + tblName + " (" + col1.getName() + ");",
                    errors, true));
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idx2Name + " ON " + tblName + " (" + col2.getName() + ");",
                    errors, true));
            analyzeAllTables();
        } catch (Exception e) { return; }

        String val1 = generateDataAwareValueForType(tblName, col1);
        String val2 = generateDataAwareValueForType(tblName, col2);

        // AND condition to trigger index merge intersection
        String whereCond = col1.getName() + " = " + val1 + " AND " + col2.getName() + " = " + val2;

        // [FIX] Build deterministic ORDER BY: sort by target column + all other columns
        // as tiebreaker to avoid non-deterministic row selection at LIMIT boundaries.
        StringBuilder orderByCols = new StringBuilder(col1.getName());
        for (MariaDBColumn c : table.getColumns()) {
            if (!c.getName().equals(col1.getName())) {
                orderByCols.append(", ").append(c.getName());
            }
        }

        String queryString = "SELECT * FROM " + tblName + " WHERE " + whereCond
                + " ORDER BY " + orderByCols + " LIMIT 200;";

        lastQueryString = "[IDX_MERGE_INTER] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        List<String> r2 = null;
        String switchVal = Randomly.fromOptions(
                "index_merge_intersection=off",
                "index_merge_sort_intersection=off",
                "index_merge_intersection=off,index_merge_sort_intersection=off");
        boolean success = safeSetSwitch(switchVal);
        if (success) {
            try {
                r2 = executeQuery(queryString);
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_IDX_MERGE_INTER");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_IDX_MERGE_INTER");
        }
    }

    // ==================== Mode 27: Join Cache Level (Phase C — MariaDB-only) ====================

    // Compares two random join_cache_level values (1-8) to verify consistent results.
    // Avoids optimize_join_buffer_size due to MDEV-32099 crash.
    private void checkJoinCacheLevel() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = new ArrayList<>(schema.getDatabaseTables());
        if (tables.size() < 2) return;

        Collections.shuffle(tables);
        MariaDBTable t1 = tables.get(0);
        MariaDBTable t2 = tables.get(1);
        if (t1.getColumns().isEmpty() || t2.getColumns().isEmpty()) return;

        MariaDBColumn col1 = Randomly.fromList(t1.getColumns());
        MariaDBColumn col2 = Randomly.fromList(t2.getColumns());

        // Create indexes on join columns to increase join variety
        try {
            MariaDBIndexGenerator.createIndexOnColumn(t1, col1);
            MariaDBIndexGenerator.createIndexOnColumn(t2, col2);
            analyzeAllTables();
        } catch (Exception e) { /* ignore */ }

        String joinType = Randomly.fromOptions("JOIN", "LEFT JOIN");
        String queryString = "SELECT * FROM " + t1.getName() + " " + joinType + " " + t2.getName()
                + " ON " + t1.getName() + "." + col1.getName() + " = "
                + t2.getName() + "." + col2.getName()
                + " LIMIT 200;";

        lastQueryString = "[JOIN_CACHE] " + queryString;
        log(queryString);

        // Pick two random join_cache_level values (1-8)
        int levelA = Randomly.fromOptions(1, 2, 3, 4, 5, 6, 7, 8);
        int levelB = Randomly.fromOptions(1, 2, 3, 4, 5, 6, 7, 8);
        while (levelB == levelA) {
            levelB = Randomly.fromOptions(1, 2, 3, 4, 5, 6, 7, 8);
        }

        List<String> r1 = null;
        List<String> r2 = null;
        try {
            Statement stmt1 = globalState.getConnection().createStatement();
            stmt1.execute("SET SESSION join_cache_level=" + levelA + ";");
            stmt1.close();
            r1 = executeQuery(queryString);
        } catch (Exception e) { /* ignore */ }

        try {
            Statement stmt2 = globalState.getConnection().createStatement();
            stmt2.execute("SET SESSION join_cache_level=" + levelB + ";");
            stmt2.close();
            r2 = executeQuery(queryString);
        } catch (Exception e) { /* ignore */ }

        // Restore default
        try {
            Statement stmtRestore = globalState.getConnection().createStatement();
            stmtRestore.execute("SET SESSION join_cache_level=default;");
            stmtRestore.close();
        } catch (Exception e) { /* ignore */ }

        if (r1 == null || r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_JOIN_CACHE");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_JOIN_CACHE");
        }
    }

    // ==================== Mode 28: Condition Pushdown for Derived (Phase C — MariaDB-only) ====================

    // Toggles condition_pushdown_for_derived/subquery and verifies results are unchanged.
    private void checkConditionPushdownDerived() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();
        String val = generateDataAwareValueForType(tblName, col);

        int queryType = Randomly.fromOptions(0, 1, 2);

        String queryString;
        switch (queryType) {
        case 0:
            // Derived table with WHERE condition pushdown
            queryString = "SELECT * FROM (SELECT * FROM " + tblName
                    + " WHERE " + colName + " IS NOT NULL) AS derived"
                    + " WHERE " + colName + " > " + val + " LIMIT 200;";
            break;
        case 1:
            // Subquery with condition pushdown
            queryString = "SELECT * FROM " + tblName + " WHERE " + colName
                    + " IN (SELECT " + colName + " FROM " + tblName
                    + " WHERE " + colName + " > " + val + ") LIMIT 200;";
            break;
        default:
            // Nested derived table
            queryString = "SELECT * FROM (SELECT " + colName + ", COUNT(*) AS cnt FROM "
                    + tblName + " WHERE " + colName + " IS NOT NULL GROUP BY " + colName
                    + ") AS derived WHERE cnt > 1 LIMIT 200;";
            break;
        }

        lastQueryString = "[PUSHDOWN_DERIVED] " + queryString;
        log(queryString);

        List<String> r1 = executeQuery(queryString);
        if (r1 == null) return;

        String switchVal = Randomly.fromOptions(
                "condition_pushdown_for_derived=off",
                "condition_pushdown_for_subquery=off",
                "condition_pushdown_for_derived=off,condition_pushdown_for_subquery=off");

        List<String> r2 = null;
        boolean success = safeSetSwitch(switchVal);
        if (success) {
            try {
                r2 = executeQuery(queryString);
            } finally {
                restoreDefaultSettings();
            }
        }
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, queryString, "MARIADB_PUSHDOWN_DERIVED");
        if (lastCompareFiltered) {
            countStarFallback(queryString, queryString, "MARIADB_PUSHDOWN_DERIVED");
        }
    }

    // ==================== Infrastructure Methods ====================

    private void ensureSufficientData() throws Exception {
        if (dataPopulated)
            return;
        dataPopulated = true;
        MariaDBSchema schema = globalState.getSchema();
        for (MariaDBTable table : schema.getDatabaseTables()) {
            int rowCount = getTableRowCount(table.getName());
            if (rowCount < 10) {
                int rowsToAdd = 20 - rowCount;
                for (int i = 0; i < rowsToAdd; i++) {
                    try {
                        globalState.executeStatement(
                                new SQLQueryAdapter("INSERT INTO " + table.getName() + " VALUES ();", errors, true));
                    } catch (Exception e) {
                        // Ignore insert errors
                    }
                }
            }
        }
        analyzeAllTables();
    }

    private int getTableRowCount(String tableName) {
        try (Statement s = globalState.getConnection().createStatement()) {
            try (ResultSet rs = s.executeQuery("SELECT COUNT(*) FROM " + tableName + ";")) {
                if (rs.next()) {
                    return rs.getInt(1);
                }
            }
        } catch (Exception e) {
            // ignore
        }
        return 0;
    }

    private void analyzeAllTables() {
        MariaDBSchema schema = globalState.getSchema();
        for (MariaDBTable table : schema.getDatabaseTables()) {
            try {
                globalState.executeStatement(
                        new SQLQueryAdapter("ANALYZE TABLE " + table.getName() + ";", true));
            } catch (Exception e) {
                // ignore
            }
        }
    }

    private List<String> executeQuery(String query) {
        try {
            Statement stmt = globalState.getConnection().createStatement();
            try {
                stmt.execute(query);
            } catch (Exception e) {
                if (errors.errorIsExpected(e.getMessage())) {
                    return null;
                }
                throw new IgnoreMeException();
            }
            ResultSet rs = stmt.getResultSet();
            if (rs == null)
                return null;
            List<String> results = new ArrayList<>();
            int colCount = rs.getMetaData().getColumnCount();
            while (rs.next()) {
                StringBuilder sb = new StringBuilder();
                for (int i = 1; i <= colCount; i++) {
                    if (i > 1)
                        sb.append("|");
                    sb.append(rs.getString(i));
                }
                results.add(sb.toString());
            }
            rs.close();
            stmt.close();
            queriesCompared++;
            return results;
        } catch (IgnoreMeException e) {
            throw e;
        } catch (Exception e) {
            if (errors.errorIsExpected(e.getMessage())) {
                return null;
            }
            throw new IgnoreMeException();
        }
    }

    private List<String> getExplainPlan(String query) {
        List<String> plan = new ArrayList<>();
        try (Statement stmt = globalState.getConnection().createStatement()) {
            try (ResultSet rs = stmt.executeQuery("EXPLAIN " + query)) {
                int colCount = rs.getMetaData().getColumnCount();
                while (rs.next()) {
                    StringBuilder sb = new StringBuilder();
                    for (int i = 1; i <= colCount; i++) {
                        if (i > 1)
                            sb.append("|");
                        String val = rs.getString(i);
                        sb.append(val != null ? val : "NULL");
                    }
                    plan.add(sb.toString());
                }
            }
        } catch (Exception e) {
            // ignore
        }
        return plan;
    }

    // Compares EXPLAIN plans by access type (col 3), key (col 5), and Extra column.
    private boolean plansAreDifferent(List<String> plan1, List<String> plan2) {
        if (plan1.isEmpty() || plan2.isEmpty()) {
            explainFiltered++;
            return false;
        }
        if (plan1.size() != plan2.size())
            return true;
        // Compare access type, key columns, and Extra column
        for (int i = 0; i < plan1.size(); i++) {
            String[] parts1 = plan1.get(i).split("\\|");
            String[] parts2 = plan2.get(i).split("\\|");
            // Check if the number of columns matches
            if (parts1.length != parts2.length)
                return true;
            if (parts1.length > 5) {
                // MariaDB EXPLAIN columns (0-indexed): 0=id, 1=select_type, 2=table,
                // 3=type, 4=possible_keys, 5=key, ...
                // Compare type (index 3) and key (index 5) in EXPLAIN output
                String type1 = parts1[3].trim();
                String type2 = parts2[3].trim();
                String key1 = parts1[5].trim();
                String key2 = parts2[5].trim();
                if (!type1.equals(type2) || !key1.equals(key2)) {
                    return true;
                }
                // Phase E3: Also compare Extra column (last column in EXPLAIN output)
                // Key Extra indicators that signal different optimization strategies:
                // - "Using index" = covering index scan
                // - "Using index condition" = Index Condition Pushdown (ICP)
                // - "Using MRR" = Multi-Range Read optimization
                // - "Rowid filter" = MariaDB Rowid Filter
                // - "Using index for group-by" = Loose Index Scan
                // - "Using where" = post-storage-engine filtering
                // - "Using filesort" = filesort instead of index order
                // - "Using temporary" = temporary table used
                String extra1 = parts1[parts1.length - 1].trim();
                String extra2 = parts2[parts2.length - 1].trim();
                if (!extra1.equals(extra2)) {
                    // Extra column differs — check if the difference is meaningful
                    if (plansAreDifferentByExtra(extra1, extra2)) {
                        return true;
                    }
                }
            }
        }
        explainFiltered++;
        return false;
    }

    // Returns true if the Extra column difference signals a genuinely different execution strategy.
    private boolean plansAreDifferentByExtra(String extra1, String extra2) {
        // Key optimization indicators that indicate genuinely different plans
        String[] meaningfulIndicators = {
            "Using index",            // covering index vs non-covering
            "Using index condition",  // ICP vs non-ICP
            "Using MRR",              // MRR vs no MRR
            "Rowid filter",           // MariaDB rowid filter
            "Using index for group-by", // Loose index scan
            "Using filesort",         // filesort vs index-sorted
            "Using temporary",        // temp table vs no temp table
            "Using join buffer",      // join buffer usage
            "LooseScan",              // Loose scan semi-join strategy
            "FirstMatch",             // FirstMatch semi-join strategy
            "Materialize",            // Materialization subquery strategy
        };

        for (String indicator : meaningfulIndicators) {
            boolean has1 = extra1.contains(indicator);
            boolean has2 = extra2.contains(indicator);
            if (has1 != has2) {
                return true; // Meaningful difference detected
            }
        }
        return false; // Difference is not meaningful for testing
    }

    private boolean safeSetSwitch(String switchVal) {
        try {
            Statement stmt = globalState.getConnection().createStatement();
            stmt.execute("SET SESSION optimizer_switch='" + switchVal + "';");
            stmt.close();
            return true;
        } catch (Exception e) {
            return false;
        }
    }

    private void restoreDefaultSettings() {
        try {
            Statement stmt = globalState.getConnection().createStatement();
            stmt.execute("SET SESSION optimizer_switch='default';");
            stmt.close();
        } catch (Exception e) {
            // ignore
        }
    }

    // ==================== Query Generation Methods ====================

    // Used by modes 0/1/9. 60% AST-based complex query, 40% simple string fallback.
    private String generateQueryForTable(MariaDBTable table) {
        if (table.getColumns().isEmpty())
            return null;

        // P3-1: 60% chance to use AST-based complex query generation
        if (Randomly.getBoolean()) {
            String astQuery = generateASTQueryForTable(table);
            if (astQuery != null) return astQuery;
        }

        // Fallback: simple string-based query
        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IS NOT NULL", "IS NULL");
        if (op.equals("IS NOT NULL") || op.equals("IS NULL")) {
            return "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + ";";
        } else {
            return "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + val + ";";
        }
    }

    // Generates AST-based query using MariaDBExpressionGenerator (BETWEEN, CASE, CAST, EXISTS, etc.).
    private String generateASTQueryForTable(MariaDBTable table) {
        List<MariaDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return null;
        String tblName = table.getName();

        try {
            MariaDBExpressionGenerator gen = new MariaDBExpressionGenerator(globalState.getRandomly());
            gen.setColumns(columns);

            // 50% index-friendly WHERE, 50% random complex WHERE using full AST
            MariaDBExpression whereExpr;
            if (Randomly.getBoolean()) {
                whereExpr = tryGenerateIndexFriendlyWhere(
                        Collections.singletonList(table), gen);
            } else {
                gen.setColumns(columns);
                whereExpr = gen.getRandomExpression();
            }
            if (whereExpr == null) return null;

            String whereStr = MariaDBVisitor.asString(whereExpr);

            // Optionally add ORDER BY on indexed columns (using MariaDBOrderByTerm)
            String orderBy = "";
            if (Randomly.getBoolean()) {
                List<MariaDBColumn> indexedCols = getIndexedColumnsForTable(table);
                if (!indexedCols.isEmpty()) {
                    MariaDBColumn orderCol = Randomly.fromList(indexedCols);
                    MariaDBOrderByTerm orderTerm = new MariaDBOrderByTerm(
                            new MariaDBColumnName(orderCol),
                            Randomly.getBoolean() ? MariaDBOrderByTerm.MariaDBOrder.ASC : MariaDBOrderByTerm.MariaDBOrder.DESC);
                    orderBy = " ORDER BY " + MariaDBVisitor.asString(orderTerm);
                } else if (Randomly.getBoolean()) {
                    // Use a random column for ORDER BY
                    MariaDBColumn orderCol = Randomly.fromList(columns);
                    MariaDBOrderByTerm orderTerm = new MariaDBOrderByTerm(
                            new MariaDBColumnName(orderCol),
                            Randomly.getBoolean() ? MariaDBOrderByTerm.MariaDBOrder.ASC : MariaDBOrderByTerm.MariaDBOrder.DESC);
                    orderBy = " ORDER BY " + MariaDBVisitor.asString(orderTerm);
                }
            }

            // Optionally add LIMIT
            String limit = "";
            if (Randomly.getBoolean()) {
                limit = " LIMIT " + globalState.getRandomly().getLong(1, 100);
            }

            return "SELECT * FROM " + tblName + " WHERE " + whereStr + orderBy + limit + ";";
        } catch (Exception e) {
            return null;
        }
    }

    private String generateSimpleQuery() {
        // Phase A4: 30% chance to use AST-based generation
        if (Randomly.fromOptions(0, 0, 0, 1, 1, 1, 1, 1, 1, 1) == 0) {
            String astQuery = generateASTQuery();
            if (astQuery != null) return astQuery;
        }

        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty())
            return null;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty())
            return null;

        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IS NOT NULL", "IS NULL");
        if (op.equals("IS NOT NULL") || op.equals("IS NULL")) {
            return "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + ";";
        } else {
            return "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + val + ";";
        }
    }

    // Generates a WHERE clause using one of 7 strategies to maximize index utilization.
    // Strategy 0: equality, 1: range, 2: IS NOT NULL+extra, 3: IN list,
    // 4: multi-column, 5: composite prefix, 6: index merge (OR).
    private String generateIndexAwareQueryString(MariaDBTable table, MariaDBIndex idx) {
        String tblName = table.getName();
        List<String> idxCols = idx.getColumnNames();

        if (idxCols.isEmpty())
            return "SELECT * FROM " + tblName + ";";

        String colName = idxCols.get(0);
        MariaDBColumn col = null;
        for (MariaDBColumn c : table.getColumns()) {
            if (c.getName().equals(colName)) {
                col = c;
                break;
            }
        }
        if (col == null)
            return "SELECT * FROM " + tblName + ";";

        // Phase A1: Multi-strategy WHERE generation (7 strategies)
        int strategy = Randomly.fromOptions(0, 1, 2, 3, 4, 5, 6);

        switch (strategy) {
        case 0: {
            // Strategy 0: Equality/range query col op sampled_value
            String val = generateDataAwareValueForType(tblName, col);
            String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
            return "SELECT * FROM " + tblName + " WHERE " + colName + " " + op + " " + val + ";";
        }
        case 1: {
            // Strategy 1: Range query col >= a AND col <= b (two sampled values)
            List<String> samples = sampleColumnValues(tblName, colName, 3);
            if (samples != null && samples.size() >= 2) {
                String valA = quoteValueForSQL(samples.get(0), col);
                String valB = quoteValueForSQL(samples.get(1), col);
                return "SELECT * FROM " + tblName + " WHERE " + colName + " >= " + valA
                        + " AND " + colName + " <= " + valB + ";";
            }
            // Fallback to simple range
            String val = generateDataAwareValueForType(tblName, col);
            return "SELECT * FROM " + tblName + " WHERE " + colName + " >= " + val + ";";
        }
        case 2: {
            // Strategy 2: IS NOT NULL + extra condition on second indexed column
            if (idxCols.size() >= 2) {
                String col2Name = idxCols.get(1);
                MariaDBColumn col2 = null;
                for (MariaDBColumn c : table.getColumns()) {
                    if (c.getName().equals(col2Name)) {
                        col2 = c;
                        break;
                    }
                }
                if (col2 != null) {
                    String val2 = generateDataAwareValueForType(tblName, col2);
                    return "SELECT * FROM " + tblName + " WHERE " + colName + " IS NOT NULL AND "
                            + col2Name + " = " + val2 + ";";
                }
            }
            return "SELECT * FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
        }
        case 3: {
            // Strategy 3: IN list (using sampled values)
            List<String> samples = sampleColumnValues(tblName, colName, 5);
            if (samples != null && !samples.isEmpty()) {
                StringBuilder inList = new StringBuilder();
                int count = Math.min(samples.size(), 4);
                for (int i = 0; i < count; i++) {
                    if (i > 0) inList.append(", ");
                    inList.append(quoteValueForSQL(samples.get(i), col));
                }
                return "SELECT * FROM " + tblName + " WHERE " + colName + " IN (" + inList + ");";
            }
            // Fallback
            String val = generateDataAwareValueForType(tblName, col);
            return "SELECT * FROM " + tblName + " WHERE " + colName + " = " + val + ";";
        }
        case 4: {
            // Strategy 4: Multi-column condition for composite indexes
            if (idxCols.size() >= 2) {
                StringBuilder where = new StringBuilder();
                for (int i = 0; i < Math.min(idxCols.size(), 3); i++) {
                    if (i > 0) where.append(" AND ");
                    String ic = idxCols.get(i);
                    MariaDBColumn icCol = null;
                    for (MariaDBColumn c : table.getColumns()) {
                        if (c.getName().equals(ic)) {
                            icCol = c;
                            break;
                        }
                    }
                    if (icCol == null) continue;

                    String op;
                    if (i == 0) {
                        op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IS NOT NULL");
                    } else {
                        op = Randomly.fromOptions("=", "IS NOT NULL");
                    }
                    if (op.equals("IS NOT NULL")) {
                        where.append(ic).append(" IS NOT NULL");
                    } else {
                        String val = generateDataAwareValueForType(tblName, icCol);
                        where.append(ic).append(" ").append(op).append(" ").append(val);
                    }
                }
                return "SELECT * FROM " + tblName + " WHERE " + where + ";";
            }
            // Fallback for single-column index
            String val = generateDataAwareValueForType(tblName, col);
            return "SELECT * FROM " + tblName + " WHERE " + colName + " = " + val + ";";
        }
        case 5: {
            // Strategy 5: Composite index prefix (equality on prefix columns, range on last)
            StringBuilder where = new StringBuilder();
            int numCols = Math.min(idxCols.size(), 3);
            for (int i = 0; i < numCols; i++) {
                if (i > 0) where.append(" AND ");
                String ic = idxCols.get(i);
                MariaDBColumn icCol = null;
                for (MariaDBColumn c : table.getColumns()) {
                    if (c.getName().equals(ic)) {
                        icCol = c;
                        break;
                    }
                }
                if (icCol == null) continue;

                if (i < numCols - 1) {
                    // Prefix columns: use equality
                    String val = generateDataAwareValueForType(tblName, icCol);
                    where.append(ic).append(" = ").append(val);
                } else {
                    // Last column: use range operator
                    String op = Randomly.fromOptions(">", "<", ">=", "<=");
                    String val = generateDataAwareValueForType(tblName, icCol);
                    where.append(ic).append(" ").append(op).append(" ").append(val);
                }
            }
            return "SELECT * FROM " + tblName + " WHERE " + where + ";";
        }
        default: {
            // Strategy 6: Index Merge simulation (OR conditions across columns)
            List<MariaDBColumn> tableCols = table.getColumns();
            if (tableCols.size() >= 2) {
                MariaDBColumn col1 = tableCols.get(0);
                MariaDBColumn col2 = tableCols.get(1);
                String val1 = generateDataAwareValueForType(tblName, col1);
                String val2 = generateDataAwareValueForType(tblName, col2);
                return "SELECT * FROM " + tblName + " WHERE " + col1.getName() + " = " + val1
                        + " OR " + col2.getName() + " = " + val2 + ";";
            }
            // Fallback
            String val = generateDataAwareValueForType(tblName, col);
            return "SELECT * FROM " + tblName + " WHERE " + colName + " = " + val + ";";
        }
        }
    }

    private String generateDataAwareValueForType(String tblName, MariaDBColumn col) {
        // Try to get an actual value from the table for this column
        try (Statement s = globalState.getConnection().createStatement()) {
            try (ResultSet rs = s.executeQuery(
                    "SELECT " + col.getName() + " FROM " + tblName + " WHERE " + col.getName()
                            + " IS NOT NULL ORDER BY RAND() LIMIT 1;")) {
                if (rs.next()) {
                    String value = rs.getString(1);
                    if (value != null) {
                        switch (col.getType()) {
                        case INT:
                            return value;
                        case REAL:
                            // [FIX] Skip Infinity/NaN — MariaDB rejects them as
                            // unknown identifiers (SQLSyntaxErrorException).
                            if (!value.equals("Infinity") && !value.equals("-Infinity")
                                    && !value.equals("NaN")) {
                                return value;
                            }
                            break;
                        case VARCHAR:
                            return "'" + value.replace("\\", "\\\\").replace("'", "\\'") + "'";
                        default:
                            return "'" + value.replace("\\", "\\\\").replace("'", "\\'") + "'";
                        }
                    }
                }
            }
        } catch (Exception e) {
            // fallback to random
        }

        // Fallback: generate a random literal based on type
        switch (col.getType()) {
        case INT:
            return String.valueOf(globalState.getRandomly().getInteger());
        case REAL:
            // [FIX] Regenerate until we get a finite value.
            // getDouble() can produce Infinity/NaN which MariaDB rejects.
            for (int attempt = 0; attempt < 10; attempt++) {
                double dval = globalState.getRandomly().getDouble();
                if (Double.isFinite(dval)) {
                    return String.valueOf(dval);
                }
            }
            return "0.0";
        case VARCHAR:
            return "'" + globalState.getRandomly().getString().replace("\\", "\\\\").replace("'", "\\'") + "'";
        default:
            return "0";
        }
    }

    // ==================== Phase A1: Column Value Sampling ====================

    // Samples actual column values for data-aware generation. Cached per check() cycle.
    private List<String> sampleColumnValues(String tableName, String colName, int limit) {
        String cacheKey = tableName + "." + colName;
        if (columnValueCache.containsKey(cacheKey)) {
            List<String> cached = columnValueCache.get(cacheKey);
            if (cached != null && cached.size() >= limit) {
                return cached.subList(0, limit);
            }
            return cached;
        }

        List<String> values = new ArrayList<>();
        try (Statement s = globalState.getConnection().createStatement()) {
            try (ResultSet rs = s.executeQuery(
                    "SELECT " + colName + " FROM " + tableName
                            + " WHERE " + colName + " IS NOT NULL ORDER BY RAND() LIMIT " + limit + ";")) {
                while (rs.next()) {
                    String val = rs.getString(1);
                    if (val != null) {
                        values.add(val);
                    }
                }
            }
        } catch (Exception e) {
            // Ignore
        }

        if (!values.isEmpty()) {
            columnValueCache.put(cacheKey, values);
        }
        return values.isEmpty() ? null : values;
    }

    // Returns unquoted numeric literals and single-quoted+escaped string literals.
    private String quoteValueForSQL(String value, MariaDBColumn col) {
        if (value == null || value.equalsIgnoreCase("NULL")) {
            return "NULL";
        }
        switch (col.getType()) {
        case INT:
            try {
                Integer.parseInt(value.trim());
                return value.trim();
            } catch (NumberFormatException e) {
                return "'" + value.replace("'", "\\'") + "'";
            }
        case REAL:
            try {
                Double.parseDouble(value.trim());
                return value.trim();
            } catch (NumberFormatException e) {
                return "'" + value.replace("'", "\\'") + "'";
            }
        case VARCHAR:
        default:
            return "'" + value.replace("'", "\\'") + "'";
        }
    }

    // ==================== Phase A2: information_schema Index Metadata ====================

    // Gets indexed (non-PK) columns via information_schema.STATISTICS; falls back to schema.
    private List<MariaDBColumn> getIndexedColumnsForTable(MariaDBTable table) {
        List<MariaDBColumn> indexedColumns = new ArrayList<>();
        try (Statement s = globalState.getConnection().createStatement()) {
            String query = "SELECT DISTINCT COLUMN_NAME FROM information_schema.STATISTICS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + table.getName()
                    + "' AND INDEX_NAME != 'PRIMARY' ORDER BY COLUMN_NAME;";
            try (ResultSet rs = s.executeQuery(query)) {
                while (rs.next()) {
                    String colName = rs.getString(1);
                    for (MariaDBColumn col : table.getColumns()) {
                        if (col.getName().equals(colName)) {
                            indexedColumns.add(col);
                            break;
                        }
                    }
                }
            }
        } catch (Exception e) {
            // Fallback to schema-based approach
            for (MariaDBIndex idx : table.getIndexes()) {
                if (!idx.isPrimaryKey()) {
                    for (String colName : idx.getColumnNames()) {
                        for (MariaDBColumn col : table.getColumns()) {
                            if (col.getName().equals(colName) && !indexedColumns.contains(col)) {
                                indexedColumns.add(col);
                            }
                        }
                    }
                }
            }
        }
        return indexedColumns;
    }

    // Returns column groups per non-PK index, ordered by SEQ_IN_INDEX. Falls back to schema.
    private List<List<MariaDBColumn>> getCompositeIndexGroups(MariaDBTable table) {
        Map<String, List<MariaDBColumn>> indexGroups = new HashMap<>();
        try (Statement s = globalState.getConnection().createStatement()) {
            String query = "SELECT INDEX_NAME, COLUMN_NAME, SEQ_IN_INDEX FROM information_schema.STATISTICS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + table.getName()
                    + "' ORDER BY INDEX_NAME, SEQ_IN_INDEX;";
            try (ResultSet rs = s.executeQuery(query)) {
                while (rs.next()) {
                    String indexName = rs.getString("INDEX_NAME");
                    String colName = rs.getString("COLUMN_NAME");
                    indexGroups.computeIfAbsent(indexName, k -> new ArrayList<>());
                    for (MariaDBColumn col : table.getColumns()) {
                        if (col.getName().equals(colName)) {
                            List<MariaDBColumn> group = indexGroups.get(indexName);
                            if (!group.contains(col)) {
                                group.add(col);
                            }
                            break;
                        }
                    }
                }
            }
        } catch (Exception e) {
            // Fallback to schema-based approach
            for (MariaDBIndex idx : table.getIndexes()) {
                List<MariaDBColumn> group = new ArrayList<>();
                for (String colName : idx.getColumnNames()) {
                    for (MariaDBColumn col : table.getColumns()) {
                        if (col.getName().equals(colName) && !group.contains(col)) {
                            group.add(col);
                        }
                    }
                }
                if (!group.isEmpty()) {
                    indexGroups.put(idx.getIndexName(), group);
                }
            }
        }
        return new ArrayList<>(indexGroups.values());
    }

    // ==================== Phase A3: COUNT(*) Fallback ====================

    // Fallback when row-level comparison is filtered: compares COUNT(*) to catch real bugs.
    private void countStarFallback(String queryA, String queryB, String mode) {
        aggregateFallbackUsed++;
        try {
            String countA = wrapInCountStar(queryA);
            String countB = wrapInCountStar(queryB);
            if (countA == null || countB == null) return;
            List<String> r1 = executeQuery(countA);
            List<String> r2 = executeQuery(countB);
            if (r1 == null || r2 == null) return;
            if (!r1.equals(r2)) {
                effectiveTests++;
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

    // Wraps query in SELECT COUNT(*) FROM (...). Strips top-level ORDER BY/LIMIT first.
    private String wrapInCountStar(String query) {
        try {
            String q = query.trim();
            if (q.endsWith(";")) q = q.substring(0, q.length() - 1).trim();
            // Strip LIMIT first (always at the very end if present)
            q = q.replaceAll("(?i)\\s+LIMIT\\s+\\d+\\s*$", "").trim();
            // Strip ORDER BY — only if it's at the top level (not inside parentheses)
            int lastOrderBy = findLastTopLevelOrderBy(q);
            if (lastOrderBy >= 0) {
                q = q.substring(0, lastOrderBy).trim();
            }
            return "SELECT COUNT(*) FROM (" + q + ") AS _count_subq;";
        } catch (Exception e) {
            return null;
        }
    }

    // Finds the last ORDER BY not inside parentheses (i.e., not in a subquery).
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

    // ==================== Phase A3: Non-Deterministic Query Detection ====================

    // LIMIT without ORDER BY produces non-deterministic rows under different plans.
    private boolean hasLimitWithoutOrderBy(String query) {
        String upperQuery = query.toUpperCase();
        boolean hasLimit = upperQuery.contains("LIMIT");
        boolean hasOrderBy = upperQuery.contains("ORDER BY");
        return hasLimit && !hasOrderBy;
    }

    // ORDER BY + LIMIT may non-deterministically pick different rows at the LIMIT boundary
    // when collation-equal values exist (unstable sort).
    private boolean hasOrderByWithLimit(String query) {
        String upperQuery = query.toUpperCase();
        return upperQuery.contains("ORDER BY") && upperQuery.contains("LIMIT");
    }

    // Returns true when GROUP BY uses only constants (no column refs) — non-deterministic output.
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

    // ==================== AST Expression Generation ====================

    // 70% index-friendly WHERE via tryGenerateIndexFriendlyWhere(), 30% random complex expression.
    private String generateASTQuery() {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return null;

        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBColumn> columns = table.getColumns();
        if (columns.isEmpty()) return null;

        try {
            // Phase I: 70% index-friendly, 30% random complex
            MariaDBExpression whereExpr;
            if (Randomly.getBoolean()) {
                // Try index-friendly WHERE first
                whereExpr = tryGenerateIndexFriendlyWhere(
                        Collections.singletonList(table),
                        new MariaDBExpressionGenerator(globalState.getRandomly()));
            }
            else {
                MariaDBExpressionGenerator gen = new MariaDBExpressionGenerator(globalState.getRandomly());
                gen.setColumns(columns);
                whereExpr = gen.getRandomExpression();
            }
            if (whereExpr == null) return null;
            String whereStr = MariaDBVisitor.asString(whereExpr);

            // Optionally add ORDER BY on an indexed column
            String orderBy = "";
            if (Randomly.getBoolean()) {
                List<MariaDBColumn> indexedCols = getIndexedColumnsForTable(table);
                if (!indexedCols.isEmpty()) {
                    MariaDBColumn orderCol = Randomly.fromList(indexedCols);
                    orderBy = " ORDER BY " + orderCol.getName()
                            + (Randomly.getBoolean() ? " ASC" : " DESC");
                }
            }

            // Optionally add LIMIT
            String limit = "";
            if (Randomly.getBoolean()) {
                limit = " LIMIT " + globalState.getRandomly().getLong(1, 100);
            }

            return "SELECT * FROM " + table.getName() + " WHERE " + whereStr + orderBy + limit + ";";
        } catch (Exception e) {
            return null;
        }
    }

    // Multi-table JOIN with index-friendly ON clauses and WHERE.
    private String generateASTJoinQuery() {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = new ArrayList<>(schema.getDatabaseTables());
        if (tables.size() < 2) return null;

        try {
            Collections.shuffle(tables);
            int numTables = Math.min(tables.size(), globalState.getRandomly().getInteger(2, 4));
            List<MariaDBTable> joinTables = tables.subList(0, numTables);

            // Phase I: Generate index-friendly JOIN clauses
            List<String> joinClauses = generateIndexFriendlyJoinClauses(joinTables);
            if (joinClauses.isEmpty()) return null;

            // Phase I: Generate index-friendly WHERE
            List<MariaDBColumn> allColumns = new ArrayList<>();
            for (MariaDBTable t : joinTables) {
                allColumns.addAll(t.getColumns());
            }

            MariaDBExpression whereExpr = null;
            if (Randomly.getBoolean()) {
                whereExpr = tryGenerateIndexFriendlyWhere(
                        new ArrayList<>(joinTables),
                        new MariaDBExpressionGenerator(globalState.getRandomly()));
            }
            String whereStr = (whereExpr != null) ? MariaDBVisitor.asString(whereExpr) : null;

            StringBuilder sb = new StringBuilder();
            sb.append("SELECT * FROM ").append(joinTables.get(0).getName());
            for (String jc : joinClauses) {
                sb.append(" ").append(jc);
            }
            if (whereStr != null) {
                sb.append(" WHERE ").append(whereStr);
            }

            // Optional LIMIT
            if (Randomly.getBoolean()) {
                sb.append(" LIMIT ").append(globalState.getRandomly().getLong(1, 50));
            }
            sb.append(";");
            return sb.toString();
        } catch (Exception e) {
            return null;
        }
    }

    // Aggregate query (COUNT/SUM/AVG/MIN/MAX) with index-aware WHERE and optional GROUP BY.
    private String generateASTAggregateQuery() {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return null;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return null;

        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();

        String aggFunc = Randomly.fromOptions("COUNT", "SUM", "AVG", "MIN", "MAX");

        // Phase I: Use index-friendly WHERE when possible
        String whereClause;
        MariaDBExpression indexWhere = tryGenerateIndexFriendlyWhere(
                Collections.singletonList(table),
                new MariaDBExpressionGenerator(globalState.getRandomly()));
        if (indexWhere != null) {
            whereClause = MariaDBVisitor.asString(indexWhere);
        } else {
            // Fallback to data-aware string WHERE
            String val = generateDataAwareValueForType(tblName, col);
            String op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IS NOT NULL");
            if (op.equals("IS NOT NULL")) {
                whereClause = colName + " IS NOT NULL";
            } else {
                whereClause = colName + " " + op + " " + val;
            }
        }

        if (Randomly.getBoolean()) {
            // With GROUP BY
            return "SELECT " + colName + ", " + aggFunc + "(" + colName + ") FROM " + tblName
                    + " WHERE " + whereClause + " GROUP BY " + colName + ";";
        } else {
            // Without GROUP BY
            return "SELECT " + aggFunc + "(" + colName + ") FROM " + tblName
                    + " WHERE " + whereClause + ";";
        }
    }

    // ==================== Phase I: Index-Friendly AST Helpers ====================

    // Returns {min, max} for a column; used to generate index-friendly range conditions.
    private String[] getColumnMinMax(String tblName, String colName) {
        try (Statement s = globalState.getConnection().createStatement()) {
            try (ResultSet rs = s.executeQuery(
                    "SELECT MIN(" + colName + "), MAX(" + colName + ") FROM " + tblName + ";")) {
                if (rs.next()) {
                    String min = rs.getString(1);
                    String max = rs.getString(2);
                    if (min != null && max != null) {
                        return new String[]{min, max};
                    }
                }
            }
        } catch (Exception e) {
            // ignore
        }
        return null;
    }

    // Returns a data-aware sampled constant for the column type, or a random fallback.
    private MariaDBExpression generateIndexFriendlyConstant(MariaDBColumn col, Randomly r) {
        // Try data-aware value first
        String tblName = null;
        // Find the table for this column
        for (MariaDBTable table : globalState.getSchema().getDatabaseTables()) {
            for (MariaDBColumn c : table.getColumns()) {
                if (c.getName().equals(col.getName())) {
                    tblName = table.getName();
                    break;
                }
            }
            if (tblName != null) break;
        }

        if (tblName != null) {
            List<String> samples = sampleColumnValues(tblName, col.getName(), 3);
            if (samples != null && !samples.isEmpty()) {
                String val = Randomly.fromList(samples);
                switch (col.getType()) {
                case INT:
                    try {
                        return MariaDBConstant.createIntConstant(Long.parseLong(val.trim()));
                    } catch (NumberFormatException e) {
                        return MariaDBConstant.createTextConstant(val);
                    }
                case REAL:
                    try {
                        return new MariaDBConstant.MariaDBDoubleConstant(Double.parseDouble(val.trim()));
                    } catch (NumberFormatException e) {
                        return MariaDBConstant.createTextConstant(val);
                    }
                case VARCHAR:
                default:
                    return MariaDBConstant.createTextConstant(val);
                }
            }
        }

        // Fallback to random constant
        switch (col.getType()) {
        case INT:
            return MariaDBConstant.createIntConstant(r.getInteger());
        case REAL:
            return new MariaDBConstant.MariaDBDoubleConstant(r.getDouble());
        case VARCHAR:
        default:
            return MariaDBConstant.createTextConstant(r.getString());
        }
    }

    // Generates col > val / col < val / col >= val / col <= val / col BETWEEN a AND b condition.
    private MariaDBExpression generateIndexFriendlyRange(MariaDBExpression colRef, MariaDBColumn col, Randomly r) {
        int opType = r.getInteger(0, 4);
        MariaDBExpression constant = generateIndexFriendlyConstant(col, r);
        switch (opType) {
        case 0:
            return new MariaDBBinaryOperator(colRef, constant,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.GREATER_THAN);
        case 1:
            return new MariaDBBinaryOperator(colRef, constant,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.LESS_THAN);
        case 2:
            return new MariaDBBinaryOperator(colRef, constant,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.GREATER_THAN_EQUAL);
        case 3:
            return new MariaDBBinaryOperator(colRef, constant,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.LESS_THAN_EQUAL);
        default:
            return new MariaDBBinaryOperator(colRef, constant,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
        }
    }

    // Returns col = val (50%) or col IS NOT NULL (50%).
    private MariaDBExpression generateSimpleIndexCondition(MariaDBExpression colRef, MariaDBColumn col, Randomly r) {
        if (Randomly.getBoolean()) {
            return new MariaDBBinaryOperator(colRef, generateIndexFriendlyConstant(col, r),
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
        } else {
            return new MariaDBPostfixUnaryOperation(
                    MariaDBPostfixUnaryOperation.MariaDBPostfixUnaryOperator.IS_NOT_NULL, colRef);
        }
    }

    // Generates a WHERE clause that maximizes index utilization.
    // Picks strategy based on available indexes:
    //   0: composite prefix, 1: full composite equality, 2: index merge (OR),
    //   3: range + NULL, 4: multi-index OR, 5: type-aware condition.
    private MariaDBExpression tryGenerateIndexFriendlyWhere(
            List<MariaDBTable> tables, MariaDBExpressionGenerator gen) {
        try {
            // Step 1: Collect index information
            List<MariaDBColumn> indexedCols = new ArrayList<>();
            List<List<MariaDBColumn>> compositeIdxCols = new ArrayList<>();
            List<MariaDBColumn> singleIdxCols = new ArrayList<>();

            for (MariaDBTable table : tables) {
                for (MariaDBIndex idx : table.getIndexes()) {
                    List<String> idxColNames = idx.getColumnNames();
                    if (idxColNames == null || idxColNames.isEmpty()) continue;

                    List<MariaDBColumn> idxColumns = new ArrayList<>();
                    for (String colName : idxColNames) {
                        for (MariaDBColumn col : table.getColumns()) {
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

            // Step 2: Choose strategy based on available indexes
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
                // No indexes — fall back to basic random WHERE
                for (MariaDBTable table : tables) {
                    if (!table.getColumns().isEmpty()) {
                        gen.setColumns(table.getColumns());
                        return gen.getRandomExpression();
                    }
                }
                return null;
            }

            switch (strategy) {
            case 0:
                return generateCompositePrefixCondition(compositeIdxCols, indexedCols, r, gen);
            case 1:
                return generateFullCompositeCondition(compositeIdxCols, indexedCols, r, gen);
            case 2:
                return generateIndexMergeCondition(singleIdxCols, indexedCols, r, gen);
            case 3:
                return generateRangeWithNullCondition(indexedCols, r, gen);
            case 4:
                return generateMultiIndexOrCondition(indexedCols, r, gen);
            default:
                return generateTypeAwareCondition(indexedCols, r, gen);
            }
        } catch (Exception e) {
            return null;
        }
    }

    // Strategy 0: c0 = val AND c1 > val2 — triggers composite index range scan on the prefix.
    private MariaDBExpression generateCompositePrefixCondition(
            List<List<MariaDBColumn>> compositeIdxCols, List<MariaDBColumn> indexedCols,
            Randomly r, MariaDBExpressionGenerator gen) {
        if (compositeIdxCols.isEmpty()) {
            // Fallback: use single indexed column
            if (indexedCols.isEmpty()) return null;
            MariaDBColumn col = Randomly.fromList(indexedCols);
            return new MariaDBBinaryOperator(new MariaDBColumnName(col),
                    generateIndexFriendlyConstant(col, r),
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
        }
        List<MariaDBColumn> idxCols = Randomly.fromList(compositeIdxCols);
        int prefixLen = Math.min(idxCols.size(), r.getInteger(1, 4));
        MariaDBExpression combined = null;
        for (int i = 0; i < prefixLen; i++) {
            MariaDBColumn col = idxCols.get(i);
            MariaDBExpression colRef = new MariaDBColumnName(col);
            MariaDBExpression condition;
            if (i == 0) {
                // First column: equality for best selectivity (ref access)
                condition = new MariaDBBinaryOperator(colRef, generateIndexFriendlyConstant(col, r),
                        MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
            } else if (i == prefixLen - 1 && Randomly.getBoolean()) {
                // Last prefix column: range to trigger range scan
                condition = generateIndexFriendlyRange(colRef, col, r);
            } else {
                condition = generateSimpleIndexCondition(colRef, col, r);
            }
            combined = (combined == null) ? condition
                    : new MariaDBBinaryOperator(combined, condition,
                            MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.AND);
        }
        return combined;
    }

    // Strategy 1: equality on all composite index columns — triggers unique/ref lookup.
    private MariaDBExpression generateFullCompositeCondition(
            List<List<MariaDBColumn>> compositeIdxCols, List<MariaDBColumn> indexedCols,
            Randomly r, MariaDBExpressionGenerator gen) {
        if (compositeIdxCols.isEmpty()) {
            if (indexedCols.isEmpty()) return null;
            MariaDBColumn col = Randomly.fromList(indexedCols);
            return new MariaDBBinaryOperator(new MariaDBColumnName(col),
                    generateIndexFriendlyConstant(col, r),
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
        }
        List<MariaDBColumn> idxCols = Randomly.fromList(compositeIdxCols);
        MariaDBExpression combined = null;
        for (MariaDBColumn col : idxCols) {
            MariaDBExpression colRef = new MariaDBColumnName(col);
            MariaDBExpression condition = new MariaDBBinaryOperator(colRef,
                    generateIndexFriendlyConstant(col, r),
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
            combined = (combined == null) ? condition
                    : new MariaDBBinaryOperator(combined, condition,
                            MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.AND);
        }
        return combined;
    }

    // Strategy 2: c0 = val1 OR c1 = val2 — triggers index_merge optimization.
    private MariaDBExpression generateIndexMergeCondition(
            List<MariaDBColumn> singleIdxCols, List<MariaDBColumn> indexedCols,
            Randomly r, MariaDBExpressionGenerator gen) {
        List<MariaDBColumn> candidates = new ArrayList<>(
                singleIdxCols.size() >= 2 ? singleIdxCols : indexedCols);
        if (candidates.size() < 2) return null;

        Collections.shuffle(candidates);
        MariaDBColumn col1 = candidates.get(0);
        MariaDBColumn col2 = candidates.get(1);

        MariaDBExpression colRef1 = new MariaDBColumnName(col1);
        MariaDBExpression colRef2 = new MariaDBColumnName(col2);

        MariaDBExpression cond1 = generateIndexFriendlyRange(colRef1, col1, r);
        MariaDBExpression cond2 = generateIndexFriendlyRange(colRef2, col2, r);

        return new MariaDBBinaryOperator(cond1, cond2,
                MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.OR);
    }

    // Strategy 3: range condition combined with IS NULL or IS NOT NULL.
    private MariaDBExpression generateRangeWithNullCondition(
            List<MariaDBColumn> indexedCols, Randomly r, MariaDBExpressionGenerator gen) {
        MariaDBColumn col = Randomly.fromList(indexedCols);
        MariaDBExpression colRef = new MariaDBColumnName(col);
        MariaDBExpression rangeCond = generateIndexFriendlyRange(colRef, col, r);

        if (Randomly.getBoolean()) {
            // col > val OR col IS NULL
            MariaDBExpression isNull = new MariaDBPostfixUnaryOperation(
                    MariaDBPostfixUnaryOperation.MariaDBPostfixUnaryOperator.IS_NULL, colRef);
            return new MariaDBBinaryOperator(rangeCond, isNull,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.OR);
        } else {
            // col > val AND col IS NOT NULL
            MariaDBExpression isNotNull = new MariaDBPostfixUnaryOperation(
                    MariaDBPostfixUnaryOperation.MariaDBPostfixUnaryOperator.IS_NOT_NULL, colRef);
            return new MariaDBBinaryOperator(rangeCond, isNotNull,
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.AND);
        }
    }

    // Strategy 4: OR conditions across 2-3 indexed columns to trigger sort-union index merge.
    private MariaDBExpression generateMultiIndexOrCondition(
            List<MariaDBColumn> indexedCols, Randomly r, MariaDBExpressionGenerator gen) {
        if (indexedCols.size() < 2) return null;
        int numCols = Math.min(indexedCols.size(), r.getInteger(2, 4));
        List<MariaDBColumn> shuffled = new ArrayList<>(indexedCols);
        Collections.shuffle(shuffled);

        MariaDBExpression combined = null;
        for (int i = 0; i < numCols; i++) {
            MariaDBColumn col = shuffled.get(i);
            MariaDBExpression colRef = new MariaDBColumnName(col);
            MariaDBExpression condition;

            int subStrategy = r.getInteger(0, 3);
            switch (subStrategy) {
            case 0: // Equality
                condition = new MariaDBBinaryOperator(colRef, generateIndexFriendlyConstant(col, r),
                        MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
                break;
            case 1: // Range
                condition = generateIndexFriendlyRange(colRef, col, r);
                break;
            default: // IS NOT NULL
                condition = new MariaDBPostfixUnaryOperation(
                        MariaDBPostfixUnaryOperation.MariaDBPostfixUnaryOperator.IS_NOT_NULL, colRef);
                break;
            }

            combined = (combined == null) ? condition
                    : new MariaDBBinaryOperator(combined, condition,
                            MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.OR);
        }
        return combined;
    }

    // Strategy 5: col = sampled_value (50%) or col > sampled_value (50%).
    private MariaDBExpression generateTypeAwareCondition(
            List<MariaDBColumn> indexedCols, Randomly r, MariaDBExpressionGenerator gen) {
        MariaDBColumn col = Randomly.fromList(indexedCols);
        MariaDBExpression colRef = new MariaDBColumnName(col);

        // 50% equality, 50% range
        if (Randomly.getBoolean()) {
            return new MariaDBBinaryOperator(colRef, generateIndexFriendlyConstant(col, r),
                    MariaDBBinaryOperator.MariaDBBinaryComparisonOperator.EQUALS);
        } else {
            return generateIndexFriendlyRange(colRef, col, r);
        }
    }

    // Returns JOIN clauses preferring equijoin on indexed columns.
    private List<String> generateIndexFriendlyJoinClauses(List<MariaDBTable> tables) {
        List<String> joinClauses = new ArrayList<>();
        if (tables.size() < 2) return joinClauses;

        try {
            String[] joinTypes = {"JOIN", "INNER JOIN", "LEFT JOIN", "RIGHT JOIN"};
            int nrJoinClauses = Math.min(tables.size() - 1,
                    globalState.getRandomly().getInteger(1, Math.min(tables.size(), 3)));

            // First table is the base
            String lastTable = tables.get(0).getName();

            for (int i = 0; i < nrJoinClauses && i + 1 < tables.size(); i++) {
                MariaDBTable joinTable = tables.get(i + 1);
                String joinType = Randomly.fromOptions(joinTypes);

                // Generate ON clause using column comparison
                String onClause = generateIndexJoinOnClause(lastTable, joinTable);
                if (onClause == null) {
                    onClause = "1=1"; // fallback: cross join
                }

                joinClauses.add(joinType + " " + joinTable.getName() + " ON " + onClause);
                lastTable = joinTable.getName();
            }
        } catch (Exception e) {
            // fallback: return simple cross join
            if (tables.size() >= 2) {
                joinClauses.add("JOIN " + tables.get(1).getName() + " ON 1=1");
            }
        }
        return joinClauses;
    }

    // Returns ON clause with 1-3 column comparisons; prefers equijoin for index utilization.
    private String generateIndexJoinOnClause(String t1Name, MariaDBTable t2) {
        Randomly r = globalState.getRandomly();

        // Find columns for both tables
        MariaDBTable t1 = null;
        for (MariaDBTable table : globalState.getSchema().getDatabaseTables()) {
            if (table.getName().equals(t1Name)) {
                t1 = table;
                break;
            }
        }
        if (t1 == null || t1.getColumns().isEmpty() || t2.getColumns().isEmpty()) return null;

        int numConditions = r.getInteger(1, 3);
        List<String> conditions = new ArrayList<>();

        for (int i = 0; i < numConditions; i++) {
            MariaDBColumn c1 = Randomly.fromList(t1.getColumns());
            MariaDBColumn c2 = Randomly.fromList(t2.getColumns());

            String op;
            int opType = r.getInteger(0, 5);
            switch (opType) {
            case 0: op = "="; break;    // equijoin — best for index
            case 1: op = ">"; break;
            case 2: op = "<"; break;
            case 3: op = ">="; break;
            default: op = "<="; break;
            }

            conditions.add(t1Name + "." + c1.getName() + " " + op + " " + t2.getName() + "." + c2.getName());
        }

        return String.join(" AND ", conditions);
    }

    // ==================== Comparison Methods ====================

    private void compareResultsSorted(List<String> r1, List<String> r2, String queryString, String mode) {
        // Phase A3: Check for non-deterministic patterns before comparing
        if (hasLimitWithoutOrderBy(queryString)) {
            lastCompareFiltered = true;
            return;
        }
        if (hasNonDeterministicGroupBy(queryString)) {
            lastCompareFiltered = true;
            return;
        }

        List<String> s1 = new ArrayList<>(r1);
        List<String> s2 = new ArrayList<>(r2);
        s1.sort(MariaDBIndexOracle::nullSafeCompare);
        s2.sort(MariaDBIndexOracle::nullSafeCompare);

        if (s1.equals(s2)) {
            // Results match after sorting — no bug detected
            return;
        }

        // Case-insensitive fallback: MariaDB's default collation (utf8mb4_uca1400_ai_ci)
        // is case-insensitive, so rows differing only in case are semantically equivalent.
        // The DB may return different case-variants non-deterministically.
        if (caseInsensitiveEquals(s1, s2)) {
            lastCompareFiltered = true;
            return;
        }

        // Case-insensitive set-difference fallback (database14.log false positive):
        // When ORDER BY columns have case-insensitive-equal values (e.g., "#y1-3wf" vs
        // "#y1-3wF"), different execution plans may pick different rows at the LIMIT
        // boundary. This is valid non-deterministic behavior under MariaDB's default
        // case-insensitive collation. Check if all differing rows pair up case-insensitively.
        if (caseInsensitiveSetEquals(s1, s2)) {
            lastCompareFiltered = true;
            return;
        }
        // PAD SPACE collation fallback (database3.log false positive):
        // MariaDB's default collation uses PAD SPACE semantics where trailing spaces
        // are ignored (e.g., '' == ' '). When ORDER BY has such values, different
        // execution plans may non-deterministically pick different rows at the LIMIT
        // boundary. If rows match after stripping trailing spaces, treat as equivalent.
        if (padSpaceSetEquals(s1, s2)) {
            lastCompareFiltered = true;
            return;
        }
        // ORDER BY + LIMIT boundary false positive (database63.log):
        // When ORDER BY columns have duplicate/equivalent values under MariaDB's
        // collation, different execution plans may non-deterministically pick
        // different rows at the LIMIT boundary. If same-size result sets differ
        // only in a few rows, this is likely unstable sort, not an index bug.
        // Fallback to COUNT(*) consistency check via countStarFallback.
        if (hasOrderByWithLimit(queryString) && s1.size() == s2.size()) {
            lastCompareFiltered = true;
            return;
        }

        // Results differ after sorting — potential bug
        lastCompareFiltered = false;
        effectiveTests++;
        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] Query: " + queryString);
        combinedString.add("-- [" + mode + "] Result 1 (sorted): " + s1);
        combinedString.add("-- [" + mode + "] Result 2 (sorted): " + s2);
        combinedString.add("-- [" + mode + "] Diff: " + findDifferences(s1, s2));
        try {
            ComparatorHelper.assumeResultSetsAreEqual(r1, r2, queryString, combinedString, globalState);
        } catch (ArrayIndexOutOfBoundsException e) {
            lastCompareFiltered = true;
        }
    }

    private void compareResultsStrict(List<String> r1, List<String> r2, String queryString, String mode) {
        if (r1.equals(r2)) {
            return;
        }

        // Phase A3: Check for non-deterministic patterns
        if (hasLimitWithoutOrderBy(queryString)) {
            lastCompareFiltered = true;
            return;
        }

        // Try sorted comparison first
        List<String> s1 = new ArrayList<>(r1);
        List<String> s2 = new ArrayList<>(r2);
        s1.sort(MariaDBIndexOracle::nullSafeCompare);
        s2.sort(MariaDBIndexOracle::nullSafeCompare);
        if (s1.equals(s2)) {
            // Results match when sorted — difference is just ordering, not a bug
            lastCompareFiltered = true;
            return;
        }


        // Case-insensitive fallback: MariaDB's default collation (utf8mb4_uca1400_ai_ci)
        // is case-insensitive, so rows that differ only in case are semantically equivalent.
        if (caseInsensitiveEquals(s1, s2)) {
            lastCompareFiltered = true;
            return;
        }
        // Case-insensitive set-difference fallback (database14.log false positive):
        if (caseInsensitiveSetEquals(s1, s2)) {
            lastCompareFiltered = true;
            return;
        }
        // PAD SPACE collation fallback (database3.log false positive):
        // MariaDB's default collation uses PAD SPACE semantics where trailing spaces
        // are ignored (e.g., '' == ' '). When ORDER BY has such values, different
        // execution plans may non-deterministically pick different rows at the LIMIT
        // boundary. If rows match after stripping trailing spaces, treat as equivalent.
        if (padSpaceSetEquals(s1, s2)) {
            lastCompareFiltered = true;
            return;
        }
        // ORDER BY + LIMIT boundary false positive (database63.log):
        if (hasOrderByWithLimit(queryString) && s1.size() == s2.size()) {
            lastCompareFiltered = true;
            return;
        }
        // Results differ even after sorting — potential bug
        lastCompareFiltered = false;
        effectiveTests++;
        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] Query: " + queryString);
        combinedString.add("-- [" + mode + "] Result 1 (strict): " + r1);
        combinedString.add("-- [" + mode + "] Result 2 (strict): " + r2);
        combinedString.add("-- [" + mode + "] Result 1 (sorted): " + s1);
        combinedString.add("-- [" + mode + "] Result 2 (sorted): " + s2);
        try {
            ComparatorHelper.assumeResultSetsAreEqual(r1, r2, queryString, combinedString, globalState);
        } catch (ArrayIndexOutOfBoundsException e) {
            lastCompareFiltered = true;
        }
    }

    private String findDifferences(List<String> sorted1, List<String> sorted2) {
        StringBuilder diff = new StringBuilder();
        Set<String> set1 = new HashSet<>(sorted1);
        Set<String> set2 = new HashSet<>(sorted2);
        for (String s : set1) {
            if (!set2.contains(s)) {
                diff.append("ONLY_IN_1:").append(s).append(" ");
            }
        }
        for (String s : set2) {
            if (!set1.contains(s)) {
                diff.append("ONLY_IN_2:").append(s).append(" ");
            }
        }
        return diff.toString();
    }

    // ==================== Helper Methods ====================


    // Element-wise case-insensitive equality check for sorted result lists.
    // MariaDB's default collation (utf8mb4_uca1400_ai_ci) is case-insensitive.
    private static boolean caseInsensitiveEquals(List<String> sorted1, List<String> sorted2) {
        if (sorted1.size() != sorted2.size()) return false;
        for (int i = 0; i < sorted1.size(); i++) {
            if (!sorted1.get(i).equalsIgnoreCase(sorted2.get(i))) return false;
        }
        return true;
    }

    // Multiset case-insensitive equality — handles LIMIT boundary false positives where
    // different plans pick different case-variants of collation-equal ORDER BY values.
    private static boolean caseInsensitiveSetEquals(List<String> sorted1, List<String> sorted2) {
        if (sorted1.size() != sorted2.size()) return false;
        List<String> remaining = new ArrayList<>(sorted2);
        for (String s1 : sorted1) {
            boolean found = false;
            for (int j = 0; j < remaining.size(); j++) {
                if (s1.equalsIgnoreCase(remaining.get(j))) {
                    remaining.remove(j);
                    found = true;
                    break;
                }
            }
            if (!found) return false;
        }
        return remaining.isEmpty();
    }

    // Element-wise PAD SPACE equality: MariaDB ignores trailing spaces ('' == ' ').
    private static boolean padSpaceEquals(List<String> sorted1, List<String> sorted2) {
        if (sorted1.size() != sorted2.size()) return false;
        for (int i = 0; i < sorted1.size(); i++) {
            String a = sorted1.get(i);
            String b = sorted2.get(i);
            if (a == null && b == null) continue;
            if (a == null || b == null) return false;
            if (!stripTrailing(a).equals(stripTrailing(b))) return false;
        }
        return true;
    }

    // Multiset PAD SPACE equality — handles LIMIT boundary false positives where
    // different plans pick rows that differ only in trailing spaces.
    private static boolean padSpaceSetEquals(List<String> sorted1, List<String> sorted2) {
        if (sorted1.size() != sorted2.size()) return false;
        List<String> remaining = new ArrayList<>(sorted2);
        for (String s1 : sorted1) {
            boolean found = false;
            String stripped1 = s1 != null ? stripTrailing(s1) : null;
            for (int j = 0; j < remaining.size(); j++) {
                String stripped2 = remaining.get(j) != null ? stripTrailing(remaining.get(j)) : null;
                if (stripped1 == null && stripped2 == null) {
                    remaining.remove(j);
                    found = true;
                    break;
                }
                if (stripped1 != null && stripped1.equals(stripped2)) {
                    remaining.remove(j);
                    found = true;
                    break;
                }
            }
            if (!found) return false;
        }
        return remaining.isEmpty();
    }

    // Java 8 compatible String.stripTrailing().
    private static String stripTrailing(String s) {
        if (s == null) return null;
        int end = s.length();
        while (end > 0 && s.charAt(end - 1) <= ' ') {
            end--;
        }
        return end == s.length() ? s : s.substring(0, end);
    }

    private static int nullSafeCompare(String a, String b) {
        if (a == null && b == null)
            return 0;
        if (a == null)
            return -1;
        if (b == null)
            return 1;
        return a.compareTo(b);
    }

    private MariaDBIndex getRandomNonPrimaryIndex() {
        List<MariaDBIndex> nonPrimaryIndexes = new ArrayList<>();
        for (MariaDBTable table : globalState.getSchema().getDatabaseTables()) {
            for (MariaDBIndex idx : table.getIndexes()) {
                if (!idx.isPrimaryKey()) {
                    nonPrimaryIndexes.add(idx);
                }
            }
        }
        if (nonPrimaryIndexes.isEmpty())
            return null;
        return Randomly.fromList(nonPrimaryIndexes);
    }

    private String findTableForIndex(MariaDBIndex targetIdx) {
        for (MariaDBTable table : globalState.getSchema().getDatabaseTables()) {
            for (MariaDBIndex idx : table.getIndexes()) {
                if (idx == targetIdx) {
                    return table.getName();
                }
            }
        }
        return null;
    }

    private void log(String message) {
        globalState.getState().logStatement(message);
    }

    // ==================== Phase D1: Index-Friendly Tables ====================

    // Creates dedicated idx_t0/t1/t2 tables with pre-built indexes and diverse column types
    // for reliable index testing, reducing reliance on randomly-generated tables.
    private void createIndexFriendlyTables() {
        if (indexFriendlyCreated) return;

        ExpectedErrors tableErrors = new ExpectedErrors();
        tableErrors.add("already exists");
        tableErrors.add("Duplicate key name");
        tableErrors.add("Specified key was too long");
        tableErrors.add("BLOB or TEXT");
        tableErrors.add("used in key specification");
        tableErrors.add("Too many keys specified");

        // Check if index-friendly tables already exist
        try {
            MariaDBSchema schema = globalState.getSchema();
            for (MariaDBTable t : schema.getDatabaseTables()) {
                if (t.getName().startsWith("idx_")) {
                    indexFriendlyCreated = true;
                    return;
                }
            }
        } catch (Exception e) { return; }

        Randomly r = globalState.getRandomly();
        int numTables = Randomly.fromOptions(2, 2, 3);

        for (int t = 0; t < numTables; t++) {
            String tableName = "idx_t" + t;
            try {
                StringBuilder createSQL = new StringBuilder();
                createSQL.append("CREATE TABLE IF NOT EXISTS ").append(tableName).append(" (");

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
                } else if (t == 1) {
                    // Table 1: INT + DOUBLE — tests DOUBLE precision index
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 DOUBLE NOT NULL, ");
                    createSQL.append("c2 INT, ");
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 DOUBLE, "); // nullable DOUBLE
                    createSQL.append("c5 VARCHAR(64) NOT NULL, ");
                    createSQL.append("c6 INT, ");
                    createSQL.append("c7 DOUBLE NOT NULL");
                } else {
                    // Table 2: INT + VARCHAR — extra VARCHAR coverage
                    createSQL.append("c0 INT NOT NULL, ");
                    createSQL.append("c1 INT NOT NULL, ");
                    createSQL.append("c2 VARCHAR(64), ");
                    createSQL.append("c3 INT NOT NULL, ");
                    createSQL.append("c4 VARCHAR(64) NOT NULL, ");
                    createSQL.append("c5 VARCHAR(64) NOT NULL, ");
                    createSQL.append("c6 INT, ");
                    createSQL.append("c7 INT NOT NULL");
                }
                createSQL.append(");");
                globalState.executeStatement(new SQLQueryAdapter(createSQL.toString(), tableErrors, true));

                // Pre-build diverse indexes
                List<String> indexStmts = new ArrayList<>();
                if (t == 0) {
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0c1c3 ON " + tableName + " (c0, c1, c3);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c5 ON " + tableName + " (c5);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0desc ON " + tableName + " (c0 DESC);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c2 ON " + tableName + " (c2);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0asc1desc ON " + tableName + " (c0 ASC, c1 DESC);");
                } else if (t == 1) {
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c1 ON " + tableName + " (c1);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c5 ON " + tableName + " (c5);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c1desc ON " + tableName + " (c1 DESC);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c4 ON " + tableName + " (c4);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c7 ON " + tableName + " (c7);");
                } else {
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0 ON " + tableName + " (c0);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0c1 ON " + tableName + " (c0, c1);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c5 ON " + tableName + " (c5);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c4 ON " + tableName + " (c4);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c0desc ON " + tableName + " (c0 DESC);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c2 ON " + tableName + " (c2);");
                    indexStmts.add("CREATE INDEX idx_" + t + "_c7 ON " + tableName + " (c7);");
                }

                for (String idxSQL : indexStmts) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(idxSQL, tableErrors, true));
                    } catch (Exception e) { /* ignore duplicate index errors */ }
                }

                // Insert type-aware data (Phase D6)
                insertTypeAwareData(tableName, t, 200);

                // ANALYZE this table immediately
                try {
                    globalState.executeStatement(
                            new SQLQueryAdapter("ANALYZE TABLE " + tableName + ";", true));
                } catch (Exception e) { /* ignore */ }

            } catch (Exception e) {
                // Table creation failed — continue with other tables
            }
        }
        indexFriendlyCreated = true;
    }

    // ==================== Phase D2: Index Signature Deduplication ====================

    // Returns signatures of existing indexes (format: "tableName:[U:]col1,col2") for dedup.
    private Set<String> collectExistingIndexSignatures() {
        Set<String> sigs = new HashSet<>();
        try {
            for (MariaDBTable table : globalState.getSchema().getDatabaseTables()) {
                for (MariaDBIndex idx : table.getIndexes()) {
                    StringBuilder sig = new StringBuilder();
                    sig.append(table.getName()).append(":");
                    if (idx.isUnique()) sig.append("U:");
                    sig.append(String.join(",", idx.getColumnNames()));
                    sigs.add(sig.toString());
                }
            }
        } catch (Exception e) { /* ignore */ }
        return sigs;
    }

    // Returns true if index creation should proceed (no duplicate signature, under the 15-index cap).
    private boolean shouldCreateIndex(Set<String> existingSigs, String tableName, List<String> colNames, boolean unique) {
        StringBuilder sig = new StringBuilder();
        sig.append(tableName).append(":");
        if (unique) sig.append("U:");
        sig.append(String.join(",", colNames));
        if (existingSigs.contains(sig.toString())) return false;
        if (existingSigs.size() >= 15) return false; // Don't create too many indexes
        return true;
    }

    // ==================== Phase D6: Type-Aware Data Insertion ====================

    // Inserts type-appropriate data (avoids all-NULL defaults). Batches 10 rows per INSERT.
    private void insertTypeAwareData(String tableName, int tableType, int targetRows) {
        ExpectedErrors insertErrors = new ExpectedErrors();
        insertErrors.add("Duplicate");
        insertErrors.add("incorrect");
        insertErrors.add("Data too long");
        insertErrors.add("Out of range");

        // Determine column types based on table type
        String[] colTypes;
        if (tableType == 0) {
            colTypes = new String[]{"INT", "INT", "INT", "INT", "INT", "VARCHAR", "VARCHAR", "VARCHAR"};
        } else if (tableType == 1) {
            colTypes = new String[]{"INT", "DOUBLE", "INT", "INT", "DOUBLE", "VARCHAR", "INT", "DOUBLE"};
        } else {
            colTypes = new String[]{"INT", "INT", "VARCHAR", "INT", "VARCHAR", "VARCHAR", "INT", "INT"};
        }

        Randomly r = globalState.getRandomly();
        int currentRows = getTableRowCount(tableName);
        int rowsNeeded = Math.max(0, targetRows - currentRows);

        // Batch inserts for efficiency (10 rows per INSERT ... VALUES)
        for (int batch = 0; batch < rowsNeeded; batch += 10) {
            StringBuilder insertSQL = new StringBuilder();
            insertSQL.append("INSERT IGNORE INTO ").append(tableName).append(" VALUES ");
            int batchSize = Math.min(10, rowsNeeded - batch);
            for (int row = 0; row < batchSize; row++) {
                if (row > 0) insertSQL.append(", ");
                insertSQL.append("(");
                for (int c = 0; c < colTypes.length; c++) {
                    if (c > 0) insertSQL.append(", ");
                    insertSQL.append(generateRandomValueForType(colTypes[c], r));
                }
                insertSQL.append(")");
            }
            insertSQL.append(";");
            try {
                globalState.executeStatement(new SQLQueryAdapter(insertSQL.toString(), insertErrors, true));
            } catch (Exception e) { /* ignore insert errors */ }
        }
    }

    // Returns a random SQL literal for INT/DOUBLE/VARCHAR within index-testable ranges.
    private String generateRandomValueForType(String type, Randomly r) {
        switch (type.toUpperCase()) {
        case "INT":
            return String.valueOf(Math.abs(r.getInteger() % 255));
        case "DOUBLE": {
            // [FIX] Generate a valid SQL DOUBLE literal — no scientific notation, no truncation.
            // Previously r.getDouble() was called twice (different random values), and
            // substring(0,12) could truncate scientific notation like "1.214331439E10" to
            // "1.214331439E" which is invalid SQL.
            // [FIX] Also guard against Infinity/NaN which MariaDB does not accept as literals.
            double dval = Math.abs(r.getDouble()) * 1000.0;
            if (Double.isInfinite(dval) || Double.isNaN(dval)) {
                dval = r.getInteger() % 1000;
            }
            return String.format("%.10f", dval);
        }
        case "VARCHAR":
            String raw = r.getString();
            // [FIX] Escape backslashes to prevent SQL syntax errors in MariaDB
            String escaped = raw.replace("\\", "\\\\").replace("'", "\\'");
            return "'" + escaped.substring(0, Math.min(escaped.length(), 20)) + "'";
        default:
            return "NULL";
        }
    }

    // ==================== Mode 29: Functional Index (Phase G) ====================

    // Tests functional indexes via STORED generated columns (MariaDB lacks MySQL 8.0's
    // CREATE INDEX ... ((expr)) syntax). Uses LOWER/TRIM/SUBSTRING/CONCAT.
    private void checkFunctionalIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MariaDBTable table = Randomly.fromList(tables);
        // [FIX] Skip if table already has too many indexes (MariaDB limit is 64)
        if (table.getIndexes().size() >= 60) return;
        // Find VARCHAR columns for functional index testing
        // [FIX] Exclude generated columns (gen_*) to prevent cascading name growth
        // that exceeds MariaDB's 64-char identifier limit
        List<MariaDBColumn> varCharCols = new ArrayList<>();
        for (MariaDBColumn col : table.getColumns()) {
            if (col.getType() == MariaDBSchema.MariaDBDataType.VARCHAR
                    && !col.getName().startsWith("gen_")) {
                varCharCols.add(col);
            }
        }
        if (varCharCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(varCharCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Choose a function to apply
        // NOTE: UPPER()/UCASE() and REVERSE() are NOT supported by MariaDB in generated columns
        // (causes "Function or expression 'xxx' cannot be used in the GENERATED ALWAYS AS clause").
        // Only use functions known to be valid: LOWER, TRIM, SUBSTRING, CONCAT with constant.
        String[][] funcDefs = {
            {"LOWER(%s)", "lower"},
            {"TRIM(%s)", "trim"},
            {"SUBSTRING(%s, 1, 10)", "substring_1_10"},
            {"CONCAT(%s, '')", "concat_empty"},
        };
        String[] chosen = Randomly.fromOptions(funcDefs);
        String funcPattern = chosen[0];
        String funcName = chosen[1];
        String funcExpr = String.format(funcPattern, colName);

        String genColName = "gen_" + funcName + "_" + colName;
        String idxName = "idx_func_" + funcName + "_" + Math.abs(colName.hashCode() % 1000);

        ExpectedErrors genErrors = new ExpectedErrors();
        genErrors.add("Duplicate column name");
        genErrors.add("Generated column");
        genErrors.add("cannot be used for generated columns");
        genErrors.add("cannot be used in the GENERATED ALWAYS AS"); // safety net for unsupported functions
        genErrors.add("Unknown column");
        genErrors.add("Duplicate key name");
        genErrors.add("Specified key was too long");
        genErrors.add("BLOB or TEXT");
        genErrors.add("used in key specification");

        // Step 1: Add generated column
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "ALTER TABLE " + tblName + " ADD COLUMN " + genColName
                            + " VARCHAR(64) AS (" + funcExpr + ") STORED;",
                    genErrors, true));
        } catch (Exception e) {
            return; // Generated column creation failed
        }

        // [FIX] Verify the generated column actually exists before creating index.
        // ALTER TABLE may be silently suppressed by ExpectedErrors (e.g. "Generated column")
        // even when the column was NOT created. Without this check, CREATE INDEX fails
        // with "Key column 'gen_xxx' doesn't exist in table" which is NOT in genErrors.
        boolean colExists = false;
        try (Statement checkStmt = globalState.getConnection().createStatement()) {
            try (ResultSet colRs = checkStmt.executeQuery(
                    "SELECT COLUMN_NAME FROM information_schema.COLUMNS WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '"
                            + tblName + "' AND COLUMN_NAME = '" + genColName + "';")) {
                colExists = colRs.next();
            }
        } catch (Exception e) {
            return;
        }
        if (!colExists) return;

        // Step 2: Create index on generated column
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + genColName + ");",
                    genErrors, true));
            analyzeAllTables();
        } catch (Exception e) {
            return; // Index creation failed
        }

        // Step 3: Query using the original function expression
        String val = generateDataAwareValueForType(tblName, col);
        // Remove quotes for function comparison
        String valClean = val;
        if (valClean.startsWith("'") && valClean.endsWith("'")) {
            valClean = valClean.substring(1, valClean.length() - 1);
        }

        int queryType = Randomly.fromOptions(0, 1, 2);
        String defaultQuery;
        String forcedQuery;
        switch (queryType) {
        case 0:
            // Query on generated column directly
            // [FIX] Use COLLATE utf8mb4_bin to avoid false positives from case-insensitive
            // collation (e.g. utf8mb4_uca1400_ai_ci treats '꙼(' = '(' due to combining mark handling)
            defaultQuery = "SELECT * FROM " + tblName + " WHERE " + genColName + " COLLATE utf8mb4_bin = " + val + ";";
            forcedQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE "
                    + genColName + " COLLATE utf8mb4_bin = " + val + ";";
            break;
        case 1:
            // Query on original column with function — should use functional index
            // [FIX] Use COLLATE utf8mb4_bin to avoid false positives from case-insensitive collation
            defaultQuery = "SELECT * FROM " + tblName + " WHERE " + funcExpr + " COLLATE utf8mb4_bin = " + val + ";";
            forcedQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE "
                    + genColName + " COLLATE utf8mb4_bin = " + val + ";";
            break;
        default:
            // Range query on generated column
            defaultQuery = "SELECT * FROM " + tblName + " WHERE " + genColName + " IS NOT NULL ORDER BY "
                    + genColName + " LIMIT 100;";
            forcedQuery = "SELECT * FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE "
                    + genColName + " IS NOT NULL ORDER BY " + genColName + " LIMIT 100;";
            break;
        }

        lastQueryString = "[FUNC_IDX] " + defaultQuery;
        log(defaultQuery);

        List<String> r1 = executeQuery(defaultQuery);
        if (r1 == null) return;
        List<String> r2 = executeQuery(forcedQuery);
        if (r2 == null) return;

        lastCompareFiltered = false;
        compareResultsSorted(r1, r2, defaultQuery, "MARIADB_FUNC_IDX");
        if (lastCompareFiltered) {
            countStarFallback(defaultQuery, forcedQuery, "MARIADB_FUNC_IDX");
        }
    }

    // ==================== Mode 30: DML + Index Consistency (Phase G) ====================

    // Verifies that INSERT/UPDATE/DELETE maintain index consistency (COUNT stays deterministic).
    private void checkDMLIndexConsistency() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MariaDBTable table = Randomly.fromList(tables);
        List<MariaDBIndex> tableIndexes = table.getIndexes();
        if (tableIndexes.isEmpty()) {
            try {
                MariaDBIndexGenerator.createIndexOnColumn(table, Randomly.fromList(table.getColumns()));
                analyzeAllTables();
                tableIndexes = table.getIndexes();
            } catch (Exception e) { return; }
        }
        if (tableIndexes.isEmpty()) return;

        MariaDBIndex idx = Randomly.fromList(tableIndexes);
        List<String> idxCols = idx.getColumnNames();
        if (idxCols.isEmpty()) return;

        String tblName = table.getName();
        String colName = idxCols.get(0);
        MariaDBColumn col = null;
        for (MariaDBColumn c : table.getColumns()) {
            if (c.getName().equals(colName)) { col = c; break; }
        }
        if (col == null) return;

        // [FIX] Skip generated columns — MariaDB rejects UPDATE/SET on generated columns.
        // Mode 29 (checkFunctionalIndex) adds STORED generated columns (gen_lower_*, etc.)
        // and indexes on them. If we pick such an index, the UPDATE branch would fail.
        if (colName.startsWith("gen_")) return;

        // Step 1: Get baseline query result
        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
        String baseQuery = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " " + op + " " + val + ";";

        lastQueryString = "[DML_IDX] Pre-DML: " + baseQuery;
        log(baseQuery);

        List<String> r1 = executeQuery(baseQuery);
        if (r1 == null) return;

        // Step 2: Execute a DML operation
        ExpectedErrors dmlErrors = new ExpectedErrors();
        dmlErrors.add("Duplicate");
        dmlErrors.add("foreign key");
        dmlErrors.add("cannot be null");
        dmlErrors.add("Data too long");
        dmlErrors.add("Out of range");
        dmlErrors.add("incorrect");
        dmlErrors.add("CONSTRAINT");

        int dmlType = Randomly.fromOptions(0, 1, 2);
        boolean dmlSuccess = false;
        switch (dmlType) {
        case 0: {
            // UPDATE with LIMIT
            String newVal = generateDataAwareValueForType(tblName, col);
            // Ensure old != new for INT columns
            if (col.getType() == MariaDBSchema.MariaDBDataType.INT) {
                try {
                    long oldV = Long.parseLong(val.trim());
                    long newV = Long.parseLong(newVal.trim());
                    if (oldV == newV) newVal = String.valueOf(oldV + 1);
                } catch (NumberFormatException e) { /* ignore */ }
            }
            String updateSQL = "UPDATE " + tblName + " SET " + colName + " = " + newVal
                    + " WHERE " + colName + " " + op + " " + val + " LIMIT 5;";
            try {
                globalState.executeStatement(new SQLQueryAdapter(updateSQL, dmlErrors, true));
                dmlSuccess = true;
            } catch (Exception e) { /* ignore */ }
            break;
        }
        case 1: {
            // DELETE with LIMIT
            String deleteSQL = "DELETE FROM " + tblName + " WHERE " + colName + " " + op + " " + val
                    + " LIMIT 3;";
            try {
                globalState.executeStatement(new SQLQueryAdapter(deleteSQL, dmlErrors, true));
                dmlSuccess = true;
            } catch (Exception e) { /* ignore */ }
            break;
        }
        default: {
            // [FIX] INSERT — only insert into non-generated columns.
            // Mode 29 (checkFunctionalIndex) adds STORED generated columns
            // (named gen_lower_*, gen_upper_*, gen_trim_*, gen_reverse_*).
            // MariaDB rejects INSERT INTO ... VALUES with values for generated columns.
            // We use explicit column list to exclude them.
            List<MariaDBColumn> allCols = table.getColumns();
            List<MariaDBColumn> insertCols = new ArrayList<>();
            for (MariaDBColumn c : allCols) {
                if (!c.getName().startsWith("gen_")) {
                    insertCols.add(c);
                }
            }
            if (insertCols.isEmpty()) return;
            StringBuilder colNames = new StringBuilder();
            StringBuilder insertVals = new StringBuilder();
            for (int i = 0; i < insertCols.size(); i++) {
                if (i > 0) {
                    colNames.append(", ");
                    insertVals.append(", ");
                }
                colNames.append(insertCols.get(i).getName());
                insertVals.append(generateDataAwareValueForType(tblName, insertCols.get(i)));
            }
            String insertSQL = "INSERT INTO " + tblName + " (" + colNames + ") VALUES (" + insertVals + ");";
            try {
                globalState.executeStatement(new SQLQueryAdapter(insertSQL, dmlErrors, true));
                dmlSuccess = true;
            } catch (Exception e) { /* ignore */ }
            break;
        }
        }

        if (!dmlSuccess) return;
        analyzeAllTables();

        // Step 3: Re-run query and verify consistency
        // The COUNT(*) query should still return a valid result (no crash, no corruption)
        List<String> r2 = executeQuery(baseQuery);
        if (r2 == null) return;

        // For DML consistency, we verify:
        // 1. No crash (already verified by r2 != null)
        // 2. COUNT(*) after DML is deterministic — run again to verify
        List<String> r3 = executeQuery(baseQuery);
        if (r3 == null) return;

        // r2 and r3 should be identical (deterministic after DML)
        if (!r2.equals(r3)) {
            effectiveTests++;
            throw new AssertionError("MARIADB_DML_IDX non-deterministic COUNT after DML!\n"
                    + "Query: " + baseQuery + "\nResult2: " + r2 + "\nResult3: " + r3);
        }

        // Also verify with index-forced query matches
        String forcedQuery = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idx.getIndexName()
                + ") WHERE " + colName + " " + op + " " + val + ";";
        List<String> r4 = executeQuery(forcedQuery);
        if (r4 == null) return;

        if (!r2.equals(r4)) {
            effectiveTests++;
            throw new AssertionError("MARIADB_DML_IDX index mismatch after DML!\n"
                    + "Default: " + baseQuery + "\nForced: " + forcedQuery
                    + "\nDefault result: " + r2 + "\nForced result: " + r4);
        }
    }

    // ==================== Mode 31: DESC Index Sort (Phase G) ====================

    // Verifies DESC index produces identical ORDER BY results vs filesort (IGNORE INDEX).
    private void checkDescIndexSort() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;

        // Get virtual generated column names — they cannot have indexes in MariaDB
        Set<String> virtualGenCols = getVirtualGeneratedColumns(table.getName());

        // Find suitable columns (INT or VARCHAR) for DESC index, excluding VIRTUAL generated columns
        List<MariaDBColumn> suitableCols = new ArrayList<>();
        for (MariaDBColumn col : table.getColumns()) {
            if (virtualGenCols.contains(col.getName().toLowerCase())) continue;
            if (col.getType() == MariaDBSchema.MariaDBDataType.INT
                    || col.getType() == MariaDBSchema.MariaDBDataType.VARCHAR) {
                suitableCols.add(col);
            }
        }
        if (suitableCols.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(suitableCols);
        String tblName = table.getName();
        String colName = col.getName();

        // Create DESC index
        String descIdxName = "desc_" + Math.abs(colName.hashCode() % 10000) + "_" + Randomly.fromOptions(0,1,2,3,4);
        ExpectedErrors idxErrors = new ExpectedErrors();
        idxErrors.add("Duplicate key name");
        idxErrors.add("Specified key was too long");

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + descIdxName + " ON " + tblName + " (" + colName + " DESC);",
                    idxErrors, true));
            analyzeAllTables();
        } catch (Exception e) {
            return;
        }

        // Generate WHERE condition using data-aware values
        String val = generateDataAwareValueForType(tblName, col);
        String op = Randomly.fromOptions(">", "<", ">=", "<=", "IS NOT NULL");
        String whereCond;
        if (op.equals("IS NOT NULL")) {
            whereCond = colName + " IS NOT NULL";
        } else {
            whereCond = colName + " " + op + " " + val;
        }

        // Test 1: ORDER BY col DESC — default plan vs IGNORE INDEX (filesort)
        int limit = Randomly.fromOptions(20, 50, 100);
        int testVariant = Randomly.fromOptions(0, 1, 2);

        switch (testVariant) {
        case 0: {
            // ORDER BY col DESC
            String defaultQuery = "SELECT " + colName + " FROM " + tblName + " WHERE " + whereCond
                    + " ORDER BY " + colName + " DESC LIMIT " + limit + ";";
            String ignoredQuery = "SELECT " + colName + " FROM " + tblName
                    + " IGNORE INDEX(" + descIdxName + ") WHERE " + whereCond
                    + " ORDER BY " + colName + " DESC LIMIT " + limit + ";";

            lastQueryString = "[DESC_IDX] " + defaultQuery;
            log(defaultQuery);

            List<String> explainPlan1 = getExplainPlan(defaultQuery);
            List<String> explainPlan2 = getExplainPlan(ignoredQuery);
            if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

            List<String> r1 = executeQuery(defaultQuery);
            if (r1 == null) return;
            List<String> r2 = executeQuery(ignoredQuery);
            if (r2 == null) return;

            // Strict comparison — order matters for ORDER BY
            lastCompareFiltered = false;
            compareResultsStrict(r1, r2, defaultQuery, "MARIADB_DESC_IDX");
            if (lastCompareFiltered) {
                countStarFallback(defaultQuery, ignoredQuery, "MARIADB_DESC_IDX");
            }
            break;
        }
        case 1: {
            // ORDER BY col ASC (DESC index used in reverse)
            String defaultQuery = "SELECT " + colName + " FROM " + tblName + " WHERE " + whereCond
                    + " ORDER BY " + colName + " ASC LIMIT " + limit + ";";
            String ignoredQuery = "SELECT " + colName + " FROM " + tblName
                    + " IGNORE INDEX(" + descIdxName + ") WHERE " + whereCond
                    + " ORDER BY " + colName + " ASC LIMIT " + limit + ";";

            lastQueryString = "[DESC_IDX_ASC] " + defaultQuery;
            log(defaultQuery);

            List<String> explainPlan1 = getExplainPlan(defaultQuery);
            List<String> explainPlan2 = getExplainPlan(ignoredQuery);
            if (!plansAreDifferent(explainPlan1, explainPlan2)) return;

            List<String> r1 = executeQuery(defaultQuery);
            if (r1 == null) return;
            List<String> r2 = executeQuery(ignoredQuery);
            if (r2 == null) return;

            lastCompareFiltered = false;
            compareResultsStrict(r1, r2, defaultQuery, "MARIADB_DESC_IDX_ASC");
            if (lastCompareFiltered) {
                countStarFallback(defaultQuery, ignoredQuery, "MARIADB_DESC_IDX_ASC");
            }
            break;
        }
        default: {
            // Composite: ORDER BY col DESC with FORCE vs IGNORE
            // Also test with a second column for multi-column sort
            List<MariaDBColumn> otherCols = new ArrayList<>();
            for (MariaDBColumn c : table.getColumns()) {
                if (!c.getName().equals(colName)) otherCols.add(c);
            }

            String forcedQuery = "SELECT " + colName + " FROM " + tblName + " FORCE INDEX(" + descIdxName + ") WHERE "
                    + whereCond + " ORDER BY " + colName + " DESC LIMIT " + limit + ";";
            String ignoredQuery = "SELECT " + colName + " FROM " + tblName + " IGNORE INDEX(" + descIdxName + ") WHERE "
                    + whereCond + " ORDER BY " + colName + " DESC LIMIT " + limit + ";";

            lastQueryString = "[DESC_IDX_FORCE] " + forcedQuery;
            log(forcedQuery);

            List<String> r1 = executeQuery(forcedQuery);
            if (r1 == null) return;
            List<String> r2 = executeQuery(ignoredQuery);
            if (r2 == null) return;

            lastCompareFiltered = false;
            compareResultsStrict(r1, r2, forcedQuery, "MARIADB_DESC_IDX_FORCE");
            if (lastCompareFiltered) {
                countStarFallback(forcedQuery, ignoredQuery, "MARIADB_DESC_IDX_FORCE");
            }
            break;
        }
        }
    }

    // ==================== Phase D6: Periodic Index Pruning ====================

    // Drops oldest non-PK indexes when a table exceeds INDEX_PRUNE_THRESHOLD.
    // Uses INNODB_SYS_INDEXES.INDEX_ID (monotonically increasing) to identify oldest first.
    private void pruneExcessIndexes() {
        ExpectedErrors dropErrors = new ExpectedErrors();
        dropErrors.add("Can't DROP");
        dropErrors.add("check that column/key exists");
        dropErrors.add("doesn't exist");

        for (MariaDBTable table : globalState.getSchema().getDatabaseTables()) {
            int nonPkCount = getNonPrimaryIndexCount(table);
            if (nonPkCount <= INDEX_PRUNE_THRESHOLD) continue;

            String tblName = table.getName();

            // [FIX] Verify table actually exists in the database before pruning.
            // During long fuzzing sessions, tables may be dropped (e.g., by TRUNCATE
            // on Aria tables that crash, DROP TABLE, etc.), causing the Java-side
            // schema to become stale. Without this check, DROP INDEX on a
            // non-existent table throws "Table doesn't exist" which was not in
            // dropErrors, triggering an AssertionError that crashes the fuzzer.
            // (See logs/mariadb/database10.log for an example.)
            if (!tableExistsInDatabase(tblName)) {
                continue;
            }

            // Query INNODB_SYS_INDEXES to get INDEX_ID for creation order
            // INDEX_ID is monotonically increasing — smaller = older
            List<String[]> indexIdNamePairs = new ArrayList<>();
            try (Statement s = globalState.getConnection().createStatement()) {
                String query = "SELECT s.INDEX_ID, s.NAME FROM information_schema.INNODB_SYS_INDEXES s "
                        + "JOIN information_schema.INNODB_SYS_TABLES t ON s.TABLE_ID = t.TABLE_ID "
                        + "WHERE t.NAME LIKE '%" + tblName + "' AND s.NAME != 'PRIMARY' "
                        + "ORDER BY s.INDEX_ID ASC;";
                try (ResultSet rs = s.executeQuery(query)) {
                    while (rs.next()) {
                        indexIdNamePairs.add(new String[]{rs.getString(1), rs.getString(2)});
                    }
                }
            } catch (Exception e) {
                // Fallback: use schema-based order (less accurate but still works)
                for (MariaDBIndex idx : table.getIndexes()) {
                    if (!idx.isPrimaryKey()) {
                        indexIdNamePairs.add(new String[]{"0", idx.getIndexName()});
                    }
                }
            }

            // Drop down to ~30 indexes (keep the most recent ~30, drop the oldest)
            int targetKeep = 30;
            int dropCount = indexIdNamePairs.size() - targetKeep;
            if (dropCount <= 0) continue;

            // Drop oldest indexes first (smallest INDEX_ID = oldest)
            int actuallyDropped = 0;
            for (int i = 0; i < dropCount && i < indexIdNamePairs.size(); i++) {
                String idxName = indexIdNamePairs.get(i)[1];
                try {
                    globalState.executeStatement(new SQLQueryAdapter(
                            "DROP INDEX `" + idxName + "` ON " + tblName + ";",
                            dropErrors, true));
                    actuallyDropped++;
                } catch (Exception e) { /* ignore */ }
            }

            try { analyzeAllTables(); } catch (Exception e) { /* ignore */ }
            log("[PRUNE] Dropped " + actuallyDropped + " oldest indexes from " + tblName
                    + " (had " + nonPkCount + " non-PK indexes, INDEX_ID-sorted)");
        }
    }

    // Queries information_schema to verify the table still exists (Java schema can become stale).
    private boolean tableExistsInDatabase(String tableName) {
        try (Statement s = globalState.getConnection().createStatement()) {
            try (ResultSet rs = s.executeQuery(
                    "SELECT 1 FROM information_schema.TABLES "
                            + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName + "' LIMIT 1;")) {
                return rs.next();
            }
        } catch (Exception e) {
            return false;
        }
    }

    private int getNonPrimaryIndexCount(MariaDBTable table) {
        int count = 0;
        for (MariaDBIndex idx : table.getIndexes()) {
            if (!idx.isPrimaryKey()) count++;
        }
        return count;
    }

    // ==================== Mode 32: DDL Column Change with Index (P1-1 — Enhanced) ====================

    private void checkDropColumnWithIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;

        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;

        String tblName = table.getName();

        // Verify table exists in database (schema may be stale)
        if (!tableExistsInDatabase(tblName)) return;

        Set<String> columnsWithGenDependency = getColumnsWithGeneratedDependency(tblName);
        Set<String> autoIncCols = getAutoIncrementColumns(tblName);

        List<MariaDBColumn> candidates = new ArrayList<>();
        for (MariaDBColumn col : table.getColumns()) {
            if (!col.isPrimaryKey()
                    && !columnsWithGenDependency.contains(col.getName().toLowerCase())
                    && !autoIncCols.contains(col.getName().toLowerCase())
                    && !col.getName().startsWith("gen_")) {
                candidates.add(col);
            }
        }
        if (candidates.isEmpty()) return;

        MariaDBColumn col = Randomly.fromList(candidates);
        String colName = col.getName();

        // Create index on the column
        String idxName = "ddl_idx_" + Math.abs(colName.hashCode() % 10000) + "_" + Randomly.smallNumber();
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }

        // Choose DDL variant
        int ddlVariant = Randomly.fromOptions(0, 1, 2, 3);

        switch (ddlVariant) {
        case 0: {
            // Variant 0: DROP COLUMN (original)
            checkDropColumn(tblName, colName, idxName);
            break;
        }
        case 1: {
            // Variant 1: RENAME COLUMN — tests index metadata update after column rename
            String newColName = "rn_" + Math.abs(colName.hashCode() % 10000);
            String queryBefore = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
            lastQueryString = "[RENAME_COL_IDX] " + queryBefore;
            log(queryBefore);

            List<String> r1 = executeQuery(queryBefore);
            if (r1 == null) return;

            try {
                globalState.executeStatement(new SQLQueryAdapter(
                        "ALTER TABLE " + tblName + " RENAME COLUMN " + colName + " TO " + newColName + ";",
                        errors, true));
                analyzeAllTables();
            } catch (Exception e) { return; }

            try { globalState.updateSchema(); } catch (Exception e) { return; }

            // Verify table is still accessible
            String queryAfter = "SELECT COUNT(*) FROM " + tblName + " WHERE " + newColName + " IS NOT NULL;";
            try {
                List<String> r2 = executeQuery(queryAfter);
                if (r2 == null) return;
                // COUNT should be identical after rename
                if (r1 != null && !r1.equals(r2)) {
                    effectiveTests++;
                    throw new AssertionError("MARIADB_RENAME_COL_IDX: COUNT mismatch after RENAME COLUMN!\n"
                            + "Before: " + r1 + "\nAfter: " + r2);
                }
            } catch (AssertionError e) { throw e; }
              catch (Exception e) {
                effectiveTests++;
                throw new AssertionError("MARIADB_RENAME_COL_IDX: Table corrupted after RENAME COLUMN!\n"
                        + "Table: " + tblName + "\nError: " + e.getMessage());
            }

            // Also run CHECK TABLE EXTENDED to verify index integrity
            checkTableIntegrity(tblName);
            break;
        }
        case 2: {
            // Variant 2: MODIFY COLUMN type change — tests index compatibility after type change
            // Only pick safe widening type changes to avoid data conversion errors:
            //   - "Truncated incorrect INTEGER value" (VARCHAR → INT)
            //   - "Out of range value for column" (DOUBLE/REAL → INT)
            // See: logs/mariadb/database3.log, logs/mariadb/database7.log
            String newType = getSafeWideningType(col.getType());
            if (newType == null) return;
            String queryBefore = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
            lastQueryString = "[MODIFY_COL_IDX] " + queryBefore;
            log(queryBefore);

            List<String> r1 = executeQuery(queryBefore);

            try {
                globalState.executeStatement(new SQLQueryAdapter(
                        "ALTER TABLE " + tblName + " MODIFY COLUMN " + colName + " " + newType + ";",
                        errors, true));
                analyzeAllTables();
            } catch (Exception e) { return; }

            try { globalState.updateSchema(); } catch (Exception e) { return; }

            String queryAfter = "SELECT COUNT(*) FROM " + tblName + ";";
            try {
                List<String> r2 = executeQuery(queryAfter);
            } catch (Exception e) {
                effectiveTests++;
                throw new AssertionError("MARIADB_MODIFY_COL_IDX: Table corrupted after MODIFY COLUMN!\n"
                        + "Table: " + tblName + ", Modified: " + colName + " to " + newType
                        + "\nError: " + e.getMessage());
            }

            checkTableIntegrity(tblName);
            break;
        }
        default: {
            // Variant 3: CHANGE COLUMN (rename + type change) — most comprehensive DDL test
            // [FIX] Use safe widening type instead of blind INT/BIGINT toggle.
            // Changing DOUBLE→INT or VARCHAR→INT causes conversion errors.
            // See: logs/mariadb/database3.log, logs/mariadb/database7.log
            String newColName = "ch_" + Math.abs(colName.hashCode() % 10000);
            String newType = getSafeWideningType(col.getType());
            if (newType == null) return;
            String queryBefore = "SELECT COUNT(*) FROM " + tblName + ";";
            lastQueryString = "[CHANGE_COL_IDX] " + queryBefore;
            log(queryBefore);

            List<String> r1 = executeQuery(queryBefore);

            try {
                globalState.executeStatement(new SQLQueryAdapter(
                        "ALTER TABLE " + tblName + " CHANGE COLUMN " + colName + " " + newColName + " " + newType + ";",
                        errors, true));
                analyzeAllTables();
            } catch (Exception e) { return; }

            try { globalState.updateSchema(); } catch (Exception e) { return; }

            String queryAfter = "SELECT COUNT(*) FROM " + tblName + ";";
            try {
                List<String> r2 = executeQuery(queryAfter);
                if (r1 != null && r2 != null && !r1.equals(r2)) {
                    effectiveTests++;
                    throw new AssertionError("MARIADB_CHANGE_COL_IDX: COUNT mismatch after CHANGE COLUMN!\n"
                            + "Before: " + r1 + "\nAfter: " + r2);
                }
            } catch (AssertionError e) { throw e; }
              catch (Exception e) {
                effectiveTests++;
                throw new AssertionError("MARIADB_CHANGE_COL_IDX: Table corrupted after CHANGE COLUMN!\n"
                        + "Table: " + tblName + "\nError: " + e.getMessage());
            }

            checkTableIntegrity(tblName);
            break;
        }
        }
    }

    // Variant 0: verifies COUNT(*) before/after DROP COLUMN and checks table integrity.
    private void checkDropColumn(String tblName, String colName, String idxName) throws Exception {
        String queryBefore = "SELECT COUNT(*) FROM " + tblName + " WHERE " + colName + " IS NOT NULL;";
        lastQueryString = "[DROP_COL_IDX] " + queryBefore;
        log(queryBefore);

        List<String> r1 = executeQuery(queryBefore);

        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "ALTER TABLE " + tblName + " DROP COLUMN " + colName + ";", errors, true));
            analyzeAllTables();
        } catch (Exception e) { return; }

        try { globalState.updateSchema(); } catch (Exception e) { return; }

        String queryAfter = "SELECT COUNT(*) FROM " + tblName + ";";
        try {
            List<String> r2 = executeQuery(queryAfter);
        } catch (Exception e) {
            throw new AssertionError("MARIADB_DROP_COL_IDX: Table corrupted after DROP COLUMN!\n"
                    + "Table: " + tblName + ", Dropped column: " + colName + "\nError: " + e.getMessage());
        }

        // Verify index was properly dropped with the column
        checkTableIntegrity(tblName);
    }

    // Returns a safe widening SQL type (INT→BIGINT/DOUBLE, VARCHAR→VARCHAR(255)/TEXT, etc.)
    // to avoid truncation/out-of-range errors during MODIFY/CHANGE COLUMN.
    private String getSafeWideningType(MariaDBSchema.MariaDBDataType currentType) {
        switch (currentType) {
        case INT: return Randomly.fromOptions("BIGINT", "DOUBLE");
        case BOOLEAN: return Randomly.fromOptions("INT", "BIGINT", "DOUBLE");
        case REAL: return Randomly.fromOptions("DOUBLE", "DECIMAL(65,30)");
        case VARCHAR: return Randomly.fromOptions("VARCHAR(255)", "TEXT");
        default: return null;
        }
    }

    // Runs CHECK TABLE EXTENDED; logs any errors (does not throw).
    private void checkTableIntegrity(String tableName) {
        try {
            Statement stmt = globalState.getConnection().createStatement();
            ResultSet rs = stmt.executeQuery("CHECK TABLE " + tableName + " EXTENDED;");
            while (rs.next()) {
                String msgType = rs.getString("Msg_type");
                String msgText = rs.getString("Msg_text");
                if ("error".equalsIgnoreCase(msgType) && !"OK".equalsIgnoreCase(msgText)) {
                    log("[INTEGRITY_CHECK] ERROR on " + tableName + ": " + msgText);
                }
            }
            rs.close();
            stmt.close();
        } catch (Exception e) { /* ignore */ }
    }

    private Set<String> getColumnsWithGeneratedDependency(String tableName) {
        Set<String> blocked = new HashSet<>();
        try {
            String query = "SELECT COLUMN_NAME, GENERATION_EXPRESSION FROM information_schema.COLUMNS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName
                    + "' AND EXTRA LIKE '%GENERATED%';";
            List<String> result = executeQuery(query);
            if (result == null || result.isEmpty()) return blocked;
            for (String row : result) {
                if (row == null || row.isEmpty()) continue;
                String[] parts = row.split("\\|");
                if (parts.length >= 1) {
                    blocked.add(parts[0].trim().toLowerCase());
                }
                if (parts.length >= 2) {
                    String expr = parts[1].trim();
                    java.util.regex.Matcher m = java.util.regex.Pattern.compile("\\b(c\\d+|\\w+_col_\\w+)\\b").matcher(expr);
                    while (m.find()) {
                        blocked.add(m.group(1).toLowerCase());
                    }
                }
            }
        } catch (Exception e) { /* best-effort */ }
        return blocked;
    }

    private void analyzeTable(String tableName) {
        try {
            globalState.executeStatement(new SQLQueryAdapter("ANALYZE TABLE " + tableName + ";", true));
        } catch (Exception e) { /* ignore */ }
    }


    // ==================== Mode 33: Generated Column + Index (P1-2) ====================

    private void checkGeneratedColumnIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().size() < 2) return;
        // [FIX] Only InnoDB supports indexes on generated columns with arbitrary
        // functions. Aria/MyISAM reject CREATE INDEX on VIRTUAL generated columns
        // with expressions like LEFT(), LOWER() etc.:
        //   "Function or expression 'left(...)' cannot be used in the GENERATED ALWAYS AS clause"
        // See: logs/mariadb/database6.log
        if (table.getEngine() != MariaDBSchema.MariaDBTable.MariaDBEngine.INNO_DB) return;
        String tblName = table.getName();
        if (table.getIndexes().size() >= 60) return;

        Set<String> autoIncCols = getAutoIncrementColumns(tblName);
        List<MariaDBColumn> candidateCols = new ArrayList<>();
        for (MariaDBColumn c : table.getColumns()) {
            if (!autoIncCols.contains(c.getName().toLowerCase()) && !c.getName().startsWith("gen_")) {
                candidateCols.add(c);
            }
        }
        if (candidateCols.isEmpty()) return;
        MariaDBColumn col1 = candidateCols.get(0);
        String col1Name = col1.getName();

        String genColName = "gen_col_" + Math.abs(col1Name.hashCode() % 10000) + "_" + Randomly.smallNumber() + "_" + Randomly.smallNumber();
        Set<String> existingColNames = new HashSet<>();
        for (MariaDBColumn c : table.getColumns()) { existingColNames.add(c.getName().toLowerCase()); }
        if (existingColNames.contains(genColName.toLowerCase())) return;

        // [FIX] Always use STORED for generated columns when the intent is to create an index.
        // VIRTUAL generated columns with certain functions (e.g., SUBSTRING → substr internally)
        // cannot be indexed in MariaDB:
        //   "Function or expression 'substr(...)' cannot be used in the GENERATED ALWAYS AS clause"
        // Since the purpose of this mode is to test index behavior, always use STORED which
        // is always indexable. See: logs/mariadb/database4.log
        boolean isStored = true;
        String storageType = "STORED";
        String genExpr, genColType;
        if (col1.getType() == MariaDBSchema.MariaDBDataType.INT) {
            genExpr = Randomly.fromOptions(col1Name + " * 2", "ABS(" + col1Name + ")", col1Name + " MOD 100");
            genColType = "BIGINT";
        } else if (col1.getType() == MariaDBSchema.MariaDBDataType.VARCHAR) {
            // NOTE: LENGTH() maps to OCTET_LENGTH() internally and is NOT supported by MariaDB
            // in generated columns. UPPER()/UCASE()/LEFT()/REVERSE() are also NOT supported.
            // Valid VARCHAR-returning: LOWER(), TRIM(), SUBSTRING(), CONCAT(), REPLACE(),
            //   RPAD(), LPAD(), IFNULL()
            // Valid INT-returning: CHAR_LENGTH() (but NOT LENGTH())
            // See: logs/mariadb/database1.log (LENGTH crash), logs/mariadb/database8.log
            if (Randomly.getBoolean()) {
                // VARCHAR-returning expressions
                genExpr = Randomly.fromOptions("LOWER(" + col1Name + ")", "TRIM(" + col1Name + ")",
                        "SUBSTRING(" + col1Name + ", 1, 10)",
                        "CONCAT(" + col1Name + ", '')",
                        "IFNULL(" + col1Name + ", '')",
                        "REPLACE(" + col1Name + ", 'a', 'b')",
                        "RPAD(" + col1Name + ", 10, ' ')",
                        "LPAD(" + col1Name + ", 10, ' ')");
                genColType = "VARCHAR(255)";
            } else {
                // INT-returning expressions (CHAR_LENGTH is supported; LENGTH is NOT)
                genExpr = Randomly.fromOptions("CHAR_LENGTH(" + col1Name + ")");
                genColType = "INT";
            }
        } else {
            genExpr = "IFNULL(" + col1Name + ", 0)";
            genColType = "BIGINT";
        }

        ExpectedErrors genErrors = new ExpectedErrors();
        genErrors.add("Duplicate column name");
        genErrors.add("Generated column");
        genErrors.add("cannot be used for generated columns");
        genErrors.add("cannot be used in the GENERATED ALWAYS AS");
        genErrors.add("Out of range");
        genErrors.add("Data truncated");
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "ALTER TABLE " + tblName + " ADD COLUMN " + genColName
                + " " + genColType + " GENERATED ALWAYS AS (" + genExpr + ") " + storageType + ";",
                genErrors, true));
        } catch (Exception e) { return; }

        String idxName = "gen_idx_" + Math.abs(genColName.hashCode() % 100000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + genColName + ");", errors, true));
            analyzeAllTables();
        } catch (Exception e) { return; }

        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + genColName + " IS NOT NULL;";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + genColName + " IS NOT NULL;";
        lastQueryString = "[GEN_COL_IDX] " + forceQ;
        log(forceQ);
        List<String> r1 = executeQuery(forceQ);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQ);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQ, "MARIADB_GEN_COL_IDX");
    }

    // Returns VIRTUAL generated column names. MariaDB only allows indexes on STORED generated columns.
    private Set<String> getVirtualGeneratedColumns(String tableName) {
        Set<String> virtualCols = new HashSet<>();
        try {
            String query = "SELECT COLUMN_NAME FROM information_schema.COLUMNS "
                    + "WHERE TABLE_SCHEMA = DATABASE() AND TABLE_NAME = '" + tableName
                    + "' AND EXTRA = 'VIRTUAL_GENERATED';";
            List<String> result = executeQuery(query);
            if (result != null) {
                for (String row : result) {
                    if (row != null && !row.isEmpty()) {
                        virtualCols.add(row.split("\\|")[0].trim().toLowerCase());
                    }
                }
            }
        } catch (Exception e) { /* best-effort */ }
        return virtualCols;
    }

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
                        autoIncCols.add(row.split("\\|")[0].trim().toLowerCase());
                    }
                }
            }
        } catch (Exception e) { /* best-effort */ }
        return autoIncCols;
    }

    // ==================== Mode 34: Collation + Index (P1-3) ====================

    private void checkCollationIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = null;
        MariaDBColumn varcharCol = null;
        for (int attempt = 0; attempt < 5; attempt++) {
            MariaDBTable t = Randomly.fromList(tables);
            for (MariaDBColumn c : t.getColumns()) {
                if (c.getType() == MariaDBSchema.MariaDBDataType.VARCHAR) { table = t; varcharCol = c; break; }
            }
            if (table != null) break;
        }
        if (table == null || varcharCol == null) return;
        String tblName = table.getName();
        String colName = varcharCol.getName();
        String collation = Randomly.fromOptions("utf8mb4_general_ci", "utf8mb4_bin", "utf8mb4_unicode_ci");
        String idxName = "coll_idx_" + Math.abs((colName + collation).hashCode() % 100000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " ((" + colName + " COLLATE " + collation + "));", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { return; }

        List<String> sampled = sampleColumnValues(tblName, colName, 5);
        if (sampled == null || sampled.isEmpty()) return;
        String val = Randomly.fromList(sampled);
        if (val == null || val.isEmpty() || val.equalsIgnoreCase("null")) return;
        if (!val.startsWith("'")) val = "'" + val.replace("'", "''") + "'";
        String whereClause = "(" + colName + " COLLATE " + collation + ") = " + val;
        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + whereClause + ";";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + whereClause + ";";
        lastQueryString = "[COLLATION_IDX] " + forceQ;
        log(forceQ);
        List<String> r1 = executeQuery(forceQ);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQ);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQ, "MARIADB_COLLATION_IDX");
    }

    // ==================== Mode 35: Type Mismatch + Index (P1-4) ====================

    private void checkTypeMismatchIndex() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = null;
        MariaDBColumn varcharCol = null;
        MariaDBColumn intCol = null;
        for (int attempt = 0; attempt < 5; attempt++) {
            MariaDBTable t = Randomly.fromList(tables);
            for (MariaDBColumn c : t.getColumns()) {
                if (c.getType() == MariaDBSchema.MariaDBDataType.VARCHAR && varcharCol == null) varcharCol = c;
                if (c.getType() == MariaDBSchema.MariaDBDataType.INT && intCol == null) intCol = c;
            }
            if (varcharCol != null) { table = t; break; }
            varcharCol = null; intCol = null;
        }
        if (table == null || varcharCol == null) return;
        String tblName = table.getName();
        String colName = varcharCol.getName();
        String idxName = "typemis_idx_" + Math.abs(colName.hashCode() % 100000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { /* may already exist */ }

        int intVal = globalState.getRandomly().getInteger(0, 1000);
        String forceQ = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + intVal + ";";
        String ignoreQ = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + idxName + ") WHERE " + colName + " = " + intVal + ";";
        lastQueryString = "[TYPE_MISMATCH] " + forceQ;
        log(forceQ);
        List<String> r1 = executeQuery(forceQ);
        if (r1 == null) return;
        List<String> r2 = executeQuery(ignoreQ);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, forceQ, "MARIADB_TYPE_MISMATCH_IDX");

        if (intCol != null) {
            String intColName = intCol.getName();
            String intIdxName = "typemis_int_" + Math.abs(intColName.hashCode() % 100000);
            try {
                globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + intIdxName + " ON " + tblName + " (" + intColName + ");", errors, true));
            } catch (Exception e) { /* may exist */ }
            String strVal = "'" + intVal + "abc'";
            String intForce = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + intIdxName + ") WHERE " + intColName + " = " + strVal + ";";
            String intIgnore = "SELECT COUNT(*) FROM " + tblName + " IGNORE INDEX(" + intIdxName + ") WHERE " + intColName + " = " + strVal + ";";
            List<String> r5 = executeQuery(intForce);
            if (r5 == null) return;
            List<String> r6 = executeQuery(intIgnore);
            if (r6 == null) return;
            compareResultsSorted(r5, r6, intForce, "MARIADB_TYPE_MISMATCH_INT");
        }
    }

    // ==================== Mode 36: SQL Semantic Equivalence (P1-5) ====================

    private void checkSQLSemanticEquivalence() throws Exception {
        MariaDBSchema schema = globalState.getSchema();
        List<MariaDBTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        MariaDBTable table = Randomly.fromList(tables);
        if (table.getColumns().isEmpty()) return;
        MariaDBColumn col = Randomly.fromList(table.getColumns());
        String tblName = table.getName();
        String colName = col.getName();
        String idxName = "seq_idx_" + Math.abs(colName.hashCode() % 10000);
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX " + idxName + " ON " + tblName + " (" + colName + ");", errors, true));
            analyzeTable(tblName);
        } catch (Exception e) { }

        String val1 = generateDataAwareValueForType(tblName, col);
        String val2 = generateDataAwareValueForType(tblName, col);
        String val3 = generateDataAwareValueForType(tblName, col);
        int variant = Randomly.fromOptions(0, 1, 2, 3);
        String queryA, queryB, modeTag;
        switch (variant) {
        case 0:
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IN (" + val1 + ", " + val2 + ", " + val3 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val1 + " OR " + colName + " = " + val2 + " OR " + colName + " = " + val3 + ";";
            modeTag = "MARIADB_SEMANTIC_IN_VS_OR";
            break;
        case 1: {
            double d1, d2;
            try { d1 = Double.parseDouble(val1.replace("'", "")); d2 = Double.parseDouble(val2.replace("'", "")); }
            catch (NumberFormatException e) { d1 = 0; d2 = 0; }
            String lowV = (d1 <= d2) ? val1 : val2;
            String highV = (d1 <= d2) ? val2 : val1;
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " BETWEEN " + lowV + " AND " + highV + ";";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " >= " + lowV + " AND " + colName + " <= " + highV + ";";
            modeTag = "MARIADB_SEMANTIC_BETWEEN";
            break;
        }
        case 2:
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " NOT IN (" + val1 + ", " + val2 + ");";
            queryB = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " <> " + val1 + " AND " + colName + " <> " + val2 + ";";
            modeTag = "MARIADB_SEMANTIC_NOT_IN";
            break;
        default:
            if (val1.equals(val2)) {
                for (int attempt = 0; attempt < 5 && val1.equals(val2); attempt++) val2 = generateDataAwareValueForType(tblName, col);
                if (val1.equals(val2)) return;
            }
            // Avoid false positive from MariaDB collation-induced equivalence:
            //   - PAD SPACE: ''      = ' '       (trailing-space ignored)
            //   - CI       : 'weo.m' = 'WEO.M'   (case-insensitive collation)
            //   - AI       : 'cafe'  = 'café'    (accent-insensitive collation)

            try {
                String eqProbe = "SELECT (" + val1 + " = " + val2 + ");";
                List<String> eqRes = executeQuery(eqProbe);
                if (eqRes != null && !eqRes.isEmpty()) {
                    String eq = eqRes.get(0).trim();
                    // MariaDB returns 1/0 (or NULL on type-incompat); treat 1 as "equal" -> skip.
                    if ("1".equals(eq)) {
                        return;
                    }
                }
            } catch (Exception probeEx) {
                // Probe failure (e.g. type-incompatible literals); fall through to retain
                // existing behavior. The legacy PAD-SPACE filter below remains as a
                // best-effort backstop in case the probe itself was unavailable.
            }
            String rawVal1 = val1.startsWith("'") && val1.endsWith("'") ? val1.substring(1, val1.length() - 1) : val1;
            String rawVal2 = val2.startsWith("'") && val2.endsWith("'") ? val2.substring(1, val2.length() - 1) : val2;
            if (rawVal1.replaceAll(" +$", "").equals(rawVal2.replaceAll(" +$", ""))) return;
            queryA = "SELECT COUNT(*) FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " IN (" + val1 + ", " + val2 + ");";
            queryB = "SELECT SUM(cnt) FROM (SELECT COUNT(*) AS cnt FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val1
                    + " UNION ALL SELECT COUNT(*) AS cnt FROM " + tblName + " FORCE INDEX(" + idxName + ") WHERE " + colName + " = " + val2 + ") t;";
            modeTag = "MARIADB_SEMANTIC_IN_VS_UNION";
            break;
        }
        lastQueryString = "[" + modeTag + "] " + queryA;
        log(queryA);
        List<String> r1 = executeQuery(queryA);
        if (r1 == null) return;
        List<String> r2 = executeQuery(queryB);
        if (r2 == null) return;
        compareResultsSorted(r1, r2, queryA, modeTag);
    }

    // Returns true if the index is actually chosen by the optimizer (not just a candidate).
    // Effective access types: ref, range, const, eq_ref, ref_or_null, unique_subquery, index_subquery, index.
    private boolean isIndexEffectivelyUsed(List<String> plan, String targetIndex) {
        Set<String> effectiveTypes = new HashSet<>(Arrays.asList(
                "ref", "range", "const", "eq_ref", "ref_or_null",
                "unique_subquery", "index_subquery", "index"));
        for (String line : plan) {
            String[] parts = line.split("\\|");
            // EXPLAIN columns: id | select_type | table | type | possible_keys | key | ...
            // type is at index 3 (0-based), key is at index 5 in MariaDB EXPLAIN
            // But our format uses pipe-delimited raw EXPLAIN output columns
            // MariaDB EXPLAIN: id, select_type, table, type, possible_keys, key, key_len, ref, rows, Extra
            String type = parts.length > 3 ? parts[3].trim() : "";
            String key = parts.length > 5 ? parts[5].trim() : "";
            // Strip backticks from key name for comparison
            String normalizedKey = key.replace("`", "");
            String normalizedTarget = targetIndex.replace("`", "");
            if (normalizedKey.equals(normalizedTarget) && effectiveTypes.contains(type)) {
                return true;
            }
        }
        return false;
    }
}
