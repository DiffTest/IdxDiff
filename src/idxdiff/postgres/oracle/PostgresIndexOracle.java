package idxdiff.postgres.oracle;

import java.sql.ResultSet;
import java.sql.SQLException;
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
 * PostgreSQL index oracle. Compares equivalent queries on EXPLAIN-verified index and
 * index-independent paths without changing optimizer settings; also checks index integrity.
 */
public class PostgresIndexOracle implements TestOracle<PostgresGlobalState> {

    private final PostgresGlobalState globalState;
    private final ExpectedErrors errors;

    private String lastQueryString;
    private boolean dataPopulated = false;
    private int iterCount = 0; // per-thread check() iteration counter for periodic refresh
    // Analyze each table once per data epoch; invalidate after DML.
    private final java.util.Set<String> analyzedThisEpoch = new java.util.HashSet<>();
    private int gsVmTries = 0; // bounded VM-heal attempts for idx_gs (case 53)
    private int aggregateFallbackUsed = 0; // how many times COUNT(*) fallback was used
    private boolean lastCompareFiltered = false; // set true when compareResults filters out a difference

    // Count gate passes, including equal results, and report unexercised shapes at shutdown.
    // Disable counting and reporting with -Didx.covcount=0.
    private static final boolean COV_COUNT = !"0".equals(System.getProperty("idx.covcount"));
    private static final long COV_FLOOR = 2000L; // only emit the silent-shape warning once the run is substantial
    private static final java.util.concurrent.ConcurrentHashMap<String, java.util.concurrent.atomic.LongAdder> COV_HIST = new java.util.concurrent.ConcurrentHashMap<>();
    // Add the primary comparator tag of each new shape here; omit legacy and secondary checks.
    private static final java.util.Set<String> EXPECTED_TAGS = new java.util.HashSet<>(java.util.Arrays.asList(
            "PG_AMCHECK", "PG_NONSARGABLE", "PG_NONSARGABLE_ORD", "PG_NS_PARTIAL", "PG_NS_PARTIMPL", "PG_NS_EXPR",
            "PG_NS_BRIN", "PG_NS_BRINBLOOM", "PG_NS_GINJ", "PG_NS_GINA", "PG_NS_GINJP", "PG_NS_GPGIST",
            "PG_NS_PREFIXRANGE", "PG_NS_SAOP", "PG_NS_HASH", "PG_NS_COVER", "PG_NS_BITMAP", "PG_NS_NULL",
            "PG_NS_COMPOSITE", "PG_NS_PREFIX", "PG_NS_TRGM", "PG_NS_AGG", "PG_NS_SUBQ", "PG_NS_UNIQUE", "PG_NS_RGIST",
            "PG_NS_JOIN", "PG_NS_SEMIJOIN", "PG_IDXDEF_CREATE", "PG_IDXDEF_DROP", "PG_NS_ORD_COMPOSITE",
            "PG_NS_ORD_UNIQUE", "PG_NS_GROUPBY", "PG_NS_DISTINCT", "PG_NS_WINDOW", "PG_NS_INCRSORT", "PG_NS_MERGEJOIN",
            "PG_NS_IOPAYLOAD", "PG_NS_KNN", "PG_NS_ROWCMP", "PG_NS_GINCONT", "PG_NS_CAST",
            "PG_NS_TSV", "PG_NS_SPGIST", "PG_NS_MIXORD", "PG_NS_HETBITMAP", "PG_NS_NULLSORD", "PG_NS_TEXTORD",
            "PG_NS_MIXNULLS", "PG_NS_PARTPRUNE", "PG_NS_ANTIJOIN", "PG_NS_LATERAL", "PG_NS_MERGEAPPEND",
            "PG_NS_GROUPINGSETS", "PG_NS_TEXTBTREE", "PG_NS_MEMOIZE", "PG_NS_DISTINCTON", "PG_NS_SETOP",
            "PG_NS_NND", "PG_NS_MCGIN", "PG_NS_BRINMM", "PG_NS_COUNTIO",
            "PG_NS_EXPRORDER", "PG_NS_DMLSCAN", "PG_NS_BLOOM", "PG_NS_BTGISTKNN", "PG_NS_BTGIN"));
    static {
        if (COV_COUNT) {
            Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                System.out.println("=== GATE-PASS COVERAGE HISTOGRAM (mode-28 shapes) ===");
                long total = 0;
                for (java.util.concurrent.atomic.LongAdder a : COV_HIST.values()) {
                    total += a.sum();
                }
                COV_HIST.entrySet().stream()
                        .sorted((a, b) -> a.getKey().compareTo(b.getKey()))
                        .forEach(e -> System.out.println(String.format("  %-24s %d", e.getKey(), e.getValue().sum())));
                System.out.println("=== END COVERAGE HISTOGRAM (total " + total + ") ===");
                if (total >= COV_FLOOR) {
                    java.util.List<String> silent = new java.util.ArrayList<>();
                    for (String tag : EXPECTED_TAGS) {
                        java.util.concurrent.atomic.LongAdder a = COV_HIST.get(tag);
                        if (a == null || a.sum() == 0) {
                            silent.add(tag);
                        }
                    }
                    if (!silent.isEmpty()) {
                        java.util.Collections.sort(silent);
                        System.out.println("WARN (advisory): " + silent.size()
                                + " expected mode-28 shape-tag(s) never passed their gate in this run ("
                                + total + " total gate-passes): " + String.join(", ", silent));
                    }
                }
            }));
        }
    }

    private static void covBump(String mode) {
        if (COV_COUNT) {
            COV_HIST.computeIfAbsent(mode == null ? "<null>" : mode, k -> new java.util.concurrent.atomic.LongAdder()).increment();
        }
    }

    private static final double EPSILON = 1e-10;
    private static final double RELATIVE_TOLERANCE = 1e-6;

    // Depth budget is sampled in [min,max); earlystop is a leaf probability in percent.
    // deep.force bypasses the normal 50% chance of adding a deep predicate.
    private static final int DEEP_MIN = Integer.getInteger("idx.deep.min", 3);
    private static final int DEEP_MAX = Integer.getInteger("idx.deep.max", 6);
    private static final int DEEP_EARLYSTOP = Integer.getInteger("idx.deep.earlystop", 10);
    private static final boolean DEEP_FORCE = Integer.getInteger("idx.deep.force", 0) != 0;
    // Verification only: deliberately break arm equivalence to exercise mismatch detection.
    private static final boolean FAULT = Integer.getInteger("idx.faultinject", 0) != 0;
    // A nonnegative idx.only selects one shape for isolated verification; -1 uses the random mix.
    private static final int ONLY = Integer.getInteger("idx.only", -1);
    // Probe type/data boundaries with RHS constants shared by both arms; enabled by default.
    private static final boolean EDGE = Integer.getInteger("idx.edge", 1) != 0;
    private static final int EDGE_PCT = Integer.getInteger("idx.edge.pct", 28);
    // Experimental, off by default: identical multiset-preserving planner fences around both arms.
    // Only valid for unordered comparisons; never apply to an order-sensitive shape.
    // env.pct controls frequency; env.force bypasses the sampling decision.
    private static final boolean ENVELOPE = Integer.getInteger("idx.envelope", 0) != 0;
    private static final int ENVELOPE_PCT = Integer.getInteger("idx.env.pct", 35);
    private static final boolean ENVELOPE_FORCE = Integer.getInteger("idx.env.force", 0) != 0;
    // Optional plan-signature output file: TSV rows of ENV/BARE and sorted node-class counts.
    private static final String PLANSIG = System.getProperty("idx.plansig");
    private static final Object PLANSIG_LOCK = new Object();
    // Seed 12000 rows per idx_t table by default to make index and BRIN paths cost-competitive.
    // Batch inserts to stay under statement-size limits.
    private static final int SEED_BATCHES = Integer.getInteger("idx.seed.batches", 24);
    private static final int SEED_ROWS_PER_BATCH = Integer.getInteger("idx.seed.rows", 500);

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
        // Avoid broad "access method" / "does not support" patterns that could hide engine bugs.
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
        // Do not suppress "could not read block": it can indicate data/index corruption.
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
        ensureSufficientData();
        // Refresh only between checks; DML must never interleave the differential arms.
        maybePeriodicRefresh();
        try {
            checkIndexDifferential();
        } catch (NullPointerException e) {
            throw new IgnoreMeException();
        }
    }
    // ==================== Query Generation ====================

    /**
     * Generate an aggregate SELECT (COUNT, SUM, etc.) with complex WHERE.
     */
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

    /**
     * Generate a JOIN query between two tables with complex WHERE conditions.
     */
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

    /**
     * Generate a SELECT with ORDER BY to test index-based sorting.
     */
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

    /**
     * Generate index-friendly JOIN clauses: t0.c0 = t1.c0 AND t0.c1 > t1.c1
     * Uses simple column comparisons for better index utilization.
     */
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

    /**
     * Generate an index-friendly JOIN ON condition: t1.c0 = t2.c0 [AND t1.c1 > t2.c1]
     */
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

    /**
     * Generate JOIN clauses — same pattern as PostgresTLPBase.
     */
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

    /**
     * Create a subquery — same pattern as PostgresTLPBase.createSubquery.
     */
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

    /**
     * Ensure at least one index exists on the tables in the query,
     * using SQLancer's built-in PostgresIndexGenerator.
     */
    private void ensureIndexesExist(PostgresSelect select) {
        try {
            // Create 1-2 indexes using SQLancer's index generator
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
                    analyzeTolerant(table.getName());
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

    // Timeout-tolerant ANALYZE. ANALYZE is statistics maintenance only (it never affects the value-identity
    // of the differential arms), but it is a non-trivial statement that can legitimately hit the per-statement
    // timeout under heavy concurrent load. A bare "ANALYZE t" with no ExpectedErrors would raise a
    // thread-killing AssertionError on that cancellation; routing every ANALYZE through here tolerates the
    // timeout (and user-request cancellation / in-flight-drop races) as a self-skip instead. Same precedent as
    // the shared expectedErrors and reindexErrors sets.
    private void analyzeTolerant(String tbl) throws Exception {
        // C1: within one data epoch the heap is frozen, so a repeat ANALYZE recomputes identical statistics —
        // a no-op for the planner. Skip it if this table was already ANALYZEd this epoch (Set.add returns false
        // when the element is already present). doDmlChurn() clears the set when it mutates data.
        if (!analyzedThisEpoch.add(tbl)) {
            return;
        }
        ExpectedErrors azErrors = new ExpectedErrors();
        azErrors.add("canceling statement due to statement timeout");
        azErrors.add("canceling statement due to user request");
        azErrors.add("deadlock detected");
        azErrors.add("relation .* does not exist");
        azErrors.add("could not open relation");
        globalState.executeStatement(new SQLQueryAdapter("ANALYZE " + tbl + ";", azErrors, true));
    }

    // C1 companion: a NON-skipping ANALYZE for the rare shape that just built a FRESH index this check
    // (cases 23/24 defidx/defuniq) and wants a refresh even though the table was already ANALYZEd this epoch.
    // A freshly-built plain btree already gets accurate relpages/reltuples from the build itself, so this is
    // defensive insurance (keeps those create-then-gate shapes provably unaffected by the C1 skip). It drops
    // the epoch mark then re-runs, so the table is re-marked and later same-epoch calls still skip.
    private void analyzeTolerantForce(String tbl) throws Exception {
        analyzedThisEpoch.remove(tbl);
        analyzeTolerant(tbl);
    }

    private List<String> executeQuery(String queryString) throws Exception {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(queryString, errors, globalState, " ||| ");
        } catch (IgnoreMeException e) {
            return null;
        }
    }


    /** Sorted comparison — for un-ordered result sets (no ORDER BY).
     *  If query has LIMIT without ORDER BY, results are non-deterministic,
     *  so we use relaxed multi-set containment check.
     *  Also handles inheritance syntax (table*) and cross joins which cause
     *  non-deterministic results across different scan methods. */
    private void compareResultsSorted(List<String> r1, List<String> r2, String queryString, String mode) throws Exception {
        covBump(mode);
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

    /**
     * Exact multiset comparison for value-identity arms. Wrappers preserve type and bytes,
     * so numeric tolerances and other heuristic filters would hide genuine mismatches.
     */
    private void compareValueIdentityStrict(List<String> r1, List<String> r2, String queryString, String mode)
            throws Exception {
        covBump(mode);
        lastCompareFiltered = false; // never filtered on the value-identity path
        if (r1.equals(r2)) {
            return; // identical rows in identical order
        }
        List<String> sorted1 = new ArrayList<>(r1);
        List<String> sorted2 = new ArrayList<>(r2);
        java.util.Comparator<String> nullSafe = (a, b) -> {
            if (a == null && b == null) {
                return 0;
            }
            if (a == null) {
                return -1;
            }
            if (b == null) {
                return 1;
            }
            return a.compareTo(b);
        };
        sorted1.sort(nullSafe);
        sorted2.sort(nullSafe);
        if (sorted1.equals(sorted2)) {
            return; // same multiset (differ only in physical row order: index scan vs seq scan)
        }
        // Genuine divergence. Emit the harness diagnostic (throws on size/set difference) ...
        List<String> combinedString = new ArrayList<>();
        combinedString.add("-- [" + mode + "] (value-identity strict) Query: " + queryString);
        ComparatorHelper.assumeResultSetsAreEqual(sorted1, sorted2, queryString, combinedString, globalState);
        // ... and if it returned (equal size + equal distinct set, but a multiplicity-only mismatch that the
        // HashSet-based helper cannot see), the multiset still differs — report it rather than swallow it.
        throw new AssertionError("[" + mode + "] value-identity multiset mismatch (multiplicity): " + queryString);
    }

    /** Strict comparison — order matters (for ORDER BY queries).
     *  Improved: LIMIT + ORDER BY with unique tie-breaker now gets strict comparison.
     *  Also handles inheritance syntax (table*) which causes non-deterministic results
     *  across different scan methods, and cross joins which create duplicate sort keys. */

    /** Column delimiter used by executeQuery via getResultSetAllColumnsAsString. */
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

    /**
     * P1: Create 1-2 dedicated index-friendly tables with:
     *   - 8-10 columns (INT + TEXT dominant, for wide index coverage)
     *   - NOT NULL constraints (avoids NULL cardinality issues)
     *   - Pre-built indexes: single-column B-tree, composite, covering, partial, expression
     *
     * These tables supplement SQLancer's randomly-generated tables, ensuring
     * the optimizer always has rich index structures to choose from.
     * Only creates tables that don't already exist.
     */
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

        // Create 1-2 index-friendly tables. Biased toward 2 (fromOptions(1,2,2)) so the cross-table
        // EXISTS semijoin shape (checkSemiJoinIndexRewrite, case 22) has two distinct idx_t tables to
        // join most of the time; pure data-diversity, both differential arms read the same snapshot.
        int numTables = Randomly.fromOptions(1, 2, 2);
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
                createSQL.append("c7 TEXT COLLATE \"C\" NOT NULL, "); // C collation → collation-aware btree comparison path
                // cb: physically-ordered column for BRIN. GENERATED ALWAYS AS IDENTITY auto-assigns in
                // insertion order → values monotonically increase with heap position → correlation ~1,
                // which is what makes a BRIN index selective (see idx_N_cbbrin below). NEVER inserted
                // explicitly (excluded from every seed/churn column list), so it is never NULL.
                createSQL.append("cb INT GENERATED ALWAYS AS IDENTITY");
                // gj / ga: dedicated GIN targets. Per-row random DEFAULTs give a ~1% selective key space
                // so `gj @> '{"k":N}'` / `ga @> ARRAY[N]` are index-worthy; both are OMITTED from every
                // seed/churn column list (excluded like cb), so PG fills the DEFAULT on every inserted row
                // (a churn-inserted row that somehow bypassed the default would get NULL, which @> treats
                // as 3VL-false in BOTH arms → still sound). SQLancer models these as TEXT (see
                // PostgresSchema.getColumnType) but the GIN shapes address them by name via the catalog.
                // gj carries TWO keys: "k" (0..99, served by jsonb_path_ops/@? in case 19) AND a per-row
                // "g<0..99>":true key. The second key is what revives case 16: the key-existence operator
                // `gj ? 'gN'` is jsonb_ops-EXCLUSIVE (jsonb_path_ops cannot serve `?`), so it is forced onto
                // the jsonb_ops idx_<n>_gjgin index that case 19's jsonb_path_ops index otherwise cannibalizes
                // for @>. ~1% selective; additive (key "k" unchanged → case 19 unaffected).
                createSQL.append(", gj JSONB DEFAULT jsonb_build_object('k', (floor(random()*100))::int, 'g' || (floor(random()*100))::int::text, true)");
                createSQL.append(", ga INT[] DEFAULT ARRAY[(floor(random()*100))::int, (floor(random()*100))::int]");
                // gp: dedicated GiST 2-D target. Integer-valued coords (0..999) are exact float8, so the
                // value-identity wrapper point(gp[0], gp[1]) ≡ gp holds bit-exactly (no float fuzz).
                // Handled exactly like gj/ga: OMITTED from every seed/churn column list so PG fills the
                // DEFAULT; SQLancer models it as TEXT (PostgresSchema.getColumnType "point"), and
                // checkGistPointRewrite addresses it by name via the catalog.
                createSQL.append(", gp POINT DEFAULT point((floor(random()*1000))::float8, (floor(random()*1000))::float8)");
                // cu: dedicated BRIN-bloom target. UNCORRELATED, moderate-cardinality (~4000 distinct over
                // 12000 rows → ~3 rows/value) and — critically — it gets ONLY a bloom BRIN index (idx_<t>_cubloom
                // below), NO btree. Equality `cu = v` therefore has no btree to ride and the planner must choose
                // the bloom BRIN (Bitmap Index Scan) vs a Seq Scan, which is the only way to actually exercise the
                // bloom opclass (the correlated/monotonic cb always out-costs bloom with plain minmax, so case 21
                // was gate-starved). OMITTED from every seed/churn column list like cb/gj/ga/gp (DEFAULT-filled);
                // modeled as plain INT by PostgresSchema, addressed by name via the catalog. Excluded from
                // wrappableColumns so generic shapes never build a competing btree on it.
                createSQL.append(", cu INT DEFAULT (floor(random()*4000))::int");
                // cm: dedicated BRIN minmax_multi target (PG14+ int4_minmax_multi_ops). Like cu, UNCORRELATED,
                // moderate-cardinality (~4000 distinct over 12000 rows) and gets ONLY a minmax_multi BRIN index
                // (idx_<t>_cmm below), NO btree — so `cm = v` / `cm BETWEEN` has no btree to ride and the planner
                // must choose the minmax_multi BRIN (Bitmap Index Scan) vs a Seq Scan. This is the only shape that
                // exercises the minmax_multi opclass (the plain-minmax cbbrin only summarizes a single [min,max]
                // per range; minmax_multi keeps up to 32 sub-ranges per block range, so for an UNCORRELATED column
                // it prunes where plain minmax cannot — a distinct build + consistent code path). OMITTED from every
                // seed/churn column list like cb/gj/ga/gp/cu/rng (DEFAULT-filled); modeled as plain INT by
                // PostgresSchema, addressed by name via the catalog. Excluded from wrappableColumns so generic
                // shapes never build a competing btree on it (which would let the planner avoid the BRIN).
                createSQL.append(", cm INT DEFAULT (floor(random()*4000))::int");
                // rng: int4range DEFAULT target that revives the range-GiST shape (case 14 checkRangeGistRewrite),
                // which self-builds nsrg_<t>_rng and was gate-starved only because no seed table had a RANGE column.
                // getColumnType already maps "int4range" → PostgresDataType.RANGE (no PostgresSchema change). Like
                // gp/gj/ga it is DEFAULT-filled and excluded from the generic insert/wrap paths (RANGE is not btree-
                // wrappable). The DEFAULT uses TWO disjoint ordered sub-ranges — lower∈[0,399], upper∈[500,899] — so
                // lower<upper ALWAYS holds despite the two independent random() evaluations (a naive int4range(r1,r2)
                // would throw "lower bound must be <= upper bound" whenever r1>r2).
                createSQL.append(", rng INT4RANGE DEFAULT int4range((floor(random()*400))::int, (floor(random()*400))::int + 500)");
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
                    // BRIN on the physically-ordered cb column. pages_per_range=1 is REQUIRED: the idx
                    // tables are ~85 pages, so the default 128-pages-per-range would still summarize the
                    // whole table as a single block range (BRIN prunes nothing → planner picks Seq Scan).
                    // With pages_per_range=1 each page is its own range → range predicates on cb become
                    // BRIN-selective (verified: Bitmap Index Scan on this index). This is the ONLY shape
                    // family that exercises BRIN — random-valued columns never get a BRIN plan.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_cbbrin ON " + tableName + " USING brin(cb) WITH (pages_per_range=1);",
                    // GIN on the jsonb column (jsonb_ops: supports @>, ?, ?|, ?&). Exercised by
                    // checkGinJsonbRewrite via a selective `gj @> '{"k":N}'` containment predicate.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_gjgin ON " + tableName + " USING gin(gj);",
                    // GIN on the int[] column (array_ops: supports &&, @>, <@, =). Exercised by
                    // checkGinArrayRewrite via a selective `ga @> ARRAY[N]` element-containment predicate.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_gagin ON " + tableName + " USING gin(ga);",
                    // Multicolumn GIN over BOTH container columns (ga int[] + gj jsonb). A single multi-key GIN
                    // index can serve a conjunction of containment predicates (ga @> ARRAY[n] AND gj @> '{...}')
                    // in one Bitmap Index Scan (ANDed within the index), a code path the two single-key GINs
                    // (gagin/gjgin) never exercise — exercised by checkMultiColGinRewrite (case 59).
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_mcgin ON " + tableName + " USING gin(ga, gj);",
                    // GiST on the point column (point_ops: supports <@, @>, ~=, <->). Exercised by
                    // checkGistPointRewrite via a selective `gp <@ box '...'` containment predicate.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_gpgist ON " + tableName + " USING gist(gp);",
                    // BRIN-bloom on the uncorrelated cu column (int4_bloom_ops: equality-only). The SOLE index on
                    // cu, so `cu = v` is forced onto this bloom BRIN (Bitmap Index Scan) vs Seq Scan — exercised by
                    // checkBrinBloomRewrite (case 21). pages_per_range=1 for the same ~85-page reason as cbbrin.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_cubloom ON " + tableName + " USING brin(cu int4_bloom_ops) WITH (pages_per_range=1);",
                    // BRIN minmax_multi (PG14+) on the uncorrelated cm column (int4_minmax_multi_ops). The SOLE index
                    // on cm, so `cm = v` / `cm BETWEEN` is forced onto this minmax_multi BRIN (Bitmap Index Scan) vs
                    // Seq Scan — exercised by checkBrinMinmaxMultiRewrite (case 60). pages_per_range=1 for the same
                    // ~85-page reason as cbbrin/cubloom. minmax_multi keeps multiple sub-ranges per block range, so
                    // it prunes an uncorrelated column where the plain-minmax cbbrin cannot.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_cmm ON " + tableName + " USING brin(cm int4_minmax_multi_ops) WITH (pages_per_range=1);",
                    // SP-GiST on c7 (text, COLLATE \"C\"): the SOLE index on c7, so `c7 = v` / prefix is forced
                    // onto SP-GiST (Index Cond) vs Seq Scan — exercised by checkSpGistTextRewrite (case 44).
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c7spgist ON " + tableName + " USING spgist(c7);",
                    // Mixed ASC/DESC composite btree LED by the heavily-duplicated c4 (~70% of rows fall in
                    // [-8,8], ~500 rows per hot value): supplies the (c4 ASC, c0 DESC) ordering with NO Sort —
                    // exercised by checkMixedOrderRewrite (case 45). The dup-heavy LEAD is deliberate: with a
                    // near-unique lead (the old c0) each lead group held ~1 row, so a direction flip on the
                    // SECOND key was invisible in the top-k (FAULT inert). Leading with c4 makes the top-k land
                    // entirely inside one c4 group, so the 2nd-key (c0) direction fully determines it. cb is the
                    // unique IDENTITY final tiebreak so the projected (c4,c0,cb) ORDER BY is a TOTAL order
                    // (positional comparison is permutation-free). NEW NAME (mixord2) so long-lived DBs that
                    // already carry the old mixord rebuild cleanly under CREATE INDEX IF NOT EXISTS.
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_mixord2 ON " + tableName + " (c4 ASC, c0 DESC, cb ASC);",
                    // DESC-with-NULLS-LAST btree on the ~85%-NULL c2 column: the SOLE index on c2, so an ordered
                    // scan `ORDER BY c2 DESC NULLS LAST` is forced onto it with NO Sort node — exercised by
                    // checkNullsOrderRewrite (case 47). This is the only coverage of index-provided NULLS placement
                    // (idx_<t>_c0desc is on NOT-NULL c0, so NULL ordering is otherwise untested).
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c2nulls ON " + tableName + " (c2 DESC NULLS LAST);",
                    // Plain btree on the COLLATE "C" text column c7 (whose ONLY other index is SP-GiST, which gives
                    // no ordered scan). Supplies an index-provided TEXT ordering with NO Sort — exercised by
                    // checkTextOrderCollateRewrite (case 48). c7 is COLLATE "C", so this is a deterministic byte-order
                    // btree (immune to the ICU/locale collation nondeterminism that bit the amcheck path), which makes
                    // the ORDER-sensitive differential sound. This is the only coverage of index-provided TEXT order
                    // (case 1 deferred TEXT because its generic wrapper has no COLLATE-aware form).
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_c7btree ON " + tableName + " (c7);",
                    // Composite mixed-direction btree LED by a NULLABLE key carrying explicit NULLS placement:
                    // (c2 DESC NULLS LAST, c0 DESC, cb ASC). c2 is ~65-85% NULL (so NULLS placement on the LEAD key
                    // dominates the top-k — a NULLS flip reliably migrates the whole NULL block in/out of the window,
                    // unlike a nullable key buried behind the near-unique c0), c0 DESC supplies the mixed direction,
                    // cb is the unique IDENTITY final tiebreak so the projected (c2,c0,cb) ORDER BY is a TOTAL order.
                    // Supplies the only coverage of index-provided ordering that COMBINES mixed direction AND NULLS
                    // placement on a nullable LEAD key — exercised by checkCompositeNullsOrderRewrite (case 49).
                    // (idx_<t>_mixord has no nullable key; idx_<t>_c2nulls is single-column — neither covers the combo.)
                    "CREATE INDEX IF NOT EXISTS idx_" + t + "_mixnulls ON " + tableName + " (c2 DESC NULLS LAST, c0 DESC, cb ASC);",
                };

                for (String idxSQL : indexStmts) {
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(idxSQL, tableErrors, true));
                    } catch (Exception e) { }
                }

                // Insert initial data — large enough (~12000 rows, ~170+ heap pages) that BRIN
                // page-skipping on the correlated cb column is cost-competitive vs a Seq Scan, and the
                // Lever-3 upper-operator shapes get GroupAggregate / Index-Only / skip-scan input plans. At
                // the old 200-row (~7-page) size the planner almost never chose BRIN (measured: 1 gate-pass
                // per ~13.5k queries), because skipping pages of a 7-page table saves nothing.
                ExpectedErrors insertErrors = new ExpectedErrors();
                insertErrors.add("violates not-null constraint");
                insertErrors.add("integer out of range");
                insertErrors.add("duplicate key value");
                insertErrors.add("invalid input syntax");
                insertErrors.add("division by zero");
                // A seed batch hitting the per-statement timeout (common only under heavy concurrent load — e.g.
                // a second JVM sharing the box) must self-skip (the table simply gets fewer rows that batch),
                // NOT escalate. executeStatement raises an AssertionError (an Error, not an Exception) when the
                // actual error is unexpected, which the catch(Exception) below cannot swallow → the thread would
                // die mid-seed. Listing the timeout/cancellation as expected makes the batch a tolerated no-op.
                insertErrors.add("canceling statement due to statement timeout");
                insertErrors.add("canceling statement due to user request");
                Randomly r = globalState.getRandomly();
                for (int batch = 0; batch < SEED_BATCHES; batch++) {
                    StringBuilder insertSQL = new StringBuilder();
                    // Explicit column list (cb omitted → GENERATED ALWAYS AS IDENTITY auto-fills in
                    // insertion order, preserving physical correlation for the BRIN index).
                    insertSQL.append("INSERT INTO ").append(tableName).append(" (c0,c1,c2,c3,c4,c5,c6,c7) VALUES ");
                    for (int row = 0; row < SEED_ROWS_PER_BATCH; row++) {
                        if (row > 0) insertSQL.append(", ");
                        insertSQL.append("(");
                        // c0, c1: uniform (anchor the prebuilt composite/partial/expr index selectivity)
                        insertSQL.append(r.getInteger(-32768, 32767)).append(", ");  // c0
                        insertSQL.append(r.getInteger(-32768, 32767)).append(", ");  // c1
                        // c2: high NULL density (~85%) → mostly-NULL index storage + checkNullIndexRewrite
                        insertSQL.append(r.getInteger(0, 100) < 85 ? "NULL" : String.valueOf(r.getInteger(-32768, 32767))).append(", ");  // c2
                        // c3: hotspot skew (~80% from a small hot set) → heavy duplicate keys (btree dedup / hash buckets)
                        insertSQL.append(skewHotspot(r)).append(", ");  // c3
                        // c4: small-magnitude concentration (~70% in [-8,8]) → heavy duplicate keys
                        insertSQL.append(skewSmallMagnitude(r)).append(", ");  // c4
                        insertSQL.append("'").append(sanitizeStringLiteral(r.getString())).append("', ");  // c5
                        insertSQL.append(Randomly.getBoolean() ? "'" + sanitizeStringLiteral(r.getString()) + "'" : "NULL").append(", ");  // c6
                        // c7: ~10% TOAST-scale wide text (mixed-alphabet defeats compression; ≤2000B < btree ~2704B limit)
                        insertSQL.append("'").append(sanitizeStringLiteral(r.getInteger(0, 100) < 10 ? wideText(r) : r.getString())).append("'");  // c7
                        insertSQL.append(")");
                    }
                    insertSQL.append(" ON CONFLICT DO NOTHING;");
                    try {
                        globalState.executeStatement(new SQLQueryAdapter(insertSQL.toString(), insertErrors, true));
                    } catch (Exception e) { }
                }

                // VACUUM (ANALYZE): refresh stats AND set the visibility map all-visible so Index-Only Scans
                // become viable. Required for the Lever-3 upper-node shapes (checkGroupByIndexRewrite /
                // checkDistinctIndexRewrite): their armA must take index-ORDERED input (GroupAggregate / Unique
                // over an Index-Only Scan, no Sort). With only ANALYZE the visibility map stays unset
                // (relallvisible≈0), so DISTINCT/GROUP BY fall back to Seq Scan + Sort and the armA "no Sort"
                // gate never passes. VACUUM is a physical-state maintenance op (not a planner GUC) → axis stays
                // orthogonal.
                //
                // VACUUM must run OUTSIDE a transaction block, but SQLancer executes statements inside one, so
                // the old executeStatement("VACUUM ...") path threw and silently degraded to ANALYZE — leaving
                // the VM unset and starving cases 29/30 of nearly all their yield. Run VACUUM on the RAW JDBC
                // connection with autocommit forced on (which first commits the just-inserted seed rows — exactly
                // what lets VACUUM mark their pages all-visible), bypassing SQLancer's transaction wrapper, then
                // restore the prior autocommit mode. Fall back to plain ANALYZE only if even this path fails.
                try (Statement vst = globalState.getConnection().createStatement()) {
                    java.sql.Connection rawCon = vst.getConnection();
                    boolean prevAutoCommit = rawCon.getAutoCommit();
                    if (!prevAutoCommit) {
                        rawCon.setAutoCommit(true);
                    }
                    try {
                        vst.execute("VACUUM (ANALYZE) " + tableName);
                    } finally {
                        if (!prevAutoCommit) {
                            rawCon.setAutoCommit(prevAutoCommit);
                        }
                    }
                } catch (Exception ve) {
                    try {
                        analyzeTolerant(tableName);
                    } catch (Exception ae) {
                        // last-resort: leave stats as-is
                    }
                }
            } catch (Exception e) {
                // Table/index creation may fail, ignore
            }
        }

        // === ITEM B: RANGE-partitioned table with a PROPAGATED (local) index on a NON-partition-key
        // column (c0), for the partition-pruning + local-index differential (case 33). Created ONCE
        // alongside the idx_t tables (same once-only guard above). Child ranges are GAP-FREE over the
        // ENTIRE int domain (MINVALUE..0, 0..1000000, 1000000..MAXVALUE), so EVERY seeded pk routes to
        // exactly one partition — the parent-routed seed can NEVER raise "violates partition constraint".
        // idx_pt and its children idx_pt_p* are addressed ONLY by name (case 33 / pickPartitionedTable);
        // the generic seed/churn/reindex loops skip "idx_pt*" so no generic INSERT ever targets a child
        // with an out-of-range pk (which would be an unexpected error → thread death). Thus idx_pt's data
        // is 100% controlled here. Bonus surface — wrapped so its setup can never kill table creation.
        try {
            boolean hasPt = false;
            for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
                if ("idx_pt".equals(t.getName())) { hasPt = true; break; }
            }
            if (!hasPt) {
                ExpectedErrors ptErrors = new ExpectedErrors();
                ptErrors.add("already exists");
                ptErrors.add("relation .* already exists");
                ptErrors.add("violates partition constraint");
                ptErrors.add("no partition of relation");
                ptErrors.add("integer out of range");
                ptErrors.add("duplicate key value");
                ptErrors.add("invalid input syntax");
                ptErrors.add("cannot create index on relation");
                String[] ptDdl = {
                    "CREATE TABLE IF NOT EXISTS idx_pt (pk INT NOT NULL, c0 INT NOT NULL, c1 INT) PARTITION BY RANGE (pk);",
                    "CREATE TABLE IF NOT EXISTS idx_pt_p0 PARTITION OF idx_pt FOR VALUES FROM (MINVALUE) TO (0);",
                    "CREATE TABLE IF NOT EXISTS idx_pt_p1 PARTITION OF idx_pt FOR VALUES FROM (0) TO (1000000);",
                    "CREATE TABLE IF NOT EXISTS idx_pt_p2 PARTITION OF idx_pt FOR VALUES FROM (1000000) TO (MAXVALUE);",
                    // Propagated (local) index on the NON-partition-key column c0: PG creates a matching
                    // child index on every partition; the planner uses the per-partition index after pruning.
                    "CREATE INDEX IF NOT EXISTS idx_pt_c0 ON idx_pt (c0);",
                };
                for (String s : ptDdl) {
                    try { globalState.executeStatement(new SQLQueryAdapter(s, ptErrors, true)); } catch (Throwable t) { }
                }
                // Seed through the PARENT (routes to children). pk drawn from 3 well-separated centers
                // (one per partition) so each partition receives ~1/3 of the rows (~4000 each → index-worthy
                // within a single pruned partition). c0 in [0,2000) → a sampled c0=V matches a handful of
                // rows (selective → the planner prefers the local c0 index over a seq scan). c1 random.
                Randomly r = globalState.getRandomly();
                int[] pkCenters = { -500, 500, 2_000_000 }; // land firmly inside p0 / p1 / p2 respectively
                for (int batch = 0; batch < 24; batch++) {
                    StringBuilder sb = new StringBuilder();
                    sb.append("INSERT INTO idx_pt (pk, c0, c1) VALUES ");
                    for (int row = 0; row < 500; row++) {
                        if (row > 0) sb.append(", ");
                        int pk = pkCenters[(int) Randomly.getNotCachedInteger(0, pkCenters.length)]
                                + (int) Randomly.getNotCachedInteger(-400, 401); // ±400, hi exclusive → [-400,400]
                        sb.append("(").append(pk).append(", ")
                          .append(r.getInteger(0, 2000)).append(", ")
                          .append(r.getInteger(-32768, 32767)).append(")");
                    }
                    sb.append(";");
                    try { globalState.executeStatement(new SQLQueryAdapter(sb.toString(), ptErrors, true)); } catch (Throwable t) { }
                }
                // VACUUM (ANALYZE) on the raw autocommit connection (same rationale as the idx_t path:
                // commit the seed + set the visibility map so per-partition Index-Only / Index scans are viable).
                try (Statement vst = globalState.getConnection().createStatement()) {
                    java.sql.Connection rawCon = vst.getConnection();
                    boolean prevAutoCommit = rawCon.getAutoCommit();
                    if (!prevAutoCommit) rawCon.setAutoCommit(true);
                    try { vst.execute("VACUUM (ANALYZE) idx_pt"); }
                    finally { if (!prevAutoCommit) rawCon.setAutoCommit(prevAutoCommit); }
                } catch (Exception ve) {
                    try { analyzeTolerant("idx_pt"); } catch (Exception ae) { }
                }
            }
            // LIST- and HASH-partitioned siblings of idx_pt (case 61 checkListHashPartitionPruneRewrite). RANGE
            // (idx_pt above) is the only partition strategy covered before this; LIST and HASH prune through
            // distinct planner code (list-value membership / hash-modulus static pruning). Both names begin
            // "idx_pt" so the existing startsWith("idx_pt") guards auto-skip them in every generic DML/pick loop.
            boolean hasPtl = false;
            boolean hasPth = false;
            for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
                if ("idx_ptl".equals(t.getName())) hasPtl = true;
                if ("idx_pth".equals(t.getName())) hasPth = true;
            }
            if (!hasPtl || !hasPth) {
                ExpectedErrors lhErrors = new ExpectedErrors();
                lhErrors.add("already exists");
                lhErrors.add("relation .* already exists");
                lhErrors.add("violates partition constraint");
                lhErrors.add("no partition of relation");
                lhErrors.add("integer out of range");
                lhErrors.add("duplicate key value");
                lhErrors.add("invalid input syntax");
                lhErrors.add("cannot create index on relation");
                Randomly r = globalState.getRandomly();
                if (!hasPtl) {
                    // LIST(pk): three explicit value-list partitions over pk ∈ {1..9} + a DEFAULT catch-all.
                    String[] lDdl = {
                        "CREATE TABLE IF NOT EXISTS idx_ptl (pk INT NOT NULL, c0 INT NOT NULL, c1 INT) PARTITION BY LIST (pk);",
                        "CREATE TABLE IF NOT EXISTS idx_ptl_p0 PARTITION OF idx_ptl FOR VALUES IN (1, 2, 3);",
                        "CREATE TABLE IF NOT EXISTS idx_ptl_p1 PARTITION OF idx_ptl FOR VALUES IN (4, 5, 6);",
                        "CREATE TABLE IF NOT EXISTS idx_ptl_p2 PARTITION OF idx_ptl FOR VALUES IN (7, 8, 9);",
                        "CREATE TABLE IF NOT EXISTS idx_ptl_pdef PARTITION OF idx_ptl DEFAULT;",
                        "CREATE INDEX IF NOT EXISTS idx_ptl_c0 ON idx_ptl (c0);",
                    };
                    for (String s : lDdl) {
                        try { globalState.executeStatement(new SQLQueryAdapter(s, lhErrors, true)); } catch (Throwable t) { }
                    }
                    // Seed through the PARENT. pk ∈ {1..9} (90%) lands in p0/p1/p2; pk ∈ {10..15} (10%) routes to
                    // DEFAULT. c0 ∈ [0,2000) → a sampled c0=V is selective (planner prefers the local c0 index).
                    for (int batch = 0; batch < 24; batch++) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("INSERT INTO idx_ptl (pk, c0, c1) VALUES ");
                        for (int row = 0; row < 500; row++) {
                            if (row > 0) sb.append(", ");
                            int pk = (Randomly.getNotCachedInteger(0, 100) < 90)
                                    ? (int) Randomly.getNotCachedInteger(1, 10)   // [1,9]
                                    : (int) Randomly.getNotCachedInteger(10, 16); // [10,15] → DEFAULT
                            sb.append("(").append(pk).append(", ")
                              .append(r.getInteger(0, 2000)).append(", ")
                              .append(r.getInteger(-32768, 32767)).append(")");
                        }
                        sb.append(";");
                        try { globalState.executeStatement(new SQLQueryAdapter(sb.toString(), lhErrors, true)); } catch (Throwable t) { }
                    }
                    try (Statement vst = globalState.getConnection().createStatement()) {
                        java.sql.Connection rawCon = vst.getConnection();
                        boolean prevAutoCommit = rawCon.getAutoCommit();
                        if (!prevAutoCommit) rawCon.setAutoCommit(true);
                        try { vst.execute("VACUUM (ANALYZE) idx_ptl"); }
                        finally { if (!prevAutoCommit) rawCon.setAutoCommit(prevAutoCommit); }
                    } catch (Exception ve) {
                        try { analyzeTolerant("idx_ptl"); } catch (Exception ae) { }
                    }
                }
                if (!hasPth) {
                    // HASH(pk) MODULUS 4: equality `pk = V` prunes statically to exactly one of the 4 partitions.
                    String[] hDdl = {
                        "CREATE TABLE IF NOT EXISTS idx_pth (pk INT NOT NULL, c0 INT NOT NULL, c1 INT) PARTITION BY HASH (pk);",
                        "CREATE TABLE IF NOT EXISTS idx_pth_p0 PARTITION OF idx_pth FOR VALUES WITH (MODULUS 4, REMAINDER 0);",
                        "CREATE TABLE IF NOT EXISTS idx_pth_p1 PARTITION OF idx_pth FOR VALUES WITH (MODULUS 4, REMAINDER 1);",
                        "CREATE TABLE IF NOT EXISTS idx_pth_p2 PARTITION OF idx_pth FOR VALUES WITH (MODULUS 4, REMAINDER 2);",
                        "CREATE TABLE IF NOT EXISTS idx_pth_p3 PARTITION OF idx_pth FOR VALUES WITH (MODULUS 4, REMAINDER 3);",
                        "CREATE INDEX IF NOT EXISTS idx_pth_c0 ON idx_pth (c0);",
                    };
                    for (String s : hDdl) {
                        try { globalState.executeStatement(new SQLQueryAdapter(s, lhErrors, true)); } catch (Throwable t) { }
                    }
                    // Seed through the PARENT. pk ∈ [0,40) over 12000 rows → ~300 rows per pk value, hash-spread
                    // across all 4 partitions (~3000 rows each). c0 ∈ [0,2000) selective as above.
                    for (int batch = 0; batch < 24; batch++) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("INSERT INTO idx_pth (pk, c0, c1) VALUES ");
                        for (int row = 0; row < 500; row++) {
                            if (row > 0) sb.append(", ");
                            sb.append("(").append((int) Randomly.getNotCachedInteger(0, 40)).append(", ")
                              .append(r.getInteger(0, 2000)).append(", ")
                              .append(r.getInteger(-32768, 32767)).append(")");
                        }
                        sb.append(";");
                        try { globalState.executeStatement(new SQLQueryAdapter(sb.toString(), lhErrors, true)); } catch (Throwable t) { }
                    }
                    try (Statement vst = globalState.getConnection().createStatement()) {
                        java.sql.Connection rawCon = vst.getConnection();
                        boolean prevAutoCommit = rawCon.getAutoCommit();
                        if (!prevAutoCommit) rawCon.setAutoCommit(true);
                        try { vst.execute("VACUUM (ANALYZE) idx_pth"); }
                        finally { if (!prevAutoCommit) rawCon.setAutoCommit(prevAutoCommit); }
                    } catch (Exception ve) {
                        try { analyzeTolerant("idx_pth"); } catch (Exception ae) { }
                    }
                }
            }
        } catch (Throwable t) {
            // idx_pt is a bonus surface; never let its setup kill table creation.
        }

        // === ITEM C: dedicated GROUPING SETS table (case 53) ===
        // The presorted-input path for GROUPING SETS (GroupAggregate over an Index-Only Scan, no Sort) is
        // the ONLY index axis case 53 can test, but the planner never chooses it for the shared idx_t tables:
        // (a) their ~12k rows are too few for the index path to out-cost Seq Scan + MixedAggregate(hash),
        // (b) the old ORDER BY in the shape forced a top-level Sort that the planner never elides through a
        // rollup GroupAggregate, and (c) the VM must be all-visible or the Index-Only Scan pays heap fetches
        // and loses on cost. Measured flip point on PG 18.6 (default costs, VACUUMed, ANALYZEd): ~25k rows at
        // ~800B/row; this table is 40k rows (60% margin) of UNIQUE c0 (worst case for hash agg → lowest flip
        // point) with an 800B filler (raises the Seq Scan cost; its CONTENT is irrelevant to the bug axis).
        // Excluded from every generic picker/populate/churn/reindex loop (see the idx_gs guards) to keep the
        // VM lit; addressed by name only from checkGroupingSetsRewrite.
        try {
            boolean hasGs = false;
            boolean hasGsHeap = false;
            for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
                if ("idx_gs".equals(t.getName())) hasGs = true;
                if ("idx_gs_heap".equals(t.getName())) hasGsHeap = true;
            }
            if (!hasGs || !hasGsHeap) {
                ExpectedErrors gsErrors = new ExpectedErrors();
                gsErrors.add("already exists");
                gsErrors.add("relation .* already exists");
                gsErrors.add("canceling statement due to statement timeout");
                gsErrors.add("canceling statement due to user request");
                // idx_gs: the arm-A table (c0 index; VM lit lazily by the shape). idx_gs_heap: the arm-B
                // GROUND-TRUTH twin — byte-identical data, deliberately NO index. On a wide table with a
                // narrow covering index the planner prefers a full Index-Only Scan for the wrapped arm too
                // (measured: even greatest(c0,c0) rode idx_gs_c0 as the cheapest full scan), so armB can
                // never be index-independent on idx_gs itself; an index-less twin makes armB a pure Seq
                // Scan by construction. Both carry the idx_gs prefix → every generic picker/populate/
                // churn/reindex guard excludes them, so the twins stay byte-identical forever.
                globalState.executeStatement(new SQLQueryAdapter(
                        "CREATE TABLE IF NOT EXISTS idx_gs (c0 INT NOT NULL, filler TEXT DEFAULT repeat('w', 800));",
                        gsErrors, true));
                globalState.executeStatement(new SQLQueryAdapter(
                        "CREATE INDEX IF NOT EXISTS idx_gs_c0 ON idx_gs (c0);", gsErrors, true));
                globalState.executeStatement(new SQLQueryAdapter(
                        "CREATE TABLE IF NOT EXISTS idx_gs_heap (LIKE idx_gs INCLUDING DEFAULTS);", gsErrors, true));
                // TRUNCATE-then-seed keeps the block idempotent after a mid-setup crash (partial twin state).
                globalState.executeStatement(new SQLQueryAdapter("TRUNCATE idx_gs, idx_gs_heap;", gsErrors, true));
                // One-shot generate_series seed, IDENTICAL for both twins (unique c0 on purpose — see ITEM C header).
                globalState.executeStatement(new SQLQueryAdapter(
                        "INSERT INTO idx_gs (c0) SELECT g FROM generate_series(1, 40000) g;", gsErrors, true));
                globalState.executeStatement(new SQLQueryAdapter(
                        "INSERT INTO idx_gs_heap (c0) SELECT g FROM generate_series(1, 40000) g;", gsErrors, true));
                // NO immediate VACUUM here: this connection just inserted the seed rows, so a same-session
                // VACUUM runs before RecentGlobalXmin advances past the seed INSERT's xid and leaves
                // relallvisible=0 (measured on PG 18.6) — the planner then keeps the hash path and the gate
                // can never pass. The shape self-heals lazily: by its first invocation the insert is long
                // committed, so its one VACUUM (see gsVacuum/gsRelallvisible in checkGroupingSetsRewrite)
                // lights the VM. ANALYZE alone is enough for now (stats; VM comes later).
                analyzeTolerant("idx_gs");
                analyzeTolerant("idx_gs_heap");
            }
        } catch (Throwable t) {
            // bonus surface; never let its setup kill table creation
        }
    }

    // Data-diversity seed helpers (Part A). These bias only the DATA both differential arms read from a
    // single snapshot; they cannot affect the armA==armB row-set equality, so they are soundness-free.

    /** c3: ~80% of values drawn from a small hot set → dense duplicate keys (btree dedup, hash buckets). */
    private int skewHotspot(Randomly r) {
        if (r.getInteger(0, 100) < 80) {
            int[] hot = { 0, 1, 2, 7, 42, 100, -1, 32767 };
            return hot[(int) Randomly.getNotCachedInteger(0, hot.length)];
        }
        return r.getInteger(-32768, 32767);
    }

    /** c4: ~70% of values concentrated in [-8, 8] → heavy duplicate keys on small magnitudes. */
    private int skewSmallMagnitude(Randomly r) {
        if (r.getInteger(0, 100) < 70) {
            return (int) Randomly.getNotCachedInteger(-8, 9); // [-8, 8] inclusive
        }
        return r.getInteger(-32768, 32767);
    }

    /** c7: a 1200–2000-char high-entropy string → row exceeds the ~2 KB TOAST threshold (detoast paths),
     *  yet stays under btree's ~2704-byte entry limit so ad-hoc btrees on c7 never error. */
    private String wideText(Randomly r) {
        int len = (int) Randomly.getNotCachedInteger(1200, 2001);
        String alpha = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        StringBuilder sb = new StringBuilder(len);
        for (int i = 0; i < len; i++) {
            sb.append(alpha.charAt((int) Randomly.getNotCachedInteger(0, alpha.length())));
        }
        return sb.toString();
    }


    /**
     * Populate tables with enough rows for the optimizer to consider indexes.
     * PostgreSQL won't use an index scan on a table with < ~20 rows.
     * Only runs once per oracle instance to avoid repeated inserts.
     */
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
                // ITEM B: idx_pt (parent + children idx_pt_p*) are seeded via the parent in
                // createIndexFriendlyTables with GAP-FREE pk routing. A generic INSERT into a child with a
                // random pk would violate its partition constraint (an unexpected error → thread death), so
                // keep idx_pt entirely out of the generic populate loop.
                if (table.getName().startsWith("idx_pt")) continue;
                // idx_gs is seeded once by ITEM C (unique c0 on purpose); generic INSERTs would dirty its
                // visibility map and starve case 53's index-ordered-input gate.
                if (table.getName().startsWith("idx_gs")) continue;
                try {
                    // Build INSERT with 50 rows at a time, repeated to reach ~1000 rows.
                    // Threshold measured empirically (EXPLAIN sweep on the idx-table shape): PostgreSQL
                    // only switches from Seq Scan to an index scan once a table crosses ~500 rows for the
                    // core b-tree families (eq/range/composite/expression/text/LIKE-prefix) and ~1000 for
                    // multi-value IN. Below that the whole table fits in ~1-2 pages and seq scan always
                    // wins, so armA never gets an Index Cond and every round is discarded at the gate.
                    // ~1000 is the evidence-based floor; bigger buys no extra plan coverage, only cost.
                    // One-time cost (guarded by dataPopulated); net-neutral churn then holds this size.
                    // Exclude generated columns — PostgreSQL does not allow inserting into them.
                    // Exclude SERIAL/IDENTITY columns (has nextval() default) — inserting explicit
                    // values triggers CHECK constraints with POWER/exponentiation causing
                    // underflow/overflow (e.g., CHECK(c0 = c0 * c0^c0) with c0=-23700).
                    List<PostgresColumn> insertableCols = table.getColumns().stream()
                            .filter(c -> !c.isGenerated())
                            .filter(c -> !c.hasSequenceDefault())
                            .filter(c -> !"cb".equals(c.getName())) // BRIN identity col — never insert explicitly
                            // gj/ga are GIN targets with per-row random DEFAULTs; SQLancer models them as
                            // TEXT (getColumnType), so a generic INSERT would push text into jsonb/int[] and
                            // fail the whole batch. Omit them so PG applies the selective DEFAULT instead.
                            .filter(c -> !"gj".equals(c.getName()) && !"ga".equals(c.getName()) && !"gp".equals(c.getName()))
                            .filter(c -> !"cu".equals(c.getName())) // bloom-only DEFAULT col — keep DEFAULT distribution
                            .filter(c -> !"cm".equals(c.getName())) // minmax_multi-only DEFAULT col — keep DEFAULT distribution
                            .filter(c -> !"rng".equals(c.getName())) // range-GiST DEFAULT col (not btree-insertable here)
                            .collect(Collectors.toList());
                    if (insertableCols.isEmpty()) continue;
                    for (int batch = 0; batch < 20; batch++) {
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
                // Analyze after inserts (via analyzeTolerant: tolerates timeout AND seeds the C1 epoch set so
                // the first window of shape ANALYZEs skip; a bare ANALYZE's AssertionError would also slip past
                // this catch(Exception), since AssertionError is an Error — analyzeTolerant's ExpectedErrors fix that)
                try {
                    analyzeTolerant(table.getName());
                } catch (Exception e) { }
            }
        } catch (Exception e) { }
    }

    // ==================== Periodic State Refresh ====================

    /**
     * Apply DML every 500 checks and REINDEX every 2000 to exercise stale-entry and rebuild paths.
     * Runs before the differential pair so both arms observe the same data.
     */
    private void maybePeriodicRefresh() {
        iterCount++;
        if (iterCount % 500 == 0) {
            doDmlChurn();
        }
        if (iterCount % 2000 == 0) {
            doReindex();
        }
    }

    /**
     * DML churn: INSERT a few rows, UPDATE a random subset, DELETE a smaller subset, then ANALYZE.
     * Net-positive row count (INSERT > DELETE) so tables keep growing rather than emptying. Uses
     * ctid-limited subselects to touch a bounded random subset without needing a primary key.
     * All statements are error-tolerant (ExpectedErrors + catch(Throwable)); a constraint violation
     * fails only its own statement and never kills the thread.
     */
    private void doDmlChurn() {
        // Data changes invalidate memoized ANALYZE results.
        analyzedThisEpoch.clear();
        ExpectedErrors churnErrors = new ExpectedErrors();
        churnErrors.add("violates not-null constraint");
        churnErrors.add("violates check constraint");
        churnErrors.add("violates unique constraint");
        churnErrors.add("violates foreign key constraint");
        churnErrors.add("new row violates check option");
        churnErrors.add("cannot insert into view");
        churnErrors.add("cannot update view");
        churnErrors.add("cannot delete from view");
        churnErrors.add("value too long");
        churnErrors.add("integer out of range");
        churnErrors.add("value .* out of range");
        churnErrors.add("duplicate key value");
        churnErrors.add("invalid input syntax");
        churnErrors.add("division by zero");
        churnErrors.add("out of memory");
        churnErrors.add("canceling statement");
        churnErrors.add("invalid regular expression");
        churnErrors.add("relation .* does not exist");
        churnErrors.add("cannot create index on relation");
        try {
            PostgresSchema schema = globalState.getSchema();
            for (PostgresTable table : schema.getDatabaseTables()) {
                if (table.getColumns().isEmpty()) continue;
                if (table.isView()) continue;
                if (table.isPartitioned()) continue;
                // ITEM B: idx_pt children would take generic INSERTs with random pk (partition-constraint
                // violation → thread death); idx_pt's data is managed only by its parent-routed seed.
                if (table.getName().startsWith("idx_pt")) continue;
                // ITEM C: idx_gs churn (UPDATE/DELETE) would clear its visibility-map all-visible bits and
                // starve case 53's index-ordered-input gate (Index-Only Scan would pay heap fetches again).
                if (table.getName().startsWith("idx_gs")) continue;
                List<PostgresColumn> insertableCols = table.getColumns().stream()
                        .filter(c -> !c.isGenerated())
                        .filter(c -> !c.hasSequenceDefault())
                        .filter(c -> !"cb".equals(c.getName())) // BRIN identity col — never insert explicitly
                        // gj/ga/gp: GIN/GiST default cols — let DEFAULT fill (see populate path for rationale).
                        .filter(c -> !"gj".equals(c.getName()) && !"ga".equals(c.getName()) && !"gp".equals(c.getName()))
                        .filter(c -> !"cu".equals(c.getName())) // bloom-only DEFAULT col — keep DEFAULT distribution
                        .filter(c -> !"cm".equals(c.getName())) // minmax_multi-only DEFAULT col — keep DEFAULT distribution
                        .filter(c -> !"rng".equals(c.getName())) // range-GiST DEFAULT col (not btree-insertable here)
                        .collect(Collectors.toList());
                if (insertableCols.isEmpty()) continue;
                String tn = table.getName();
                // Net-NEUTRAL churn: INSERT count == DELETE count so table size holds at the seeded
                // level and never grows unbounded (mirrors CRDB's bounded-data policy — CRDB re-populates
                // toward a target with PK-idempotent inserts rather than compounding growth). This keeps
                // the desync coverage (UPDATE/DELETE) without the throughput decay of net-positive growth.
                final int churnRows = 25;
                // (1) INSERT ~churnRows rows (replenishes exactly what DELETE removes)
                try {
                    StringBuilder sb = new StringBuilder();
                    sb.append("INSERT INTO ").append(tn).append("(");
                    sb.append(insertableCols.stream().map(c -> c.getName()).collect(Collectors.joining(", ")));
                    sb.append(") VALUES ");
                    for (int row = 0; row < churnRows; row++) {
                        if (row > 0) sb.append(", ");
                        sb.append("(");
                        for (int col = 0; col < insertableCols.size(); col++) {
                            if (col > 0) sb.append(", ");
                            sb.append(generateRandomValueForType(insertableCols.get(col).getType()));
                        }
                        sb.append(")");
                    }
                    sb.append(" ON CONFLICT DO NOTHING;");
                    log(sb.toString());
                    globalState.executeStatement(new SQLQueryAdapter(sb.toString(), churnErrors, true));
                } catch (Throwable t) { }
                // (2) UPDATE ~30 random rows on one random insertable column (drives index<->heap
                // desync: partial-index membership drift, expression-index recompute, HOT chains).
                // UPDATE does not change row count, so it is size-neutral.
                try {
                    PostgresColumn uc = Randomly.fromList(insertableCols);
                    String updSql = "UPDATE " + tn + " SET " + uc.getName() + " = "
                            + generateRandomValueForType(uc.getType())
                            + " WHERE ctid IN (SELECT ctid FROM " + tn + " ORDER BY random() LIMIT 30);";
                    log(updSql);
                    globalState.executeStatement(new SQLQueryAdapter(updSql, churnErrors, true));
                } catch (Throwable t) { }
                // (3) DELETE churnRows random rows (== INSERT count → net-neutral, bounded table size)
                try {
                    String delSql = "DELETE FROM " + tn
                            + " WHERE ctid IN (SELECT ctid FROM " + tn + " ORDER BY random() LIMIT " + churnRows + ");";
                    log(delSql);
                    globalState.executeStatement(new SQLQueryAdapter(delSql, churnErrors, true));
                } catch (Throwable t) { }
                // (4) Refresh stats (via analyzeTolerant → repopulates the C1 epoch set so same-epoch shape
                // ANALYZEs of this table skip until the next churn)
                try {
                    analyzeTolerant(tn);
                } catch (Throwable t) { }
            }
        } catch (Throwable t) { }
    }

    /**
     * PruneIndexes analogue: REINDEX every table to rebuild its indexes from the (churned) heap.
     * Single-thread-per-database, so the ACCESS EXCLUSIVE lock is uncontended. Error-tolerant.
     */
    private void doReindex() {
        try {
            // REINDEX is heavy and can legitimately hit the per-statement timeout, deadlock, or lose a
            // race with concurrent DDL. None of these are index bugs — tolerate them as expected so a
            // benign operational error never escalates to a thread-killing AssertionError.
            ExpectedErrors reindexErrors = new ExpectedErrors();
            reindexErrors.add("canceling statement due to statement timeout");
            reindexErrors.add("deadlock detected");
            reindexErrors.add("could not obtain lock");
            reindexErrors.add("does not exist");
            reindexErrors.add("out of memory");
            reindexErrors.add("out of shared memory");
            reindexErrors.add("could not create unique index");
            reindexErrors.add("cannot reindex");
            PostgresSchema schema = globalState.getSchema();
            for (PostgresTable table : schema.getDatabaseTables()) {
                if (table.isView()) continue;
                if (table.isPartitioned()) continue;
                // ITEM B: keep idx_pt entirely under its own seed/case-33 management.
                if (table.getName().startsWith("idx_pt")) continue;
                // ITEM C: REINDEX on idx_gs (40k×800B) is pure waste and resets its index VM bits.
                if (table.getName().startsWith("idx_gs")) continue;
                try {
                    String sql = "REINDEX TABLE " + table.getName() + ";";
                    log(sql);
                    globalState.executeStatement(new SQLQueryAdapter(sql, reindexErrors, true));
                } catch (Throwable t) { }
            }
        } catch (Throwable t) { }
    }

    /**
     * Sanitize a string for use inside a PostgreSQL string literal.
     * Removes control characters (newline, CR, tab, null, etc.) that would
     * cause "Unterminated string literal" or similar syntax errors, and
     * escapes single quotes.
     */
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

    /**
     * P0: Generate a value that targets actual data in the table.
     * Priority: sampleColumnValues > MIN/MAX > random (fallback).
     * This replaces bare generateRandomValueForType() calls in query WHERE clauses
     * to ensure WHERE conditions hit real data instead of producing empty result sets.
     *
     * Adapted from MySQL's generateDataAwareValueForType() for PostgreSQL.
     */
    private String generateDataAwareValueForType(String tableName, PostgresColumn col) {
        // Priority 0: ② boundary-value injection (~EDGE_PCT% when enabled). Probes range edges where
        // off-by-one btree-descent / BRIN-boundary bugs hide. Returns an RHS constant only, so armB stays a
        // byte-identical twin of armA (0-FP preserved). Null => type has no edge form; fall through.
        if (EDGE && Randomly.getNotCachedInteger(0, 100) < EDGE_PCT) {
            String edge = generateEdgeValueForType(tableName, col);
            if (edge != null) {
                return edge;
            }
        }
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

    /**
     * ② Produce a boundary literal for {@code col}, or null if the type has no edge form (caller then falls
     * back to the normal sampled/MIN-MAX path). Only INT and TEXT get edge forms — the two families where
     * off-by-one range-descent bugs are well-defined. FLOAT/REAL/DECIMAL are deliberately excluded (no clean
     * integral boundary; -0.0 / render hazards). The returned string is always an RHS constant that is
     * dropped into a predicate identically in both arms, so it never affects A/B value-identity.
     */
    private String generateEdgeValueForType(String tableName, PostgresColumn col) {
        PostgresDataType t = col.getType();
        if (t == PostgresDataType.INT) {
            switch ((int) Randomly.getNotCachedInteger(0, 6)) {
            case 0:
                return "2147483647";    // int4 max
            case 1:
                return "-2147483648";   // int4 min
            case 2:
                return "0";
            case 3:
                return "32767";         // int2 max (exercises smallint-boundary coercions)
            case 4:
                return "-32768";        // int2 min
            default:
                // The column's own MIN or MAX, nudged by ±1 — the tight boundary around real data where an
                // index range-scan either includes or drops the extremal row.
                String mm = tryGetMinMaxValue(tableName, col);
                if (mm != null) {
                    try {
                        long v = Long.parseLong(mm.trim());
                        long adj = v + (Randomly.getBoolean() ? 1 : -1);
                        // Clamp to int4 range so we never emit an out-of-range literal (which would error
                        // and waste the round). Clamping back onto the boundary is itself a valid edge probe.
                        if (adj > 2147483647L) {
                            adj = 2147483647L;
                        } else if (adj < -2147483648L) {
                            adj = -2147483648L;
                        }
                        return Long.toString(adj);
                    } catch (NumberFormatException ignore) {
                        // non-integral render — fall through to a safe constant
                    }
                }
                return "0";
            }
        }
        if (t == PostgresDataType.TEXT) {
            switch ((int) Randomly.getNotCachedInteger(0, 3)) {
            case 0:
                return "''";            // empty string — collation lower boundary
            case 1: {
                // 1-char prefix of a genuinely-sampled value (a real btree neighbour boundary).
                List<String> sampled = sampleColumnValues(tableName, col.getName(), 5);
                if (sampled != null && !sampled.isEmpty()) {
                    String raw = Randomly.fromList(sampled);
                    if (raw != null) {
                        String inner = raw;
                        if (inner.startsWith("'") && inner.endsWith("'") && inner.length() >= 2) {
                            inner = inner.substring(1, inner.length() - 1);
                        }
                        if (inner.length() >= 1) {
                            return "'" + sanitizeStringLiteral(inner.substring(0, 1)) + "'";
                        }
                    }
                }
                return "''";
            }
            default:
                return "''";
            }
        }
        return null;
    }

    /**
     * Quote a sampled value based on column type.
     * TEXT values need single-quote wrapping; numeric values returned as-is.
     */
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

    /**
     * P0: Try to get MIN or MAX value from column for better index hit rate.
     * Uses the column's index (if any) for efficient single-row lookup.
     */
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

    /**
     * Try to generate a WHERE condition that can utilize an existing index.
     * Returns null if no suitable index found (caller should fall back to random WHERE).
     */
    /**
     * Smart index-aware WHERE clause generation.
     * Analyzes actual indexes on the tables and generates conditions that
     * trigger specific PostgreSQL optimizer paths:
     * - Composite index prefix conditions (range scan, ref access)
     * - OR across different indexed columns (Bitmap index scan)
     * - Multi-column AND conditions (composite index full match)
     * - NULL handling conditions (IS NULL / IS NOT NULL)
     * - Type-specific patterns (IN for INT, LIKE prefix for VARCHAR, etc.)
     */
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

    /** Strategy 1: Composite index prefix condition — triggers composite index range scan */
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

    /** Strategy 2: Full composite index condition — triggers unique/ref lookup */
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

    /** Strategy 3: Index merge condition — OR across different indexed columns (Bitmap OR) */
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

    /** Strategy 4: Range with NULL handling — tests index scan NULL boundary */
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

    /** Strategy 5: Multi-index OR with varied operators — triggers BitmapOr */
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

    /** Strategy 6: Type-aware conditions for specific optimizer paths */
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

    /** Generate a range condition: col > val, col < val, col >= val, or col BETWEEN a AND b */
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

    /** Generate a list of constants for IN conditions */
    private List<PostgresExpression> generateConstantList(PostgresDataType type, Randomly r, int min, int max) {
        List<PostgresExpression> list = new ArrayList<>();
        int count = r.getInteger(min, max + 1);
        for (int i = 0; i < count; i++) {
            list.add(PostgresExpressionGenerator.generateConstant(r, type));
        }
        return list;
    }

    /** Maybe add a complex extra expression */
    private PostgresExpression maybeAddComplexExtra(PostgresExpression combined, PostgresExpressionGenerator gen) {
        if (combined != null && Randomly.getBooleanWithRatherLowProbability()) {
            try {
                PostgresExpression randomExtra = gen.generateExpression(0, PostgresDataType.BOOLEAN);
                return new PostgresBinaryLogicalOperation(combined, randomExtra, BinaryLogicalOperator.AND);
            } catch (Exception e) { }
        }
        return combined;
    }

    /** Fallback: basic WHERE using all columns */
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

    /** Generate a simple, index-friendly condition: col op constant */
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



    // ==================== P0: Inheritance & Cross-Join Detection ====================

    /**
     * Check if the query uses inheritance syntax (table*).
     * Inheritance syntax causes different scan methods to return different rows
     * because SeqScan includes child tables while some IndexScan paths may not.
     */
    private boolean usesInheritanceSyntax(String queryString) {
        // Match PostgreSQL inheritance syntax: a SQLancer table name (t<digits>) directly followed by
        // '*' (optionally one space), e.g. "FROM t0*" / "FROM t3 *". Do NOT use a bare contains("* ")
        // test: it false-matches the ubiquitous "SELECT * FROM ..." projection and, combined with the
        // size-difference filter in compareResults*, would silently SWALLOW genuine cardinality-mismatch
        // index bugs (the mode-28 arms are value-identity equal by construction, so every size diff is a
        // real bug). The idx oracle never emits inheritance, so this is effectively always false here.
        return queryString.matches("(?s).*\\bt\\d+ ?\\*.*");
    }

    /**
     * Check if the query involves a cross join (FROM multiple tables without JOIN conditions).
     * Cross joins create duplicate ORDER BY values even when the ORDER BY column is unique
     * in its own table, making sort order non-deterministic.
     */
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

    /**
     * Check if the query references a view (v0 or v1) that may produce
     * non-deterministic row ordering. Recursive views and temporary views
     * without ORDER BY can return rows in different orders depending on
     * the execution path (SeqScan vs IndexScan), leading to false positives
     * when combined with cross joins.
     */
    private boolean usesNonDeterministicView(String queryString) {
        String upper = queryString.toUpperCase();
        // Check for view references (v0, v1) in FROM clause or JOIN
        // These are created by SQLancer's view generation and may be recursive
        return upper.matches("(?s).*\\bV[01]\\b.*");
    }

    // ==================== P1: Tie-Breaker Detection ====================

    /**
     * Check if the ORDER BY clause includes a column that is a PRIMARY KEY or UNIQUE index
     * AND the column has no NULL values.
     * If so, the sort order is deterministic even with LIMIT, because there are no ties.
     *
     * IMPORTANT: PostgreSQL UNIQUE constraints allow multiple NULL values, so a UNIQUE index
     * alone is NOT sufficient to guarantee deterministic ORDER BY. We must also verify that
     * the column has no NULLs (via NOT NULL constraint or runtime check).
     */
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

    /**
     * Extract table names from the FROM clause of a query.
     * Returns null if parsing fails (conservative: null means "don't filter").
     * Handles: FROM t0, FROM t0, t1, FROM ONLY t2, FROM t0*, FROM t0 AS a, FROM t0 a
     */
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

    /**
     * Runtime check: does the given column have any NULL values in the table?
     * Returns true if NULL values exist, false if no NULLs (or on error, conservatively returns true).
     */
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

    /**
     * Runtime verification that a column actually has unique values in the table.
     * This handles edge cases where schema metadata is inaccurate:
     * 1. UNIQUE index creation failed (data has duplicates, but schema may be stale)
     * 2. Partial UNIQUE index (only enforces uniqueness on a WHERE subset)
     * 3. Index dropped/recreated between schema fetch and query execution
     *
     * @return true if the column has no duplicate values, false otherwise
     */
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


    /**
     * Extract ORDER BY column values from result rows.
     * Each row is formatted as "col0 ||| col1 ||| col2 ||| ..."
     * We extract the values at the specified column indices.
     * Returns a multi-set (using sorted string representation for comparison).
     */
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
    /**
     * P0: Build a data-driven partial index condition using actual column statistics.
     * Instead of fixed "col > 0", uses MIN/MAX/sampled values to create
     * selective partial index conditions that target real data ranges.
     */
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

    /**
     * P0: Build a query that exercises the partial index in diverse ways.
     * Patterns:
     *   0: Exact match of partial index condition (basic coverage)
     *   1: Partial condition + additional data-aware filter on another column
     *   2: Partial condition + range scan on indexed column
     *   3: Partial condition + IN list with sampled values
     */
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

    // ==================== Index Differential Shapes ====================

    /**
     * Dispatch equivalent-query, index-definition and integrity checks. Query rewrites preserve
     * values while preventing index matching; EXPLAIN gates verify the intended access paths.
     * Do not force optimizer settings: the reference arm must remain index-independent.
     */
    private void checkIndexDifferential() throws Exception {
        int shape = Randomly.fromOptions(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
                22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46,
                47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 65, 66, 67);
        // Give applicability-limited shapes extra attempts without relaxing their EXPLAIN gates.
        if (Randomly.getPercentage() < 0.25) {
            shape = Randomly.fromOptions(4, 12, 13, 22, 26, 28, 31, 15, 50, 51, 55, 57, 60, 33, 62, 63, 64, 65, 66, 67,
                    2, 59);  // partial + mcgin: gate-healthy but draw-starved in full mix
        }
        if (ONLY >= 0) {
            shape = ONLY;
        }
        switch (shape) {
        case 0:  checkNonSargableRewrite(); break;      // scalar: WHERE col <op> V vs WHERE f(col) <op> V
        case 1:  checkOrderByIndexRewrite(); break;     // ORD: index-provided order vs explicit Sort
        case 2:  checkPartialIndexRewrite(); break;     // partial index predicate-implication
        case 3:  checkExpressionIndexRewrite(); break;  // expression index (lower/abs)
        case 4:  checkBrinRewrite(); break;             // BRIN block-range bitmap scan
        case 5:  checkCoveringIndexRewrite(); break;    // covering / index-only scan
        case 6:  checkMultiIndexRewrite(); break;       // multi-index bitmap OR merge
        case 7:  checkNullIndexRewrite(); break;        // NULL handling through the index
        case 8:  checkCompositeIndexRewrite(); break;   // composite (a,b) index cond pushdown
        case 9:  checkPrefixIndexRewrite(); break;      // prefix LIKE via text_pattern_ops
        case 10: checkTrigramLikeRewrite(); break;      // infix LIKE via pg_trgm GIN
        case 11: checkAggregateIndexRewrite(); break;   // MIN/MAX index pushdown (InitPlan)
        case 12: checkSubqueryIndexRewrite(); break;    // index use with a scalar-subquery RHS
        case 13: checkUniqueIndexRewrite(); break;      // unique-index equality scan
        case 14: checkRangeGistRewrite(); break;        // int4range GiST overlap/contain
        case 15: checkJoinIndexRewrite(); break;        // join-key index (index-nested-loop) vs hash join
        case 16: checkGinJsonbRewrite(); break;         // GIN jsonb key-existence (gj ? 'gN', jsonb_ops-exclusive)
        case 17: checkGinArrayRewrite(); break;         // GIN int[] containment (ga @> ARRAY[N])
        case 18: checkHashIndexRewrite(); break;        // HASH index equality scan
        case 19: checkGinJsonbPathRewrite(); break;     // GIN jsonb_path_ops jsonpath @? (other opclass+op)
        case 20: checkGistPointRewrite(); break;        // GiST 2-D point containment (gp <@ box)
        case 21: checkBrinBloomRewrite(); break;        // BRIN bloom opclass equality
        case 22: checkSemiJoinIndexRewrite(); break;    // MULTI-TABLE: cross-table EXISTS semijoin index probe
        case 23: checkIndexDefinitionConsistency(); break; // INDEX-DEF: before/after CREATE equivalent index
        case 24: checkIndexDropConsistency(); break;    // INDEX-DEF: before/after DROP our own index
        case 25: checkCompositeOrderByIndexRewrite(); break; // ORDER-SENSITIVE: composite index order, key-only projection
        case 26: checkUniqueOrderByIndexRewrite(); break;    // ORDER-SENSITIVE: unique cb total order, full projection
        case 27: checkCompositePrefixRangeRewrite(); break;  // MULTI-KEY: equality-prefix + range second key descent
        case 28: checkSaopRewrite(); break;                  // SAOP: same-column equality-OR -> c0 = ANY(array) descent
        case 29: checkGroupByIndexRewrite(); break;          // UPPER-NODE: GROUP BY grouping over indexed key (GroupAggregate)
        case 30: checkDistinctIndexRewrite(); break;         // UPPER-NODE: DISTINCT over indexed key (Unique/skip-scan)
        case 31: checkWindowIndexRewrite(); break;           // UPPER-NODE: window OVER (ORDER BY cb) index-provided order
        case 32: checkAmcheckIntegrity(); break;             // INTEGRITY: amcheck bt_index_check(heapallindexed) ground truth
        case 33: checkPartitionPruneRewrite(); break;        // PARTITION: prune to one partition + ride propagated local c0 index
        case 34: checkPartialImplicationRewrite(); break;    // PARTIAL-IMPLICATION: query pred strictly implies (differs from) index WHERE
        case 35: checkIncrementalSortRewrite(); break;       // UPPER-NODE: index prefix feeds Incremental Sort
        case 36: checkMergeJoinRewrite(); break;             // UPPER-NODE: index-ordered inputs feed a Merge Join
        case 37: checkIndexOnlyPayloadRewrite(); break;      // PAYLOAD: covering INCLUDE index serves c0,c3,c4 from the index
        case 38: checkKnnOrderRewrite(); break;              // KNN: GiST <-> distance order (Index Scan Order By)
        case 39: checkRowComparisonRewrite(); break;         // ROW-CMP: composite (c0,c1) > (x,y) row-comparator descent
        case 40: checkGinContainmentRewrite(); break;        // GIN-INTERSECT: multi-element @> posting-list intersection
        // case 41 (EXPRIDX) merged into case 3 (checkExpressionIndexRewrite): abs-range variant folded in.
        case 42: checkCrossTypeCastRewrite(); break;         // CROSS-TYPE: c0 <op> v::bigint int4↔int8 Index Cond
        case 43: checkTsvectorRewrite(); break;              // FULLTEXT: to_tsvector @@ tsquery rides functional GIN
        case 44: checkSpGistTextRewrite(); break;            // SP-GIST: c7 text equality/prefix rides spgist (sole index)
        case 45: checkMixedOrderRewrite(); break;            // ORDER-SENSITIVE: (c0 ASC, c1 DESC) mixed-direction composite
        case 46: checkHeteroBitmapRewrite(); break;          // HETERO-BITMAP: BitmapAnd of btree(c0)+GIN(gj)
        case 47: checkNullsOrderRewrite(); break;            // NULLS-ORDER: c2 DESC NULLS LAST index-provided placement
        case 48: checkTextOrderCollateRewrite(); break;      // TEXT-ORDER: c7 COLLATE "C" index-provided byte-order scan
        case 49: checkCompositeNullsOrderRewrite(); break;   // ORDER-SENSITIVE: (c0 ASC, c2 DESC NULLS LAST) nullable-key combo
        case 50: checkAntiJoinIndexRewrite(); break;         // MULTI-TABLE: cross-table NOT EXISTS anti-join index probe
        case 51: checkLateralIndexRewrite(); break;          // LATERAL: top-N-per-group self-lateral inner index probe
        case 52: checkMergeAppendOrderRewrite(); break;      // PARTITION-ORDER: cross-partition Merge Append ordered c0 scan
        case 53: checkGroupingSetsRewrite(); break;          // UPPER-NODE: ROLLUP/CUBE/GROUPING SETS over indexed c0
        case 54: checkTextBtreeRangeRewrite(); break;        // TEXT-PRED: c7 COLLATE "C" btree equality/range Index Cond
        case 55: checkMemoizeRewrite(); break;               // MEMOIZE: self-join inner-index-probe caching (Nested Loop + Memoize)
        case 56: checkDistinctOnRewrite(); break;            // DISTINCT-ON: index-ordered first-row-per-group (Unique over index, no Sort)
        case 57: checkSetOpInputRewrite(); break;            // SET-OP: UNION/INTERSECT/EXCEPT over c0-index range inputs
        case 58: checkNullsNotDistinctRewrite(); break;      // NND: PG15+ NULLS NOT DISTINCT unique index build + ordered scan
        case 59: checkMultiColGinRewrite(); break;           // MCGIN: multicolumn GIN gin(ga, gj) ANDed-within-index Bitmap Index Scan
        case 60: checkBrinMinmaxMultiRewrite(); break;       // BRINMM: PG14+ BRIN minmax_multi opclass equality/range on uncorrelated cm
        // case 61 (PARTPRUNE_LH) merged into case 33 (checkPartitionPruneRewrite): LIST/HASH strategies folded in.
        case 62: checkExprOrderByRewrite(); break;           // A2/EXPR-ORDER: ORDER BY abs(c0) rides idx_<t>_expr (no Sort) vs explicit Sort
        case 63: checkCountIndexOnlyRewrite(); break;        // B3/COUNT-IO: count(*) over a c0 btree range as an Index Only Scan
        case 64: checkDeleteScanRewrite(); break;            // A1/DML-SCAN: index scan feeding a Delete (rolled back) vs Seq Scan Delete
        case 65: checkBloomRewrite(); break;                 // BLOOM: contrib bloom signature index (c3,c6) multi-eq Bitmap Index Scan vs Seq Scan
        case 66: checkBtreeGistKnnRewrite(); break;          // BTGISTKNN: contrib btree_gist scalar int KNN (c3 <-> v) distance-ordered Index Scan vs Sort
        case 67: checkBtreeGinRewrite(); break;              // BTGIN: contrib btree_gin scalar int equality (c3=v) Bitmap Index Scan vs Seq Scan
        default: checkNonSargableRewrite(); break;
        }
    }

    /**
     * Orthogonal index-INTEGRITY axis (mode 29) — NOT a query differential. PostgreSQL's own amcheck
     * extension structurally verifies a B-tree index against its heap: bt_index_check(heapallindexed
     * => true) asserts (a) the B-tree per-page order / sibling / high-key / parent-downlink invariants
     * and (b) that every heap tuple has a matching index tuple (and vice-versa). This directly targets
     * index-CORRUPTION bugs — build path, incremental INSERT/UPDATE/DELETE maintenance, dedup/posting
     * lists, opclass/collation handling — that a value-identity query differential (mode 28) cannot see.
     *
     * Soundness / zero false positives: amcheck is PG's own checker, so a correct index ALWAYS passes.
     * A violation is reported as an ERROR with SQLSTATE XX001 (data_corrupted) or XX002 (index_corrupted)
     * — a class distinct from every operational error (undefined_table 42P01, query_canceled 57014,
     * out_of_memory 53200, ...). We flag a bug IFF the SQLSTATE is XX001/XX002; any other SQLException
     * (index dropped/altered between catalog read and check, timeout, recovery, resource) is skipped.
     * No comparison, no constructed equivalence, NO GUC — orthogonal to NoREC/TLP/MOZI. amcheck 1.4 is
     * B-tree only, so we discover and check only valid, ready btree indexes on ordinary/matview tables.
     */
    /**
     * True iff the EXPLAIN plan text contains a real Sort NODE (its cost line "Sort  (cost=...", two spaces).
     * This is the ONLY reliable Sort-node signal: a property line "Sort Key: ..." and the composite node labels
     * "Merge Append"/"Gather Merge" print the word "Sort" (or carry a "Sort Key:") WITHOUT a top Sort node, so a
     * bare {@code contains("Sort")} both over-matches those decoys and is noisy. "Incremental Sort  (cost" also
     * contains this substring (an Incremental Sort IS a sort step); callers that must distinguish a FULL Sort
     * from an Incremental Sort additionally test {@code !contains("Incremental Sort")} (see case 35).
     */
    private static boolean hasSortNode(String plan) {
        return plan != null && plan.contains("Sort  (cost");
    }

    private void checkAmcheckIntegrity() throws Exception {
        // amcheck is contrib; enable once (idempotent). If unavailable/permission-denied, skip the axis.
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE EXTENSION IF NOT EXISTS amcheck;", errors, true));
        } catch (Exception e) {
            return;
        }
        // Discover valid, ready B-tree indexes on ordinary/matview tables in user schemas from the LIVE
        // catalog (current for this connection), not SQLancer's cached schema.
        List<String> targets;
        try {
            targets = executeQuery(
                    "SELECT i.indexrelid::regclass::text "
                  + "FROM pg_index i "
                  + "JOIN pg_class c ON c.oid = i.indexrelid "
                  + "JOIN pg_class t ON t.oid = i.indrelid "
                  + "JOIN pg_am am ON am.oid = c.relam "
                  + "JOIN pg_namespace n ON n.oid = c.relnamespace "
                  + "WHERE am.amname = 'btree' AND i.indisvalid AND i.indisready "
                  + "AND t.relkind IN ('r','m') "
                  + "AND n.nspname NOT IN ('pg_catalog','information_schema','pg_toast') "
                  // Collation-SAFE indexes: every key-column collation OID in indcollation is either 0 (int,
                  // jsonb, array, numeric, ...) OR a DETERMINISTIC byte-order collation ("C"/"POSIX"). This
                  // excises the ONE false-positive route amcheck has here — a *locale* (libc/ICU) collation whose
                  // text ordering is inconsistent (non-transitive / equal-but-unequal) makes
                  // bt_index_parent_check report "down-link lower bound invariant violated" on a perfectly stored
                  // index (reproduces after REINDEX; bt_index_check still passes). That is an environment defect,
                  // not a DBMS index bug, so it must never be flagged. "C"/"POSIX" are pure memcmp byte-ordering
                  // (locale-independent, fully transitive) so they carry ZERO FP risk — admitting them lets the
                  // STRONGEST check (parent, heapallindexed) cover the seeded `idx_<t>_c7btree` on c7 COLLATE "C".
                  + "AND NOT EXISTS (SELECT 1 FROM unnest(i.indcollation::oid[]) col WHERE col <> 0 "
                  + "AND col NOT IN (SELECT oid FROM pg_collation WHERE collname IN ('C','POSIX')))");
        } catch (Exception e) {
            return;
        }
        if (targets == null || targets.isEmpty()) return;

        String target = Randomly.fromList(targets);
        // Tier-3 #7: before the integrity check, stress incremental btree maintenance (page splits, dead
        // tuples, HOT updates) on the index's OWNING table when it is a seeded, churnable idx_t<n> table.
        // Resolve the owner from the live catalog; the discovery query returned only an index regclass.
        try {
            List<String> own = executeQuery("SELECT indrelid::regclass::text FROM pg_index WHERE indexrelid = '"
                    + target.replace("'", "''") + "'::regclass");
            String owner = (own != null && !own.isEmpty()) ? own.get(0) : null;
            // Only idx_t<n> (columns c0..c7, cb identity, defaults for gj/ga/gp/cu/rng). Exclude partition
            // children idx_pt_* (random writes violate the RANGE constraint) and any provider table.
            if (owner != null && owner.startsWith("idx_t") && !owner.startsWith("idx_pt")) {
                amcheckChurn(owner);
            }
        } catch (Throwable ignore) {
            // churn is best-effort; a failed churn must never abort the integrity check or kill the thread.
        }
        // heapallindexed => true is the strongest mode (also verifies heap<->index coverage). Randomly pick
        // bt_index_parent_check (additionally checks parent-child down-link bounds) vs bt_index_check — both
        // are now sound: the discovery query admits only collation-free indexes, so neither can hit the OS
        // collation false positive. Each SQLancer thread owns its database on a single connection (no
        // concurrency), so the stronger lock parent_check takes is harmless.
        String fn = Randomly.getBoolean() ? "bt_index_parent_check" : "bt_index_check";
        String checkSql = "SELECT " + fn + "(index => '" + target.replace("'", "''")
                + "'::regclass, heapallindexed => true);";
        log(checkSql);

        // Run on the raw JDBC statement, NOT SQLQueryAdapter.execute(): the adapter funnels every error
        // through checkException(), which rethrows an unexpected error as a blanket AssertionError BEFORE we
        // can read its SQLSTATE — which would surface operational noise (dropped rel, timeout, recovery) as a
        // bug. Executing directly hands us the raw SQLException so we flag IFF the state is XX001/XX002.
        boolean checkPassed = false;
        try (Statement st = globalState.getConnection().createStatement()) {
            st.execute(checkSql);
            checkPassed = true;
            covBump("PG_AMCHECK");
        } catch (SQLException e) {
            String state = e.getSQLState();
            if ("XX001".equals(state) || "XX002".equals(state)) {
                // data_corrupted / index_corrupted — a real index-integrity bug.
                throw new AssertionError("PG_AMCHECK " + state + " on " + target + ": " + e.getMessage(), e);
            }
            return; // operational error (missing rel, timeout, recovery, resource) — never a bug.
        }
        // FAULT self-proof (ships OFF): real corruption cannot be injected here, so when the index checks out
        // clean, simulate a detected XX001 to prove the detection→AssertionError surfacing path is wired live.
        if (checkPassed && FAULT) {
            throw new AssertionError("PG_AMCHECK XX001 (FAULT self-proof) on " + target);
        }
    }

    /**
     * Tier-3 #7 churn burst for {@link #checkAmcheckIntegrity()}: a bounded, single-session clone-INSERT +
     * indexed-column UPDATE + DELETE on a seeded {@code idx_t<n>} table to exercise incremental btree
     * maintenance (page splits, dead tuples, HOT) before the integrity verification. Each statement runs in
     * its own try/catch(Throwable) with tolerant ExpectedErrors so churn can never abort the check or kill a
     * thread. NO VACUUM afterward — the churned/dead-tuple state is exactly what bt_index_check verifies.
     */
    private void amcheckChurn(String owner) {
        ExpectedErrors churnErrors = new ExpectedErrors();
        churnErrors.add("canceling statement due to statement timeout");
        churnErrors.add("canceling statement due to user request");
        churnErrors.add("deadlock detected");
        churnErrors.add("duplicate key value violates unique constraint");
        churnErrors.add("value out of range");
        churnErrors.add("integer out of range");
        churnErrors.add("out of range");
        churnErrors.add("relation .* does not exist");
        churnErrors.add("could not open relation");
        long k = globalState.getRandomly().getInteger(20, 80);
        long d = globalState.getRandomly().getInteger(1, 100);
        String[] stmts = {
            // clone valid rows (cb identity + gj/ga/gp/cu/rng defaults auto-fill) → index growth / splits.
            "INSERT INTO " + owner + " (c0,c1,c2,c3,c4,c5,c6,c7) SELECT c0,c1,c2,c3,c4,c5,c6,c7 FROM " + owner
                    + " ORDER BY random() LIMIT " + k,
            // churn indexed columns in place → dead index tuples + fresh ones.
            "UPDATE " + owner + " SET c0 = c0 + " + d + ", c1 = c1 - " + d + " WHERE cb IN (SELECT cb FROM "
                    + owner + " ORDER BY random() LIMIT " + k + ")",
            // delete rows → dead heap/index tuples.
            "DELETE FROM " + owner + " WHERE cb IN (SELECT cb FROM " + owner + " ORDER BY random() LIMIT " + k + ")",
        };
        for (String sql : stmts) {
            try {
                globalState.executeStatement(new SQLQueryAdapter(sql, churnErrors, true));
            } catch (Throwable ignore) {
                // best-effort — proceed to the integrity check regardless of this statement's fate.
            }
        }
        // the heap just changed: let a later same-epoch ANALYZE re-stat these tables if a shape needs it.
        analyzedThisEpoch.remove(owner);
    }

    // ---- shared helpers for the mode-28 sound shapes ----

    /** Pick a random non-view table, or null. */
    private PostgresTable pickNonViewTable() {
        List<PostgresTable> tables = globalState.getSchema().getDatabaseTables();
        if (tables.isEmpty()) return null;
        PostgresTable t = Randomly.fromList(tables);
        // ITEM B: keep partition internals out of the generic scalar/expr/covering/… shapes — idx_pt is
        // exercised only by the dedicated case 33 (pickPartitionedTable). (Landing on a child is already
        // value-identity-sound, but isolating it avoids partition-specific plan quirks and wasted rounds.)
        // ITEM C: idx_gs is the dedicated GROUPING SETS table (case 53) — 40k rows × 800B. Generic shapes
        // landing on it would pay a ~32MB Seq Scan per armB and (via their own DDL/DML) dirty its visibility
        // map, silently starving case 53's index-ordered-input gate. It is exercised ONLY by case 53.
        if (t.isView() || t.getName().startsWith("idx_pt") || t.getName().startsWith("idx_gs")) return null;
        return t;
    }

    /**
     * Pick an {@code idx_t<n>} table that has the physically-ordered {@code cb} column — the only
     * tables the BRIN shape can exercise. The generic {@link #pickNonViewTable()} landed on a valid
     * cb-table only ~28% of the time (measured), starving the BRIN funnel; this targets them directly.
     */
    private PostgresTable pickBrinCbTable() {
        List<PostgresTable> tables = globalState.getSchema().getDatabaseTables();
        if (tables.isEmpty()) return null;
        List<PostgresTable> cbTables = new ArrayList<>();
        for (PostgresTable t : tables) {
            if (t.isView() || !t.getName().startsWith("idx_t")) continue;
            for (PostgresColumn c : t.getColumns()) {
                if ("cb".equals(c.getName())) { cbTables.add(t); break; }
            }
        }
        return cbTables.isEmpty() ? null : Randomly.fromList(cbTables);
    }

    /** Columns of the table that have a validated value-identity non-sargable wrapper. */
    private List<PostgresColumn> wrappableColumns(PostgresTable table) {
        List<PostgresColumn> out = new ArrayList<>();
        for (PostgresColumn c : table.getColumns()) {
            // gp is a POINT column modeled as TEXT by the schema reader (PostgresDataType has no POINT).
            // POINT has NO default btree/hash operator class, so any generic shape that builds a plain
            // btree/hash index on it (checkUniqueIndexRewrite, scalar, expr, composite, …) fails DDL with
            // "data type point has no default operator class" — a hard error not in every shape's LOCAL
            // expected-error set → a thread-killing AssertionError. gp is exercised ONLY by the dedicated
            // GiST shape checkGistPointRewrite, which addresses it by name (pickGinTable("gp")) and builds
            // a GiST index, so it never needs the generic wrappable pool. Exclude it here. (gj/ga stay:
            // jsonb/array DO have btree opclasses, so their generic index builds succeed and any ill-typed
            // predicate self-skips via the shared errors set.)
            if ("gp".equals(c.getName())) {
                continue;
            }
            // cu is bloom-only by design (see createIndexFriendlyTables): it must have NO btree so `cu = v` is
            // forced onto the bloom BRIN (case 21). Excluding it here stops generic shapes building a competing
            // btree (nsidx_*_cu) that would steal case 21's gate. cu is addressed by name, never via this pool.
            if ("cu".equals(c.getName())) {
                continue;
            }
            // cm is minmax_multi-only by design (see createIndexFriendlyTables): it must have NO btree so `cm = v`
            // / `cm BETWEEN` is forced onto the minmax_multi BRIN (case 60). Excluding it here stops generic shapes
            // building a competing btree that would steal case 60's gate. cm is addressed by name, never via this pool.
            if ("cm".equals(c.getName())) {
                continue;
            }
            // rng is an int4range column: like gp (POINT) it has NO default btree/hash operator class, so a generic
            // plain-index build (checkUniqueIndexRewrite, scalar, composite, …) would hard-error "data type int4range
            // has no default operator class" → a thread-killing AssertionError. rng is exercised ONLY by the dedicated
            // range-GiST shape (case 14 checkRangeGistRewrite), which addresses RANGE columns by type and builds a
            // GiST index, so it never needs the generic wrappable pool. Exclude it here.
            if ("rng".equals(c.getName())) {
                continue;
            }
            if (nonSargableWrapFor(c, c.getName()) != null) {
                out.add(c);
            }
        }
        return out;
    }

    /**
     * Wrappable join keys excluding TEXT, whose platform-dependent collation can produce
     * index/heap differences unrelated to the index logic under test.
     */
    private List<PostgresColumn> joinKeyColumns(PostgresTable table) {
        List<PostgresColumn> out = new ArrayList<>();
        for (PostgresColumn c : wrappableColumns(table)) {
            if (c.getType() == PostgresDataType.TEXT) {
                continue;
            }
            out.add(c);
        }
        return out;
    }

    private boolean isNumericType(PostgresColumn col) {
        switch (col.getType()) {
        case INT: case DECIMAL: case FLOAT: case REAL:
            return true;
        default:
            return false;
        }
    }

    /**
     * Extract a LIKE token (up to {@code len} chars) from a sampled real value of the column,
     * escaped for a standard-conforming-strings LIKE literal (backslash/%/_ /quote). Returns
     * null if no suitable value exists. When {@code requireFull}, the raw value must be at least
     * {@code len} chars (so trigram infix patterns carry enough content for the GIN index).
     */
    private String sampleLikeToken(String tbl, String colName, int len, boolean requireFull) {
        List<String> vals = sampleColumnValues(tbl, colName, 8);
        if (vals == null) return null;
        for (String raw : vals) {
            if (raw == null) continue;
            String s = raw;
            if (s.length() >= 2 && s.startsWith("'") && s.endsWith("'")) {
                s = s.substring(1, s.length() - 1);
            }
            if (requireFull ? s.length() < len : s.isEmpty()) continue;
            String tok = s.substring(0, Math.min(len, s.length()))
                    .replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_").replace("'", "''");
            if (!tok.isEmpty()) return tok;
        }
        return null;
    }

    private void checkNonSargableRewrite() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        PostgresTable table = Randomly.fromList(tables);
        if (table.isView()) return;
        if (table.getName().startsWith("idx_gs")) return; // dedicated to case 53 (see ITEM C)

        // Candidate scalar columns that have a validated value-identity wrapper.
        List<PostgresColumn> candidates = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (nonSargableWrapFor(col, col.getName()) != null) {
                candidates.add(col);
            }
        }
        if (candidates.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(candidates);
        String tbl = table.getName();
        String colName = col.getName();

        // ONE wrapper instance threaded through armB (do NOT recompute — desync risk).
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;

        // V targets real data for a good index-hit rate. Skip NULL (col = NULL never
        // matches, so it is a wasted case, not a bug).
        String v = generateDataAwareValueForType(tbl, col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;

        String idxName = "nsidx_" + tbl + "_" + colName;
        // Predicate variety: equality, B-tree range, and IN-list all keep armA sargable while the
        // wrapper makes armB index-independent. Value-identity of the wrapper holds under every
        // comparison operator, so the two arms compute the same row set by construction.
        String pred;
        String predWrapped;
        String op = Randomly.fromOptions("=", ">", "<", ">=", "<=", "IN");
        if ("IN".equals(op)) {
            String v2 = generateDataAwareValueForType(tbl, col);
            String v3 = generateDataAwareValueForType(tbl, col);
            if (v2 == null || v3 == null || "NULL".equalsIgnoreCase(v2) || "NULL".equalsIgnoreCase(v3)) return;
            String list = " IN (" + v + ", " + v2 + ", " + v3 + ")";
            pred = colName + list;
            predWrapped = wrapped + list;
        } else {
            pred = colName + " " + op + " " + v;
            predWrapped = wrapped + " " + op + " " + v;
        }
        // Depth: with probability governed by the deep knobs, AND a DEEP deterministic sub-predicate onto
        // the indexable conjunct. armB wraps every target-column reference (in the conjunct AND the deep
        // part), so the two WHEREs stay value-equivalent under 3VL -> equal row sets by construction, while
        // the deep Filter exercises the index recheck/filter path against a complex predicate. OR/NOT live
        // only inside the parenthesized deep sub-predicate, so armA stays index-eligible on the target
        // conjunct. Routed through maybeDeepen so all six deepened shapes share the tunable config.
        // FAULT self-proof (ships OFF): NOT-wrap armB's (already non-sargable) predicate so its row set
        // diverges while the wrapped LHS keeps armB a Seq Scan (the armB gate still accepts). armB ≡ armA when OFF.
        String armA = "SELECT * FROM " + tbl + " WHERE " + pred;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + predWrapped + ")" : predWrapped);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];

        List<String> rA;
        List<String> rB;
        try {
            // Ensure an index exists on the target column so armA CAN be index-accelerated.
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX IF NOT EXISTS " + idxName + " ON " + tbl + " (" + colName + ");", errors, true));
            analyzeTolerant(tbl);

            // EXPLAIN gate (no GUC): armA index-accelerated (Index Cond present); armB a
            // pure heap Seq Scan with NO index node at all (index-independent ground truth).
            // Otherwise discard (misses eviction — sound, just lower yield).
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // Column-bound positive gate: require an "Index Cond" line that references the TARGET column
            // (colName) specifically, not just any Index Cond a deepened sub-predicate may have pulled in on a
            // DIFFERENT indexed column. This isolates the differential to colName's index. (FP-safety does not
            // depend on this -- the armB gate below rejects any armB that keeps an index node.) The live plan
            // renders the cond as "Index Cond: (c0 = 5)"; colNames c0..c7/cb/cu are mutually non-substring, so a
            // plain contains on the Index Cond line is unambiguous and the index NAME lives on a separate line.
            boolean armAUsesIndex = false;
            for (String planLine : planA.split("\n")) {
                if (planLine.contains("Index Cond") && planLine.contains(colName)) {
                    armAUsesIndex = true;
                    break;
                }
            }
            boolean armBIndexIndependent = planB.contains("Seq Scan") && !planB.contains("Index");
            if (!armAUsesIndex || !armBIndexIndependent) return;

            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return; // discard per-arm DDL/runtime errors — not the bug axis
        }
        if (rA == null || rB == null) return;

        log(armA);
        log(armB);
        // Reports (throws AssertionError) on any surviving row-set mismatch = real bug.
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NONSARGABLE");
    }

    /**
     * Value-identity non-sargable wrapper for the column, or null if unsupported.
     * Validated on PG 17.6 (all exact identity incl. NULL, all non-sargable):
     *   INT/DECIMAL/FLOAT/REAL/TEXT/BOOLEAN/MONEY/INET/BIT → least(c,c) | greatest(c,c)
     * BOOLEAN/RANGE skipped for AND/OR (sargable); RANGE handled by checkRangeGistRewrite.
     * NB: c+0 / c*1 are excluded deliberately — they are constant-fold traps (brittle).
     *
     * TEXT deliberately uses least/greatest, NOT (c||'')/(''||c): the concat wrapper casts the
     * operand to `text`, which for a CHAR(n)/bpchar column (SQLancer maps CHAR(n) -> TEXT) STRIPS
     * the trailing blank-padding and switches equality/ORDER/LIKE from blank-insensitive bpchar
     * semantics to blank-sensitive text semantics -> NOT value-identity (min(c) vs min(''||c)
     * render differently; c=V vs (''||c)=V can select different rows). least/greatest(c,c) returns
     * the SAME type (bpchar stays bpchar, padded) and is an exact value-identity for text/varchar/
     * bpchar alike, and is equally non-sargable. psql-proven on PG 17.6.
     */
    private String nonSargableWrapFor(PostgresColumn col, String expr) {
        switch (col.getType()) {
        case INT:
        case DECIMAL:
        case FLOAT:
        case REAL:
        case TEXT:
            return wrapValueIdentity(expr);
        case BOOLEAN:
        case MONEY:
        case INET:
        case BIT:
            // Value-identity (incl NULL) for any btree-ordered type and non-sargable (the planner cannot
            // match the wrapped expression to a plain-column index -> Seq Scan). psql-validated on PG 17.6
            // for all four types. NOTE: boolean's (b AND b) IS sargable, so we use the wrapper catalog here
            // too. RANGE is deliberately excluded (handled by checkRangeGistRewrite's own wrapper).
            return wrapValueIdentity(expr);
        default:
            return null;
        }
    }

    /**
     * ① Identity-wrapper catalog. Returns {@code expr} re-expressed through one of four provably
     * value-identity, type-generic, NULL-preserving, non-sargable forms (picked uniformly at random):
     *   least(e,e) / greatest(e,e)  — min/max of a value with itself = itself (incl NULL -> NULL).
     *   coalesce(e,e)               — first non-null of (e,e); coalesce(NULL,NULL)=NULL=e, else e.
     *   CASE WHEN true THEN e END    — the only branch is taken for every row -> e for every value incl NULL.
     * All four leave the row set identical to {@code expr}; none is matched to a plain-column btree/GIN/GiST
     * index by the planner, so armB is forced onto a Seq Scan. SOUNDNESS: if PG ever constant-folds coalesce
     * or the CASE back to the bare column and re-acquires the index, the caller's armB gate
     * ({@code Seq Scan && !Index}) simply fails and the round is skipped — a folded wrapper lowers yield,
     * it can never produce a false positive. Rendering (type/collation/padding) is preserved by all four:
     * least/greatest/coalesce return the SAME type as their args; CASE returns the THEN-branch type.
     */
    // NOTE: the 4th historical form "(CASE WHEN true THEN x END)" was REMOVED — PG's constant-condition
    // simplification folds it back to x in EVERY context (WHERE/ORDER BY/GROUP BY, measured on 18.6), so
    // armB re-acquired the index under test and the index-independence gate silently discarded the round
    // (~25% of all wrapper draws wasted across the WHERE/ORD shape families). The three remaining forms are
    // all value-identity (incl. NULL) and planner-non-matchable.
    private String wrapValueIdentity(String expr) {
        switch ((int) Randomly.getNotCachedInteger(0, 3)) {
        case 0:
            return "least(" + expr + ", " + expr + ")";
        case 1:
            return "greatest(" + expr + ", " + expr + ")";
        default:
            return "coalesce(" + expr + ", " + expr + ")";
        }
    }

    /**
     * Build a DEEP, deterministic boolean predicate over {@code table}'s columns, returned as a
     * two-element array {armA-render, armB-render}. The two renders are produced in lockstep and
     * differ ONLY in that every reference to {@code targetCol} is the bare column in [0] and the
     * value-identity wrapper ({@link #nonSargableWrapFor}) in [1]. Because the wrapper is an exact
     * value-identity (incl. NULL) and every other token is byte-identical, the two predicates
     * evaluate to the identical 3-valued truth for every row -> identical row sets by construction.
     * The builder emits ONLY column refs, data-aware constant literals, comparison / logical
     * operators, and IMMUTABLE functions (abs/lower/upper/length) -- never a volatile or
     * time-dependent function -- so both arms (two SEPARATE executions) embed identical literals and
     * evaluate identically. Returns null if no usable operand/constant could be produced.
     */
    private String[] deepFilterArms(PostgresTable table, PostgresColumn targetCol, int depth) {
        String targetName = targetCol.getName();
        String targetWrap = nonSargableWrapFor(targetCol, targetName);
        if (targetWrap == null) return null;
        List<PostgresColumn> pool = new ArrayList<>(wrappableColumns(table));
        // The residual AND-tree is pure heap-tuple variation; it must NOT reference ANY indexed column,
        // otherwise armB's seq-scan predicate could re-acquire an index (yield loss — the armB gate then
        // discards the round) or armA could migrate the clause asymmetrically into an Index Cond. Restrict
        // the leaf pool to the NON-INDEXED columns c2 / c4 / c6 (no btree/gin/gist/brin key references them),
        // so the deep tree is a plain Filter identical in both arms that never collides with any index. The
        // explicit target exclusion below is then a defensive no-op (the target is always an indexed column).
        java.util.Set<String> nonIndexed = new java.util.HashSet<>(java.util.Arrays.asList("c2", "c4", "c6"));
        pool.removeIf(c -> !nonIndexed.contains(c.getName()));
        pool.removeIf(c -> c.getName().equals(targetName));
        if (pool.isEmpty()) return null;
        return buildBoolExpr(table, targetCol, targetName, targetWrap, pool, depth);
    }

    /**
     * With ~50% probability, AND a deep deterministic sub-predicate (see {@link #deepFilterArms}) onto
     * both arms, returning the possibly-extended {armA, armB}. A no-op (returns the inputs unchanged) when
     * the coin declines or the builder returns null. The 50% keeps each shape's proven simple form in
     * rotation as a baseline alongside the deep variant.
     *
     * PRECONDITION: armA/armB must END in their WHERE predicate (no trailing ORDER BY/LIMIT/GROUP BY), so
     * appending " AND (...)" is well-formed. SOUNDNESS: {@code targetCol} MUST be a column whose every
     * reference armB already wraps in a value-identity function; deepFilterArms wraps exactly that column's
     * refs in the deep part too, so armB stays armA with target-col refs wrapped node-for-node → identical
     * 3-valued truth per row → identical row set. The deep part becomes a Filter/Recheck in armA (it does
     * not disturb the top-level Index Cond on the shape's indexable conjunct).
     */
    private String[] maybeDeepen(PostgresTable table, PostgresColumn targetCol, String armA, String armB) {
        if (!DEEP_FORCE && !Randomly.getBoolean()) return new String[] { armA, armB };
        String[] deep = deepFilterArms(table, targetCol, (int) Randomly.getNotCachedInteger(DEEP_MIN, DEEP_MAX));
        if (deep == null) return new String[] { armA, armB };
        return new String[] { armA + " AND (" + deep[0] + ")", armB + " AND (" + deep[1] + ")" };
    }

    /**
     * ③ convenience wrapper: deepen a single-table WHERE-ending shape keyed on {@code c0} as the deep target,
     * for shapes whose own indexed key (gj/ga/gp/jsonb/…) is not a plain {@link #nonSargableWrapFor} operand.
     * SOUND for ANY such shape: {@link #deepFilterArms} restricts the leaf pool to the NON-INDEXED columns
     * c2/c4/c6 and excludes the target, so the appended AND-tree is byte-identical in BOTH arms (it never
     * references the shape's index key) — armB therefore stays armA with ONLY the key wrapped, and armB's
     * deep Filter cannot acquire an index (c2/c4/c6 are keyless) so armB's Seq-Scan gate still holds. A no-op
     * (returns the inputs) when the table has no c0, or the coin / builder declines. c0 is pool-excluded so
     * passing it does not shrink the c2/c4/c6 pool.
     */
    private String[] maybeDeepenC0(PostgresTable table, String armA, String armB) {
        PostgresColumn c0 = table.getColumns().stream()
                .filter(cc -> "c0".equals(cc.getName())).findFirst().orElse(null);
        if (c0 == null) return new String[] { armA, armB };
        return maybeDeepen(table, c0, armA, armB);
    }

    /**
     * EXPERIMENTAL structural-envelope combinator (see the {@code idx.envelope} knob). Wraps BOTH arms in one
     * IDENTICAL, output-multiset-preserving (bijective) envelope chosen at random, so the index-ride point is
     * exercised inside a new plan context without perturbing the A/B differential. Callers MUST apply this
     * AFTER the complete arm (incl. any {@link #maybeDeepen}) is built and ONLY on WHERE-ending shapes whose
     * comparator is order-insensitive ({@link #compareValueIdentityStrict}); a reordering envelope on an
     * ordered comparator would be a false positive. Both envelopes are optimization fences, so the inner arm
     * is planned as-written and the shape's existing EXPLAIN string gate still matches the nested inner nodes.
     * A no-op (returns inputs unchanged) unless {@code -Didx.envelope=1} and the per-call coin fires.
     */
    private String[] applyEnvelope(String armA, String armB) {
        if (!ENVELOPE) return new String[] { armA, armB };
        if (!ENVELOPE_FORCE && Randomly.getNotCachedInteger(0, 100) >= ENVELOPE_PCT) {
            return new String[] { armA, armB };
        }
        // Both envelopes keep the inner scan nodes (idxName / Seq Scan) visible to the string gate and preserve
        // the output multiset 1:1 (they only buffer / fence, never filter or aggregate).
        if (Randomly.getBoolean()) {
            // MATERIALIZED CTE: a hard optimization fence — inner planned standalone as-written, rows buffered.
            return new String[] {
                    "WITH __env AS MATERIALIZED (" + armA + ") SELECT * FROM __env",
                    "WITH __env AS MATERIALIZED (" + armB + ") SELECT * FROM __env" };
        }
        // OFFSET 0 fenced subquery: PostgreSQL never pulls up a subquery carrying OFFSET, so the inner arm is
        // its own planning island (adds a Limit/Subquery-Scan node); OFFSET 0 removes zero rows → bijective.
        return new String[] {
                "SELECT * FROM (" + armA + " OFFSET 0) __env",
                "SELECT * FROM (" + armB + " OFFSET 0) __env" };
    }

    private String[] buildBoolExpr(PostgresTable table, PostgresColumn targetCol, String targetName,
            String targetWrap, List<PostgresColumn> pool, int depth) {
        if (depth <= 0 || Randomly.getNotCachedInteger(0, 100) < DEEP_EARLYSTOP) {
            return buildLeaf(table, targetName, targetWrap, pool);
        }
        if ((int) Randomly.getNotCachedInteger(0, 3) == 0) { // NOT
            String[] c = buildBoolExpr(table, targetCol, targetName, targetWrap, pool, depth - 1);
            if (c == null) return null;
            return new String[] { "(NOT " + c[0] + ")", "(NOT " + c[1] + ")" };
        }
        String[] l = buildBoolExpr(table, targetCol, targetName, targetWrap, pool, depth - 1); // AND / OR
        String[] r = buildBoolExpr(table, targetCol, targetName, targetWrap, pool, depth - 1);
        if (l == null || r == null) return null;
        String bop = Randomly.getBoolean() ? " AND " : " OR ";
        return new String[] { "(" + l[0] + bop + r[0] + ")", "(" + l[1] + bop + r[1] + ")" };
    }

    /** One deterministic leaf; the operand is a random pooled column (wrapped in [1] iff it is the target). */
    private String[] buildLeaf(PostgresTable table, String targetName, String targetWrap,
            List<PostgresColumn> pool) {
        PostgresColumn operand = Randomly.fromList(pool);
        boolean isTarget = operand.getName().equals(targetName);
        String aRef = operand.getName();
        String bRef = isTarget ? targetWrap : operand.getName();
        String tbl = table.getName();

        int kind = (int) Randomly.getNotCachedInteger(0, 5); // 0..4
        if (kind == 0) { // IS [NOT] NULL -- no constant needed, always deterministic/safe
            String nn = Randomly.getBoolean() ? " IS NULL" : " IS NOT NULL";
            return new String[] { aRef + nn, bRef + nn };
        }
        if (kind == 4) { // immutable-function comparison (expression-recheck depth)
            String[] fn = buildFuncLeaf(tbl, operand, aRef, bRef);
            if (fn != null) return fn;
            // else fall through to a plain comparison
        }
        String v = generateDataAwareValueForType(tbl, operand);
        if (v == null || "NULL".equalsIgnoreCase(v)) { // value-identity-safe deterministic fallback
            return new String[] { aRef + " IS NOT NULL", bRef + " IS NOT NULL" };
        }
        if (kind == 2) { // BETWEEN -- order the bounds via LEAST/GREATEST so a reversed (v>v2) pair is a
                         // real two-sided range, not a silent no-op that empties the result. Type-generic,
                         // server-side, and identical in both arms.
            String v2 = generateDataAwareValueForType(tbl, operand);
            if (v2 != null && !"NULL".equalsIgnoreCase(v2)) {
                String loB = "LEAST(" + v + ", " + v2 + ")";
                String hiB = "GREATEST(" + v + ", " + v2 + ")";
                return new String[] { aRef + " BETWEEN " + loB + " AND " + hiB,
                        bRef + " BETWEEN " + loB + " AND " + hiB };
            }
        } else if (kind == 3) { // IN-list
            String v2 = generateDataAwareValueForType(tbl, operand);
            String v3 = generateDataAwareValueForType(tbl, operand);
            if (v2 != null && v3 != null && !"NULL".equalsIgnoreCase(v2) && !"NULL".equalsIgnoreCase(v3)) {
                String list = " IN (" + v + ", " + v2 + ", " + v3 + ")";
                return new String[] { aRef + list, bRef + list };
            }
        }
        String op = Randomly.fromOptions("=", "<>", ">", "<", ">=", "<="); // kind 1, or BETWEEN/IN fallback
        return new String[] { aRef + " " + op + " " + v, bRef + " " + op + " " + v };
    }

    /** Immutable-function comparison leaf, or null if the operand type has no safe form. */
    private String[] buildFuncLeaf(String tbl, PostgresColumn operand, String aRef, String bRef) {
        if (isNumericType(operand)) {
            String v = generateDataAwareValueForType(tbl, operand);
            if (v == null || "NULL".equalsIgnoreCase(v)) return null;
            String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
            return new String[] { "abs(" + aRef + ") " + op + " " + v, "abs(" + bRef + ") " + op + " " + v };
        }
        if (operand.getType() == PostgresDataType.TEXT) {
            if ((int) Randomly.getNotCachedInteger(0, 3) == 0) { // length(ref) <op> smallint literal
                long n = Randomly.getNotCachedInteger(0, 16);
                String op = Randomly.fromOptions("=", ">", "<", ">=", "<=");
                return new String[] { "length(" + aRef + ") " + op + " " + n,
                        "length(" + bRef + ") " + op + " " + n };
            }
            String fn = Randomly.getBoolean() ? "lower" : "upper";
            String v = generateDataAwareValueForType(tbl, operand);
            if (v == null || "NULL".equalsIgnoreCase(v)) return null;
            String op = Randomly.getBoolean() ? "=" : "<>";
            return new String[] { fn + "(" + aRef + ") " + op + " " + v,
                    fn + "(" + bRef + ") " + op + " " + v };
        }
        return null;
    }

    // ==================== Mode 26: Index-Provided-Sort / ORD (VLDB PG port, Phase 2) ====================

    /**
     * Mode 26 (isolated): index-provided-sort differential.
     * armA `SELECT col FROM t ORDER BY col dir NULLS n LIMIT k` gets its order FROM the
     * tested index (Index/Index-Only Scan, no Sort node).
     * armB `SELECT col FROM t ORDER BY f(col) dir NULLS n LIMIT k`, where f is an
     * order-preserving value-identity wrapper the planner cannot match to the index, must
     * add an explicit Sort over an index-independent path (Seq Scan on PG 17.6). Both arms
     * project exactly the ORDER BY key column, so any two rows tied on the key are
     * byte-identical in output ⇒ a positional comparison cannot false-positive on a
     * legitimate tie reordering, and LIMIT truncation of a tie group yields identical rows.
     * Any surviving positional mismatch is a real index-provided-sort bug.
     *
     * Orthogonal to NoREC/TLP/MOZI: the differential axis is the ORDER BY expression, NOT a
     * GUC/optimizer-config flip. No GUC is set — the LIMIT creates the cost asymmetry that
     * naturally routes armA through the index and armB through a Seq Scan + Sort. Mirrors
     * CRDB mode 28's ORD shape; the {@code @idx}/{@code @primary} hints (unavailable on PG)
     * are replaced by the non-matchable wrapper + the EXPLAIN gate.
     */
    private void checkOrderByIndexRewrite() throws Exception {
        PostgresSchema schema = globalState.getSchema();
        List<PostgresTable> tables = schema.getDatabaseTables();
        if (tables.isEmpty()) return;
        PostgresTable table = Randomly.fromList(tables);
        if (table.isView()) return;
        if (table.getName().startsWith("idx_gs")) return; // dedicated to case 53 (see ITEM C)

        // Order-shape-safe columns: value-equality must ⟹ identical rendering. Only INT and
        // BOOLEAN qualify (DECIMAL/FLOAT/REAL have -0/+0/NaN/1.0-vs-1.00 tie-render hazards;
        // TEXT needs COLLATE "C" — both deferred).
        List<PostgresColumn> candidates = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            if (orderWrapFor(col, col.getName()) != null) {
                candidates.add(col);
            }
        }
        if (candidates.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(candidates);
        String tbl = table.getName();
        String colName = col.getName();

        // ONE wrapper instance threaded through armB (do NOT recompute — desync risk).
        String wrapped = orderWrapFor(col, colName);
        if (wrapped == null) return;

        boolean asc = Randomly.getBoolean();
        String dir = asc ? "ASC" : "DESC";
        String nulls = Randomly.getBoolean() ? "FIRST" : "LAST";
        // Create the index with the EXACT ordering spec we query, so armA matches it and can
        // provide the order without a Sort. Name encodes dir+nulls to keep IF NOT EXISTS
        // reuse correct across the 4 combos.
        String idxName = "nsord_" + tbl + "_" + colName + "_" + (asc ? "a" : "d") + (nulls.equals("FIRST") ? "f" : "l");
        long k = globalState.getRandomly().getInteger(1, 100);
        // B3 depth: ~50% of rounds prepend an identical OFFSET m (0..20) before the LIMIT in BOTH arms. OFFSET
        // is absorbed by the Limit node — it adds NO Sort, so armA's `!hasSortNode` gate is unaffected and armB
        // still carries its explicit Sort; the top-k skip exercises the index-ordered-scan early-stop + skip path.
        // Byte-identical in both arms (only the ORDER-BY key is wrapped), so FP-safety is untouched; the FAULT
        // direction-flip still perturbs the surviving window.
        String limOff = " LIMIT " + k + (Randomly.getBoolean()
                ? " OFFSET " + globalState.getRandomly().getInteger(0, 21) : "");
        String armA = "SELECT " + colName + " FROM " + tbl
                + " ORDER BY " + colName + " " + dir + " NULLS " + nulls + limOff;
        // FAULT self-proof (ships OFF): flip armB's sort direction so the top-k row sequence diverges from armA
        // while the wrapper still forces an explicit Sort (the armB gate still accepts). armB ≡ armA when OFF.
        String dirB = FAULT ? (asc ? "DESC" : "ASC") : dir;
        String armB = "SELECT " + colName + " FROM " + tbl
                + " ORDER BY " + wrapped + " " + dirB + " NULLS " + nulls + limOff;

        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX IF NOT EXISTS " + idxName + " ON " + tbl
                    + " (" + colName + " " + dir + " NULLS " + nulls + ");", errors, true));
            analyzeTolerant(tbl);

            // EXPLAIN gate (no GUC): armA order comes FROM the tested index (references idx,
            // no Sort); armB has an explicit Sort and does NOT reference the tested index
            // (ground-truth order not derived from the index-under-test). Else discard.
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            boolean armAIndexProvided = planA.contains(idxName) && !hasSortNode(planA);
            boolean armBExplicitSort = hasSortNode(planB) && !planB.contains(idxName);
            if (!armAIndexProvided || !armBExplicitSort) return;

            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return; // discard per-arm DDL/runtime errors — not the bug axis
        }
        if (rA == null || rB == null) return;

        log(armA);
        log(armB);
        // Positional (order-preserving) comparison — self-throws AssertionError on mismatch.
        compareResultsOrdered(rA, rB, armA, armB, "PG_NONSARGABLE_ORD", true);
    }

    /**
     * Order-preserving value-identity wrapper for the ORDER BY key, or null if the type is
     * not order-shape-safe. least/greatest(c,c) ≡ c in value, order, AND rendering (incl.
     * NULL) for INT and BOOLEAN — validated on PG 17.6. Other types are excluded (see
     * {@link #checkOrderByIndexRewrite}).
     */
    private String orderWrapFor(PostgresColumn col, String expr) {
        switch (col.getType()) {
        case INT:
        case BOOLEAN:
            return Randomly.getBoolean()
                    ? "least(" + expr + ", " + expr + ")"
                    : "greatest(" + expr + ", " + expr + ")";
        default:
            return null;
        }
    }

    /**
     * Positional (order-preserving) result comparison for the index-provided-sort shape.
     * Unlike {@link #compareResultsSorted} (which sorts both sides) it compares element by
     * element — the only way to catch an ordering-only divergence. Soundness against ORDER
     * BY ties is guaranteed by the caller projecting exactly the ordered column, so a
     * surviving positional mismatch is a real bug, reported by throwing an AssertionError
     * (same bug-reporting convention the sorted comparator uses via assumeResultSetsAreEqual).
     */
    /**
     * Ordered comparator for index-provided-sort shapes. armA takes its row order from the index; armB applies
     * an explicit sort over value-identical rows. A1 guardrail: a positional difference is a bug ONLY when the
     * sort is a TOTAL order. If the caller cannot guarantee a unique tiebreak, rows that tie on the sort key may
     * legitimately come back in a different relative order from the two paths — that is NOT an index bug, and
     * throwing on it would be a false positive. So:
     *   - different multiset (sizes or contents differ as a set) → always a genuine row-set bug → throw;
     *   - same multiset, different order, {@code totalOrder==true}  → genuine index-ordering bug → throw
     *     (caller asserts a unique tiebreak, so the order is deterministic and must match);
     *   - same multiset, different order, {@code totalOrder==false} → tie-order ambiguity only → filter + pass.
     * With {@code totalOrder==true} this is byte-for-byte the old throw-on-any-positional-diff behavior, so every
     * existing caller (all carry the unique {@code cb} tiebreak) is unchanged; the guardrail only protects future
     * callers that pass {@code false}.
     */
    private void compareResultsOrdered(List<String> r1, List<String> r2, String queryA, String queryB,
            String mode, boolean totalOrder) {
        covBump(mode);
        boolean equalInOrder = r1.size() == r2.size();
        if (equalInOrder) {
            for (int i = 0; i < r1.size(); i++) {
                String a = r1.get(i);
                String b = r2.get(i);
                if (a == null ? b != null : !a.equals(b)) {
                    equalInOrder = false;
                    break;
                }
            }
        }
        if (equalInOrder) {
            return;
        }
        // Positional diff. Separate a real row-set bug from a mere tie-order ambiguity by comparing multisets.
        List<String> s1 = new java.util.ArrayList<>(r1);
        List<String> s2 = new java.util.ArrayList<>(r2);
        java.util.Comparator<String> cmp = java.util.Comparator.nullsFirst(java.util.Comparator.naturalOrder());
        java.util.Collections.sort(s1, cmp);
        java.util.Collections.sort(s2, cmp);
        boolean sameMultiset = s1.equals(s2);
        if (sameMultiset && !totalOrder) {
            // Rows tie on the sort key and no unique tiebreak was asserted → relative order is unconstrained →
            // not a bug. Record the filtered difference and pass (mirrors lastCompareFiltered elsewhere).
            lastCompareFiltered = true;
            return;
        }
        throw new AssertionError("PG index-provided-sort " + (sameMultiset ? "order" : "row-set")
                + " mismatch [" + mode + "]"
                + System.lineSeparator() + "armA (index-provided order): " + queryA
                + System.lineSeparator() + "armB (explicit sort): " + queryB
                + System.lineSeparator() + "armA rows: " + r1
                + System.lineSeparator() + "armB rows: " + r2);
    }

    // ==================== Mode 28 sound re-casts of the legacy GUC-forcing modes ====================
    // Each method below re-implements one legacy index scenario using the sound skeleton (armA uses
    // the index; armB wraps the indexed expr/col in a value-identity function → index-independent
    // path; EXPLAIN-gated; NO GUC; provably-equal rows). All discard on any missing candidate / gate
    // miss / caught exception and only ever throw via the comparator on a genuine mismatch.

    /** Legacy mode 13: partial index predicate-implication. */
    private void checkPartialIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        String v = generateDataAwareValueForType(tbl, col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;

        String pred = colName + " IS NOT NULL";
        String idxName = "nsp_" + tbl + "_" + colName;
        // FAULT self-proof (was inert — only maybeDeepen varied armB): NOT-wrap armB's (already
        // non-sargable) predicate so its row set diverges while the wrapped LHS keeps armB a Seq Scan.
        // Ships OFF ⇒ armB ≡ armA. This complements case 34's strict-implication path.
        // ~50% of rounds use a multi-row RANGE instead of a single equality; least/greatest on the two
        // literals guarantees lo≤hi type-agnostically, and the wrap stays on the COLUMN only (value-identity).
        String primA;
        String primB;
        if (Randomly.getBoolean()) {
            String v2 = generateDataAwareValueForType(tbl, col);
            if (v2 == null || "NULL".equalsIgnoreCase(v2)) v2 = v;
            String lo = "least(" + v + ", " + v2 + ")";
            String hi = "greatest(" + v + ", " + v2 + ")";
            primA = colName + " >= " + lo + " AND " + colName + " <= " + hi;
            primB = wrapped + " >= " + lo + " AND " + wrapped + " <= " + hi;
        } else {
            primA = colName + " = " + v;
            primB = wrapped + " = " + v;
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + pred + " AND (" + primA + ")";
        String armB = "SELECT * FROM " + tbl + " WHERE " + pred + " AND ("
                + (FAULT ? "NOT (" + primB + ")" : primB) + ")";
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + colName + ") WHERE " + pred + ";", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_PARTIAL");
    }

    /**
     * Mode-28 PARTIAL-INDEX PREDICATE IMPLICATION (case 34). Unlike case 2 (checkPartialIndexRewrite), which
     * sets the index WHERE = the query predicate verbatim (no proving needed), this shape makes the query
     * predicate STRICTLY IMPLY but DIFFER FROM the index WHERE, forcing PostgreSQL's predicate-implication
     * prover (predtest.c) to admit the partial index. The partial index is {@code nspi_<tbl>_c0 ON (c0)
     * WHERE c0 > lo}; the query predicate is {@code c0 > hi} with {@code hi > lo}, which strictly implies
     * {@code c0 > lo} (narrower). armA rides the partial index (the planner choosing an index whose WHERE
     * differs from the query WHERE is itself proof it ran implication proving); armB wraps the sole c0 ref in
     * {@code least(c0,c0)} (not index-matchable) → a heap Seq Scan. {@code least(c0,c0) ≡ c0} for every row
     * incl. NULL (3VL-false both sides) ⇒ the row sets are provably equal ⇒ any mismatch is a real
     * index/implication bug. compareValueIdentityStrict. FAULT shifts armB to {@code least(c0,c0) + 1 > hi}
     * (still non-sargable → armB gate still Seq Scan) → the row set shifts → must throw.
     */
    private void checkPartialImplicationRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c0")) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        // Sample two distinct data-aware ints, order lo < hi. The query bound (hi) is strictly above the
        // index bound (lo), so the query predicate c0 > hi strictly implies the index WHERE c0 > lo.
        String v1s = generateDataAwareValueForType(tbl, c0col);
        String v2s = generateDataAwareValueForType(tbl, c0col);
        if (v1s == null || v2s == null) return;
        long lo;
        long hi;
        try {
            long a = Long.parseLong(v1s.trim());
            long b = Long.parseLong(v2s.trim());
            if (a == b) return;
            lo = Math.min(a, b);
            hi = Math.max(a, b);
        } catch (NumberFormatException e) {
            return;
        }
        String idxName = "nspi_" + tbl + "_c0";
        String keyB = FAULT ? wrap + " + 1" : wrap;
        String armA = "SELECT * FROM " + tbl + " WHERE c0 > " + hi;
        String armB = "SELECT * FROM " + tbl + " WHERE " + keyB + " > " + hi;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c0) WHERE c0 > " + lo + ";", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride THIS partial index whose WHERE (c0 > lo) DIFFERS from the query WHERE (c0 > hi) —
            // the planner using it is proof it proved implication. armB's wrapped key can't match → Seq Scan.
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_PARTIMPL");
    }

    /** Legacy mode 12: expression index (lower(col) for TEXT, abs(col) for numeric). */
    private void checkExpressionIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        String v = generateDataAwareValueForType(tbl, col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;

        // Expression-index differential. Numeric path rides abs(col) and ~50% uses a multi-row BETWEEN range on
        // the expression key (absorbs the former case-41 EXPRIDX range variant); text path rides lower(col)=v.
        String expr;
        String predA;      // armA predicate — rides the functional index as an Index Cond
        String predBcore;  // armB predicate (pre-NOT) — wrapped expression the planner cannot match → Seq Scan
        if (col.getType() == PostgresDataType.TEXT) {
            expr = "lower(" + colName + ")";
            String wrapped = nonSargableWrapFor(col, expr); // (lower(c)||'')≡lower(c)
            if (wrapped == null) return;
            String rhs = "lower(" + v + ")";
            predA = expr + " = " + rhs;
            predBcore = wrapped + " = " + rhs;
        } else if (isNumericType(col)) {
            expr = "abs(" + colName + ")";
            String wrapped = nonSargableWrapFor(col, expr); // least(abs(c),abs(c))≡abs(c)
            if (wrapped == null) return;
            Long parsed = null;
            try { parsed = Math.abs(Long.parseLong(v.trim())); } catch (Exception ignore) { }
            if (parsed != null && Randomly.getBoolean()) {
                // RANGE variant: multi-row BETWEEN on the expression key (abs is non-negative so bounds stay ≥0).
                long window = globalState.getRandomly().getInteger(0, 500);
                long lo = Math.max(0, parsed - window);
                long hi = parsed + window;
                predA = expr + " BETWEEN " + lo + " AND " + hi;
                predBcore = wrapped + " BETWEEN " + lo + " AND " + hi;
            } else {
                String rhs = "abs(" + v + ")";
                predA = expr + " = " + rhs;
                predBcore = wrapped + " = " + rhs;
            }
        } else {
            return;
        }

        String idxName = "nse_" + tbl + "_" + colName;
        String armA = "SELECT * FROM " + tbl + " WHERE " + predA;
        // FAULT self-proof (ships OFF): NOT-wrap armB's wrapped-expression predicate so its row set diverges
        // while the wrapped LHS keeps armB a Seq Scan (the armB gate still accepts). armB ≡ armA when OFF.
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + predBcore + ")" : predBcore);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + expr + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_EXPR");
    }

    /**
     * Mode 28 shape: BRIN block-range bitmap scan on the physically-correlated {@code cb} column.
     *
     * BRIN only prunes when the column value is correlated with heap order, so this shape restricts
     * itself to the {@code idx_t<n>} tables' {@code cb} column (GENERATED ALWAYS AS IDENTITY →
     * correlation ~1, never NULL; verified 0.9999) which carries a prebuilt BRIN index
     * {@code idx_<n>_cbbrin WITH (pages_per_range=1)}. Random-valued columns never get a BRIN plan
     * (measured), so the legacy "pick any numeric column, default pages_per_range" form was a dead
     * shape — its EXPLAIN gate essentially never passed. Targeting the correlated column is what
     * makes BRIN actually selectable and testable.
     *
     * armA `cb BETWEEN v AND (v + W)` over a NARROW band → Bitmap Index Scan on the BRIN + lossy
     * Recheck Cond (measured: BRIN beats a Seq Scan up to ~8% selectivity; a wide band flips to Seq
     * Scan and the gate discards the round, so the band is kept narrow: W ∈ [3,50] over ~1000+ rows).
     * armB wraps {@code cb} in the exact value-identity {@code least/greatest(cb,cb)} the planner
     * cannot match → Seq Scan (index-independent ground truth). {@code cb} is never NULL so
     * {@code least(cb,cb) ≡ cb} exactly, and the band literals are embedded identically in both arms
     * → identical row sets by construction; any surviving mismatch is a real BRIN bug (lossy recheck,
     * summarization, block-range maintenance). NO GUC → axis stays orthogonal to NoREC/TLP/MOZI.
     */
    private void checkBrinRewrite() throws Exception {
        PostgresTable table = pickBrinCbTable();
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("cb".equals(c.getName())) { col = c; break; }
        }
        if (col == null) return;
        String colName = "cb";
        // The prebuilt BRIN on cb (see createIndexFriendlyTables): idx_t<n> → idx_<n>_cbbrin.
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_cbbrin";
        // least/greatest(cb,cb): exact value-identity (cb is NOT NULL), non-sargable → armB Seq Scan.
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        // Anchor the band at a real cb value and keep it NARROW: BRIN only beats a Seq Scan at high
        // selectivity. A wide band flips the planner to Seq Scan and the gate discards the round.
        // The band bounds are constant expressions embedded IDENTICALLY in both arms (v + W is folded
        // the same way in each), so soundness is preserved.
        String v = generateDataAwareValueForType(tbl, col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;
        long w = Randomly.getNotCachedInteger(3, 50);
        String hi = "(" + v + " + " + w + ")";
        // Operator pool: each maps to a distinct brin_minmax_consistent strategy (less/lessequal/equal-band/
        // greaterequal/greater). The RHS (v, hi) is a constant expression embedded BYTE-IDENTICALLY in both
        // arms; only the LHS differs (cb vs least/greatest(cb,cb)), so soundness is unchanged. Open-ended
        // operators are higher-selectivity only near cb's extremes, so some rounds are discarded by the
        // Bitmap-Index-Scan gate below — a yield cost, never an FP.
        String opForm = Randomly.fromOptions("BETWEEN", "<", "<=", ">", ">=");
        // FAULT self-proof (ships OFF ⇒ vB≡v, hiB≡hi, byte-identical RHS): shift ONLY armB's RHS constant far
        // past cb's IDENTITY range so armB's row set differs from armA's, while the wrapped LHS keeps armB a
        // Seq Scan (the armB gate still accepts). This perturbs the comparison constant, not the identity.
        String vB = FAULT ? "(" + v + " + 1000000)" : v;
        String hiB = FAULT ? "(" + hi + " + 1000000)" : hi;
        String predA;
        String predB;
        if ("BETWEEN".equals(opForm)) {
            predA = colName + " BETWEEN " + v + " AND " + hi;
            predB = wrapped + " BETWEEN " + vB + " AND " + hiB;
        } else {
            predA = colName + " " + opForm + " " + v;
            predB = wrapped + " " + opForm + " " + vB;
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + predA;
        String armB = "SELECT * FROM " + tbl + " WHERE " + predB;
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal the BRIN index (idempotent) in case a random DDL statement dropped it.
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING brin(" + colName + ") WITH (pages_per_range=1);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride the BRIN (a Bitmap Index Scan on the pages_per_range=1 BRIN index);
            // otherwise the band was too wide / stats stale and the planner chose Seq Scan.
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            // armB must be index-independent ground truth.
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_BRIN");
    }

    /**
     * BRIN bloom-opclass equality (case 21). Distinct from {@link #checkBrinRewrite} (minmax opclass,
     * range BETWEEN): the {@code int4_bloom_ops} opclass (built-in PG 14+) summarizes each block range
     * with a Bloom filter and serves EQUALITY only. Targets the dedicated {@code cu} column, whose SOLE
     * index is the prebuilt bloom BRIN {@code idx_<n>_cubloom} — cu has NO btree and NO minmax BRIN, so
     * `cu = v` has nothing else to ride and the planner MUST choose the bloom BRIN (a Bitmap Index Scan).
     * (The earlier cb target was gate-starved: cb is monotonic, so its minmax {@code cbbrin} always
     * out-costs a bloom filter for equality — the bloom plan was never chosen.) cu is uncorrelated,
     * moderate-cardinality (~4000 distinct → ~3 rows/value), so the bloom prunes to a few pages. {@code v}
     * is sampled from an actual heap cu so armA reliably matches ≥1 row (gate + FAULT fire). armB wraps cu
     * in the exact value-identity {@code least/greatest(cu,cu)} (cu is NOT NULL via DEFAULT) → a pure heap
     * Seq Scan. Row sets provably equal → any mismatch is a real BRIN-bloom bug. No deepening (a deep
     * scalar predicate could reintroduce a Seq Scan on armA and lose the gate; keep it simple).
     */
    private void checkBrinBloomRewrite() throws Exception {
        PostgresTable table = pickBrinCbTable();
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("cu".equals(c.getName())) { col = c; break; }
        }
        if (col == null) return;
        String colName = "cu";
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_cubloom";
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        // Sample up to 4 ACTUAL cu values so armA matches ≥1 row (so the gate passes and the FAULT NOT-wrap set
        // genuinely differs); fall back to a bounded random int in cu's range.
        java.util.List<Long> vs = new java.util.ArrayList<>();
        try {
            List<String> vr = executeQuery(
                    "SELECT cu FROM " + tbl + " WHERE cu IS NOT NULL ORDER BY random() LIMIT 4");
            if (vr != null) {
                for (String s : vr) {
                    if (s != null && !s.trim().isEmpty()) {
                        vs.add(Long.parseLong(s.trim()));
                    }
                }
            }
        } catch (Exception e) {
            return;
        }
        if (vs.isEmpty()) {
            vs.add(Randomly.getNotCachedInteger(0, 3999));
        }
        // Variant selector: single equality (as before), IN-list, or OR-chain. The bloom opclass answers each
        // equality; the planner OR-s the per-value bitmaps under one Bitmap Index Scan on idx_<t>_cubloom. armB wraps
        // the key in EVERY term (least(cu,cu)≡cu) → not index-matchable → Seq Scan. All variants are value-identity-
        // sound; a wide IN that the planner serves by Seq Scan is simply discarded by the gate (sound-but-lower-yield).
        int variant = (vs.size() >= 2) ? Randomly.fromOptions(0, 1, 2) : 0;
        String predA;
        String primB;
        if (variant == 1) { // IN-list
            StringBuilder inList = new StringBuilder();
            for (int i = 0; i < vs.size(); i++) {
                if (i > 0) inList.append(", ");
                inList.append(vs.get(i));
            }
            predA = colName + " IN (" + inList + ")";
            primB = wrapped + " IN (" + inList + ")";
        } else if (variant == 2) { // OR-chain
            StringBuilder orA = new StringBuilder();
            StringBuilder orB = new StringBuilder();
            for (int i = 0; i < vs.size(); i++) {
                if (i > 0) { orA.append(" OR "); orB.append(" OR "); }
                orA.append(colName).append(" = ").append(vs.get(i));
                orB.append(wrapped).append(" = ").append(vs.get(i));
            }
            predA = orA.toString();
            primB = orB.toString();
        } else { // single equality
            predA = colName + " = " + vs.get(0);
            primB = wrapped + " = " + vs.get(0);
        }
        // FAULT self-proof (ships OFF): NOT-wrap armB's predicate so its row set diverges while the wrapped LHS
        // keeps armB a Seq Scan (the armB gate still accepts). armB ≡ armA when OFF.
        String armA = "SELECT * FROM " + tbl + " WHERE " + predA;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: a prior shape in this DB may have dropped this prebuilt index; IF NOT EXISTS re-creates it.
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING brin(" + colName + " int4_bloom_ops) WITH (pages_per_range=1);",
                    errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_BRINBLOOM");
    }

    /**
     * Pick an {@code idx_t<n>} table carrying the dedicated GIN targets {@code gj} (jsonb) / {@code ga}
     * (int[]). Every idx_t table has them (see createIndexFriendlyTables), but a random DDL statement or
     * a schema race could leave a stale table without the column, so we verify the column is present.
     */
    private PostgresTable pickGinTable(String colName) {
        List<PostgresTable> tables = globalState.getSchema().getDatabaseTables();
        if (tables.isEmpty()) return null;
        List<PostgresTable> hits = new ArrayList<>();
        for (PostgresTable t : tables) {
            if (t.isView() || !t.getName().startsWith("idx_t")) continue;
            for (PostgresColumn c : t.getColumns()) {
                if (colName.equals(c.getName())) { hits.add(t); break; }
            }
        }
        return hits.isEmpty() ? null : Randomly.fromList(hits);
    }

    /**
     * GIN over the jsonb column {@code gj} (case 16). armA rides the {@code idx_<n>_gjgin} GIN index via the
     * key-existence predicate {@code gj ? 'gN'} (a Bitmap Index Scan — GIN's only plan shape); armB wraps the
     * column in the exact value-identity {@code least(gj,gj)}, which the planner cannot match to a GIN index →
     * a pure heap Seq Scan (index-independent ground truth). The {@code ?} key-existence operator is
     * jsonb_ops-EXCLUSIVE — the {@code jsonb_path_ops} opclass (idx_<n>_gjpgin, built by case 19 on the SAME
     * column) does NOT index {@code ?}, so armA can only ride the jsonb_ops index; this is what revives the
     * shape, which previously used {@code @>} and lost every round to case 19's cheaper jsonb_path_ops index.
     * {@code least} on jsonb is well-defined (jsonb has a total btree order) and returns jsonb, so {@code ?}
     * still applies and the wrapper is an exact value-identity incl. NULL (a NULL gj yields SQL NULL under
     * both {@code ?} operands → 3VL-false in BOTH arms). Row sets provably equal → any mismatch is a real GIN
     * bug. The 'g<0..99>' key space (seeded in the gj DEFAULT) makes {@code gj ? 'gN'} ~1% selective
     * (index-worthy). NOTE: the single {@code ?} is sent literally (arms run via a plain java.sql.Statement,
     * not a PreparedStatement), so it is the jsonb operator, not a JDBC bind placeholder.
     */
    private void checkGinJsonbRewrite() throws Exception {
        PostgresTable table = pickGinTable("gj");
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_gjgin";
        long n = Randomly.getNotCachedInteger(0, 100);
        long m = Randomly.getNotCachedInteger(0, 100);
        // Operator pool over jsonb_ops GIN strategies: Exists(?)=9, ExistsAny(?|)=10, ExistsAll(?&)=11,
        // Contains(@>)=7 — each a distinct extractQuery searchMode + triConsistent branch the single `?`
        // never reached. `?&` pairs the random g-key with the universal "k" key (every row has "k") so
        // ExistsAll yields ~1% instead of ~0 (two distinct g-keys never co-occur in one row).
        String op = Randomly.fromOptions("?", "?|", "?&", "@>");
        String rhs;
        String rhsB; // identical to rhs under identity operation; shifted to a never-seeded key under FAULT.
        long nF = n + 1000;
        switch (op) {
        case "?|":
            rhs = "array['g" + n + "','g" + m + "']";
            rhsB = FAULT ? "array['g" + nF + "','g" + (m + 1000) + "']" : rhs;
            break;
        case "?&":
            rhs = "array['g" + n + "','k']";
            rhsB = FAULT ? "array['g" + nF + "','k']" : rhs;
            break;
        case "@>":
            // Two distinct containment value-paths over the same jsonb_ops GIN: the universal "k":int pair,
            // and the ~1% existence-key population {"gN": true}. The gN path exercises object containment on
            // a sparse boolean key (distinct from the ? / ?| / ?& key-existence strategies above).
            if (Randomly.getBoolean()) {
                rhs = "'{\"g" + n + "\": true}'";
                rhsB = FAULT ? "'{\"g" + nF + "\": true}'" : rhs;
            } else {
                rhs = "'{\"k\":" + n + "}'";
                rhsB = FAULT ? "'{\"k\":" + nF + "}'" : rhs;
            }
            break;
        default: // "?"
            rhs = "'g" + n + "'";
            rhsB = FAULT ? "'g" + nF + "'" : rhs;
            break;
        }
        String armA = "SELECT * FROM " + tbl + " WHERE gj " + op + " " + rhs;
        String armB = "SELECT * FROM " + tbl + " WHERE least(gj, gj) " + op + " " + rhsB;
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin(gj);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // GIN is accessed only via a Bitmap Index Scan; require the target index by name.
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GINJ");
    }

    /**
     * GIN over the int[] column {@code ga} (case 17). Mirror of {@link #checkGinJsonbRewrite}: armA rides
     * the {@code idx_<n>_gagin} GIN (array_ops) via {@code ga @> ARRAY[N]} element-containment; armB wraps
     * it in {@code least(ga,ga)} (exact value-identity — arrays have a total btree order — returning int[],
     * so {@code @>} still applies), which the planner cannot match to a GIN index → Seq Scan. Row sets
     * provably equal → any mismatch is a real GIN bug. N ∈ [0,99] matches the DEFAULT element space.
     */
    private void checkGinArrayRewrite() throws Exception {
        PostgresTable table = pickGinTable("ga");
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_gagin";
        long n = Randomly.getNotCachedInteger(0, 100);
        long m = Randomly.getNotCachedInteger(0, 100);
        long nF = n + 1000;
        // Operator pool over array_ops GIN strategies: Contains(@>), Overlap(&&) are the high-yield
        // distinct searchMode branches; ContainedBy(<@) and Equals(=) force GIN_SEARCH_MODE_ALL and are
        // low-yield (planner often declines → armA gated out, correct, just rare). All share TAG PG_NS_GINA.
        String op = Randomly.fromOptions("@>", "&&", "<@", "=");
        String c;
        String cB; // identical to c under identity operation; shifted to never-seeded elements under FAULT.
        if (op.equals("@>")) {
            c = "ARRAY[" + n + "]";
            cB = FAULT ? "ARRAY[" + nF + "]" : c;
        } else {
            c = "ARRAY[" + n + ", " + m + "]";
            cB = FAULT ? "ARRAY[" + nF + ", " + (m + 1000) + "]" : c;
        }
        String armA = "SELECT * FROM " + tbl + " WHERE ga " + op + " " + c;
        String armB = "SELECT * FROM " + tbl + " WHERE least(ga, ga) " + op + " " + cB;
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin(ga);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GINA");
    }

    /**
     * GIN over the jsonb column {@code gj} using the {@code jsonb_path_ops} opclass + a jsonpath predicate
     * (case 19). Complements {@link #checkGinJsonbRewrite} (default {@code jsonb_ops} + {@code @>}): the
     * {@code jsonb_path_ops} opclass hashes whole paths (a distinct extract/consistent implementation), and
     * the {@code @?} jsonpath-match operator is a different GIN entry point. armA rides a fresh
     * {@code idx_<n>_gjpgin} via {@code gj @? '$.k ? (@ == N)'} (a Bitmap Index Scan — GIN's only plan
     * shape); armB wraps the column in the exact value-identity {@code least(gj,gj)} (jsonb has a total
     * btree order → returns jsonb; a NULL gj yields SQL NULL on both operands → 3VL-false in BOTH arms),
     * which the planner cannot match to a GIN index → a pure heap Seq Scan. Row sets provably equal → any
     * mismatch is a real GIN bug. N ∈ [0,99] matches the DEFAULT key space so ~1% of rows hit. No
     * deepening (scalar comparisons are ill-typed against jsonb).
     */
    private void checkGinJsonbPathRewrite() throws Exception {
        PostgresTable table = pickGinTable("gj");
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_gjpgin";
        long n = Randomly.getNotCachedInteger(0, 100);
        long nB = FAULT ? n + 1 : n;
        // Operator pool over jsonb_path_ops: @? with an equality filter, @? with a range filter (distinct
        // extractQuery/triConsistent descent), and the @@ predicate operator (also served by jsonb_path_ops).
        // The jsonpath literal is the RHS, embedded identically in both arms when not faulting (nB == n), so
        // least(gj,gj) @<op> path is an exact identity → provably equal row sets. Under FAULT the armB path
        // value is shifted by +1 → armB matches a different row set → mismatch → the TAG throws.
        String op;
        String pathA;
        String pathB;
        String form = Randomly.fromOptions("eq", "ge", "pred");
        if ("eq".equals(form)) {
            op = "@?";
            pathA = "'$.k ? (@ == " + n + ")'";
            pathB = "'$.k ? (@ == " + nB + ")'";
        } else if ("ge".equals(form)) {
            op = "@?";
            pathA = "'$.k ? (@ >= " + n + ")'";
            pathB = "'$.k ? (@ >= " + nB + ")'";
        } else {
            op = "@@";
            pathA = "'$.k == " + n + "'";
            pathB = "'$.k == " + nB + "'";
        }
        String armA = "SELECT * FROM " + tbl + " WHERE gj " + op + " " + pathA;
        String armB = "SELECT * FROM " + tbl + " WHERE least(gj, gj) " + op + " " + pathB;
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin(gj jsonb_path_ops);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GINJP");
    }

    /**
     * GiST 2-D geometry over the point column {@code gp} (case 20). Opens the GiST point_ops
     * consistent/penalty/picksplit code path (distinct from the range-GiST shape). armA rides a fresh
     * {@code idx_<n>_gpgist} via a selective box-containment predicate {@code gp <@ box '...'} (an Index
     * Cond on the GiST index); armB replaces the column with the exact value-identity wrapper
     * {@code point(gp[0], gp[1])} — the point reconstructed from its own coordinates. Because gp's coords
     * are integer-valued float8 (DEFAULT draws 0..999), {@code point(gp[0],gp[1]) ≡ gp} holds bit-exactly
     * (no float fuzz), yet the planner cannot match the reconstructed expression to the GiST index → a
     * pure heap Seq Scan (index-independent ground truth). Row sets provably equal → any mismatch is a
     * real GiST bug. The box is a small (~50×50 of 1000×1000 ≈ 0.25%) selective window. No deepening.
     */
    private void checkGistPointRewrite() throws Exception {
        PostgresTable table = pickGinTable("gp");
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_gpgist";
        // Operator pool over point_ops GiST strategies: box-containment (<@, RTContainedBy) is the
        // high-yield headline; ~= (RTSame, exact point equality) is a distinct consistent branch (low
        // yield — exact-coordinate match — but index-eligible and genuinely different code). Both share
        // TAG PG_NS_GPGIST; the <@ branch carries the fault-injection proof for the TAG. (point_ops does
        // NOT register <@ against circle/polygon in pg_amop, so those stay dropped — permanently dead.)
        String op = Randomly.fromOptions("<@", "~=");
        String rhs;
        String rhsB; // identical to rhs under identity operation; shifted off the data under FAULT.
        if (op.equals("~=")) {
            int px = (int) Randomly.getNotCachedInteger(0, 1000);
            int py = (int) Randomly.getNotCachedInteger(0, 1000);
            rhs = "point '(" + px + "," + py + ")'";
            rhsB = FAULT ? "point '(" + (px + 1) + "," + py + ")'" : rhs;
        } else { // "<@" box: a small axis-aligned ~50×50 window within the [0,1000)^2 coordinate space.
            int x1 = (int) Randomly.getNotCachedInteger(0, 950);
            int y1 = (int) Randomly.getNotCachedInteger(0, 950);
            int x2 = x1 + 50;
            int y2 = y1 + 50;
            rhs = "box '((" + x1 + "," + y1 + "),(" + x2 + "," + y2 + "))'";
            rhsB = FAULT ? "box '((" + (x1 + 2000) + "," + (y1 + 2000) + "),(" + (x2 + 2000) + "," + (y2 + 2000)
                    + "))'" : rhs;
        }
        String armA = "SELECT * FROM " + tbl + " WHERE gp " + op + " " + rhs;
        String armB = "SELECT * FROM " + tbl + " WHERE point(gp[0], gp[1]) " + op + " " + rhsB;
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gist(gp);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GPGIST");
    }

    /**
     * MULTI-KEY descent (case 27): equality-prefix + range on the second key over a dedicated composite
     * {@code idx_<n>_c3c4} on {@code (c3, c4)}. armA {@code WHERE c3 = V AND c4 <op> W} drives a
     * multi-scankey nbtree descent ({@code _bt_first} seeks the c3=V prefix, {@code _bt_checkkeys} applies
     * the c4 range boundary) — a code path none of the single-conjunct shapes reach. armB wraps BOTH keys
     * in the exact value-identity {@code least/greatest(c,c)}, which the planner can match to no index → a
     * pure heap Seq Scan (index-independent ground truth). Row sets provably equal → any mismatch is a real
     * multi-key index bug. {@code op}+{@code W} are byte-identical in both arms under normal operation.
     *
     * Why (c3, c4) and NOT (c0, c1): the leading key MUST have no competing single-column index, else the
     * planner serves the equality prefix from that cheaper index and drops the second key into a Filter
     * (observed with c0 — idx_c0/idx_c0desc/idx_cover/idx_expr all tie, so the composite is never chosen and
     * the descent degenerates). The seed builds single-column btrees only on c0 and c5, so c3 is the only
     * index path for {@code c3 = V} → the composite is forced, and c3's ~3-rows-per-value selectivity keeps
     * the index strictly cheaper than a Seq Scan. Both NOT NULL (clean range bounds).
     *
     * Critical gate ("genuinely multi-key, not just touched"): the armA plan must put BOTH c3 and c4 into
     * the index's Index Cond AND leave c4 OUT of any Filter line; if c4 degenerates into a Filter the round
     * collapsed to the single-column c3 case → DISCARD (still FP-safe, just not multi-key coverage).
     */
    private void checkCompositePrefixRangeRewrite() throws Exception {
        PostgresTable table = pickGinTable("c3");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c3col = null;
        PostgresColumn c4col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c3")) c3col = c;
            else if (c.getName().equals("c4")) c4col = c;
        }
        if (c3col == null || c4col == null) return;
        String v = generateDataAwareValueForType(tbl, c3col);
        String w = generateDataAwareValueForType(tbl, c4col);
        if (v == null || w == null || "NULL".equalsIgnoreCase(v) || "NULL".equalsIgnoreCase(w)) return;
        String wrapC3 = nonSargableWrapFor(c3col, "c3");
        String wrapC4 = nonSargableWrapFor(c4col, "c4");
        if (wrapC3 == null || wrapC4 == null) return;
        String op = Randomly.fromOptions(">", "<", ">=", "<=");
        // Under FAULT the second-key operator is flipped so armB selects the complementary range →
        // deliberately non-equivalent to armA (proves the compare chain is live + data discriminating).
        String opB = op;
        if (FAULT) {
            switch (op) {
            case ">":  opB = "<="; break;
            case "<":  opB = ">="; break;
            case ">=": opB = "<";  break;
            default:   opB = ">";  break; // "<="
            }
        }
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c3c4";
        String armA = "SELECT * FROM " + tbl + " WHERE c3 = " + v + " AND c4 " + op + " " + w;
        String armB = "SELECT * FROM " + tbl + " WHERE " + wrapC3 + " = " + v + " AND " + wrapC4 + " " + opB
                + " " + w;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c3, c4);", errors, true));
            analyzeTolerant(tbl);
            List<String> planLines = getExplainPlan(armA);
            String planA = String.join("\n", planLines);
            String planB = String.join("\n", getExplainPlan(armB));
            if (!planA.contains(idxName)) return;
            boolean indexCondBothKeys = false;
            boolean c4InFilter = false;
            for (String line : planLines) {
                if (line.contains("Index Cond") && line.contains("c3") && line.contains("c4")) {
                    indexCondBothKeys = true;
                }
                if (line.contains("Filter") && line.contains("c4")) {
                    c4InFilter = true;
                }
            }
            if (!indexCondBothKeys || c4InFilter) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_PREFIXRANGE");
    }

    /**
     * SAOP single descent (case 28): a same-column equality-OR {@code c0 = V1 OR c0 = V2 OR c0 = V3} that
     * the planner collapses into a ScalarArrayOpExpr {@code c0 = ANY('{V1,V2,V3}')} served by the prebuilt
     * {@code idx_<n>_c0} — PG17's rewritten nbtree array-key advancement path (a single multi-value index
     * descent, genuinely distinct from the two-DIFFERENT-column BitmapOr that {@code checkMultiIndexRewrite}
     * already covers). armB wraps every c0 reference in the exact value-identity {@code least/greatest(c0,c0)}
     * → no index match → pure heap Seq Scan. Row sets provably equal → any mismatch is a real index bug.
     *
     * Gate accepts the {@code = ANY(...)} form in an Index/Bitmap Index Scan Index Cond with no Seq Scan on
     * the table — it does NOT require the literal "BitmapOr" token (rare for same-column SAOP). The
     * {@code idx_<n>_c0} substring also matches other c0-leading indexes (c0c1, c0desc, cover) — accepted,
     * each still serves the SAOP via the same nbtree array-key path.
     */
    private void checkSaopRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c0")) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        // Sample DISTINCT, GENUINELY-EXISTING c0 values straight from the table (ORDER BY random) so every
        // disjunct provably matches >=1 live row. generateDataAwareValueForType can occasionally emit a literal
        // with no live row, which would make the FAULT "drop the last disjunct" perturbation INERT (armB would
        // still equal armA). Direct sampling removes that dependency. Vary the arity 3..5 (Tier-4 form variety):
        // a 3/4/5-element same-column equality-OR all collapse to the nbtree SAOP array-key descent.
        long arity = globalState.getRandomly().getInteger(3, 6); // 3, 4 or 5
        // DISTINCT must be isolated in a subquery: "SELECT DISTINCT c0 ... ORDER BY random()" is illegal in
        // PostgreSQL (42P10 "for SELECT DISTINCT, ORDER BY expressions must appear in select list") because
        // random() is not in the DISTINCT list — the whole sample query errored, returning null on every call
        // and silently killing this shape. Deduplicate in the inner scan, then randomize/limit in the outer.
        List<String> vlist = executeQuery("SELECT c0 FROM (SELECT DISTINCT c0 FROM " + tbl
                + " WHERE c0 IS NOT NULL) s ORDER BY random() LIMIT " + arity);
        if (vlist == null || vlist.size() < 3) return;
        // armB wraps every c0 reference in the exact value-identity (non-sargable → Seq Scan ground truth);
        // the OR of equalities is byte-for-byte the same disjunction as armA, so the row sets are provably
        // equal. Under FAULT we drop the LAST disjunct from armB (keeping it a genuine OR → Seq Scan, NOT a
        // contradiction): armB then selects a strict subset of armA, non-equivalent because the dropped value
        // exists (sampled above). (An OR→AND perturbation would be a contradiction the planner folds to
        // "One-Time Filter: false" — no Seq Scan node — which the armB gate rejects, so it could never throw;
        // dropping a disjunct keeps armB a real heap scan the gate accepts.)
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c0";
        StringBuilder aOr = new StringBuilder();
        StringBuilder bOr = new StringBuilder();
        StringBuilder bOrFault = new StringBuilder();
        for (int i = 0; i < vlist.size(); i++) {
            String v = vlist.get(i);
            if (i > 0) { aOr.append(" OR "); bOr.append(" OR "); }
            aOr.append("c0 = ").append(v);
            bOr.append(wrap).append(" = ").append(v);
            if (i < vlist.size() - 1) {
                if (i > 0) bOrFault.append(" OR ");
                bOrFault.append(wrap).append(" = ").append(v);
            }
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + aOr;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? bOrFault : bOr);
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c0);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond") && !planA.contains("Seq Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_SAOP");
    }

    /**
     * HASH index equality scan (case 18). Hash indexes serve ONLY equality, so armA is a plain
     * {@code col = V} that rides a freshly-built {@code hashidx_<tbl>_<col>} hash index (an Index Scan);
     * armB wraps the column in the exact value-identity {@code least/greatest(col,col)} (non-sargable →
     * Seq Scan, index-independent ground truth). This exercises the hash AM's bucket lookup / heap
     * recheck path, which no other shape reaches (btree/brin/gin only). Row sets provably equal → any
     * mismatch is a real hash-index bug. gj/ga are excluded (jsonb/array modeled as TEXT would produce
     * ill-typed {@code = <text>} predicates). Deepened like the scalar shapes.
     */
    private void checkHashIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        String tbl = table.getName();
        // Candidate scalar columns with a validated value-identity wrapper, minus the jsonb/array GIN
        // targets (modeled as TEXT → a text-typed equality against jsonb/int[] would error out).
        List<PostgresColumn> candidates = new ArrayList<>();
        for (PostgresColumn col : table.getColumns()) {
            String cn = col.getName();
            if ("gj".equals(cn) || "ga".equals(cn)) continue;
            if (nonSargableWrapFor(col, cn) != null) {
                candidates.add(col);
            }
        }
        if (candidates.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(candidates);
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        String v = generateDataAwareValueForType(tbl, col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;
        String idxName = "hashidx_" + tbl + "_" + colName;
        String armA = "SELECT * FROM " + tbl + " WHERE " + colName + " = " + v;
        // FAULT self-proof (ships OFF): NOT-wrap armB's wrapped equality so its row set diverges while the
        // wrapped LHS keeps armB a Seq Scan (the armB gate still accepts). armB ≡ armA when OFF.
        String primB = wrapped + " = " + v;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING hash(" + colName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride the hash index (Index Scan using hashidx...); armB pure Seq Scan, no index.
            if (!(planA.contains(idxName) && planA.contains("Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_HASH");
    }

    /** Legacy mode 8: covering index → index-only scan. */
    private void checkCoveringIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        if (table.getColumns().size() < 2) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn a = Randomly.fromList(cands);
        PostgresColumn b = null;
        for (PostgresColumn c : table.getColumns()) {
            if (!c.getName().equals(a.getName())) { b = c; break; }
        }
        if (b == null) return;
        String tbl = table.getName();
        String aName = a.getName();
        String bName = b.getName();
        String wrapped = nonSargableWrapFor(a, aName);
        if (wrapped == null) return;
        String v = generateDataAwareValueForType(tbl, a);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;

        String idxName = "nscov_" + tbl + "_" + aName;
        // Deepen the covering (INDEX ONLY) path beyond a bare point lookup: when the INCLUDE column b has a
        // btree-comparable type, AND a payload filter on b. PG serves b straight from the index payload, so the
        // plan STAYS an Index Only Scan (b shows up as a Filter on that node) — exercising the index-only tuple
        // path the plain point form skips. The b-filter is byte-identical in both arms (b is payload, never the
        // index-under-test key), so soundness is unchanged. FAULT self-proof: NOT-wrap armB's primary a-predicate
        // (still non-sargable ⇒ armB stays a Seq Scan) so its row set diverges. Ships OFF ⇒ armB ≡ armA.
        boolean bComparable = wrappableColumns(table).stream().anyMatch(c -> c.getName().equals(bName));
        String vb = bComparable ? generateDataAwareValueForType(tbl, b) : null;
        String bPred = "";
        if (vb != null && !"NULL".equalsIgnoreCase(vb) && (DEEP_FORCE || Randomly.getBoolean())) {
            bPred = " AND " + bName + " " + Randomly.fromOptions("=", "<>", "<", "<=", ">", ">=") + " " + vb;
        }
        String primB = wrapped + " = " + v;
        String armA = "SELECT " + aName + ", " + bName + " FROM " + tbl + " WHERE " + aName + " = " + v + bPred;
        String armB = "SELECT " + aName + ", " + bName + " FROM " + tbl + " WHERE "
                + (FAULT ? "NOT (" + primB + ")" : primB) + bPred;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + aName + ") INCLUDE (" + bName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Only Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_COVER");
    }

    /** Legacy modes 6/9: two single-column indexes → bitmap OR merge. */
    private void checkMultiIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.size() < 2) return;
        PostgresColumn a = Randomly.fromList(cands);
        PostgresColumn b = a;
        while (b.getName().equals(a.getName())) {
            b = Randomly.fromList(cands);
        }
        String tbl = table.getName();
        String aName = a.getName();
        String bName = b.getName();
        String wrapA = nonSargableWrapFor(a, aName);
        String wrapB = nonSargableWrapFor(b, bName);
        if (wrapA == null || wrapB == null) return;
        String va = generateDataAwareValueForType(tbl, a);
        String vb = generateDataAwareValueForType(tbl, b);
        if (va == null || vb == null || "NULL".equalsIgnoreCase(va) || "NULL".equalsIgnoreCase(vb)) return;

        // Deepen the two-index bitmap combination beyond plain equality BitmapOr: pick a connector
        // (OR → BitmapOr, AND → BitmapAnd) and an independent comparison operator per side
        // (= / < / <= / > / >=). Range operators drive range Bitmap Index Scans and the per-tuple
        // "Recheck Cond" path; the AND connector exercises the BitmapAnd intersection node. FP invariant is
        // unchanged: armB wraps ONLY the two indexed keys with the proven least(k,k)≡k identity (incl. NULL);
        // the connector, both operators, and both RHS values are byte-identical across arms, so the two row
        // sets are provably equal regardless of which bitmap path the planner chooses.
        String connector = Randomly.fromOptions("OR", "AND");
        String opA = Randomly.fromOptions("=", "<", "<=", ">", ">=");
        String opB = Randomly.fromOptions("=", "<", "<=", ">", ">=");
        // FAULT self-proof: flip the connector in armB only → OR-set vs AND-set differ whenever the two
        // conditions do not cover identical rows (the overwhelmingly common case), so the comparator must throw.
        String connectorB = FAULT ? ("OR".equals(connector) ? "AND" : "OR") : connector;

        String idxA = "nsbm_" + tbl + "_" + aName;
        String idxB = "nsbm_" + tbl + "_" + bName;
        String armA = "SELECT * FROM " + tbl + " WHERE " + aName + " " + opA + " " + va
                + " " + connector + " " + bName + " " + opB + " " + vb;
        String armB = "SELECT * FROM " + tbl + " WHERE " + wrapA + " " + opA + " " + va
                + " " + connectorB + " " + wrapB + " " + opB + " " + vb;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxA
                    + " ON " + tbl + " (" + aName + ");", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxB
                    + " ON " + tbl + " (" + bName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must GENUINELY combine two indexes via a bitmap node. Gate structurally (BitmapOr/BitmapAnd
            // + at least two Bitmap Index Scans) rather than pinning the nsbm_ names: the planner often serves a
            // condition from a prebuilt index on the same column, which is an equally valid index path and must
            // not be discarded. Soundness rests only on the identity wrapper + armB being a pure Seq Scan, never
            // on which index armA picks.
            int bitmapIndexScans = planA.split("Bitmap Index Scan", -1).length - 1;
            boolean combinedBitmap = (planA.contains("BitmapOr") || planA.contains("BitmapAnd"))
                    && bitmapIndexScans >= 2;
            if (!combinedBitmap) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_BITMAP");
    }

    /** Legacy mode 20: NULL handling through the index. */
    private void checkNullIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        // Prefer a KNOWN-nullable seed column (c2 ~85% NULL, c6 ~50% NULL) so IS NULL returns many rows instead
        // of an always-empty set on a NOT NULL column (which is sound but tests nothing). Fall back to the random
        // wrappable pick for non-seed tables / when neither is present.
        List<PostgresColumn> nullable = cands.stream()
                .filter(c -> "c2".equals(c.getName()) || "c6".equals(c.getName()))
                .collect(java.util.stream.Collectors.toList());
        PostgresColumn col = Randomly.fromList(nullable.isEmpty() ? cands : nullable);
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;

        String idxName = "nsnull_" + tbl + "_" + colName;
        // Predicate variety: the canonical IS NULL probe PLUS an equality variant on the same (often nullable)
        // key. Both descend the btree as an Index Cond ("col IS NULL" / "col = v"); the equality form exercises a
        // different index-search path (a point descent vs the NULL sentinel) over the identical seed column.
        // FAULT self-proof (was inert): NOT-wrap armB's (already non-sargable) predicate so its row set diverges
        // while the wrapped LHS keeps armB a Seq Scan. Ships OFF ⇒ armB ≡ armA.
        String pred;
        String primB;
        String v = generateDataAwareValueForType(tbl, col);
        if (v != null && !"NULL".equalsIgnoreCase(v) && Randomly.getBoolean()) {
            pred = colName + " = " + v;
            primB = wrapped + " = " + v;
        } else {
            pred = colName + " IS NULL";
            primB = wrapped + " IS NULL";
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + pred;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + colName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // Require the IS NULL predicate to ride the index as an Index Cond (btree emits
            // "Index Cond: (col IS NULL)") — a bare idxName substring could be a Seq-Scan Filter.
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_NULL");
    }

    /** Legacy mode 23: composite (a,b) index — index cond pushdown. */
    private void checkCompositeIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.size() < 2) return;
        PostgresColumn a = Randomly.fromList(cands);
        PostgresColumn b = a;
        while (b.getName().equals(a.getName())) {
            b = Randomly.fromList(cands);
        }
        String tbl = table.getName();
        String aName = a.getName();
        String bName = b.getName();
        String wrapA = nonSargableWrapFor(a, aName);
        String wrapB = nonSargableWrapFor(b, bName);
        if (wrapA == null || wrapB == null) return;
        String va = generateDataAwareValueForType(tbl, a);
        String vb = generateDataAwareValueForType(tbl, b);
        if (va == null || vb == null || "NULL".equalsIgnoreCase(va) || "NULL".equalsIgnoreCase(vb)) return;

        String idxName = "nscomp_" + tbl + "_" + aName + "_" + bName;
        // 2nd-key operator variety: the lead key stays equality (required for the composite btree to descend on
        // both columns), but the trailing key ranges over =/>=/<=/>/< so armA exercises the composite
        // equality-prefix + range-suffix Index Cond, not only the point/point case. Both keys still appear in the
        // SAME Index Cond line (verified by the gate below), so this stays a true composite-descent differential.
        String op2 = Randomly.fromOptions("=", ">=", "<=", ">", "<");
        String armA = "SELECT * FROM " + tbl + " WHERE " + aName + " = " + va + " AND " + bName + " " + op2 + " " + vb;
        // FAULT self-proof (ships OFF): NOT-wrap armB's conjunction so its row set diverges while the wrapped
        // keys keep armB a Seq Scan (the armB gate still accepts). armB ≡ armA when OFF.
        String primB = wrapA + " = " + va + " AND " + wrapB + " " + op2 + " " + vb;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, a, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + aName + ", " + bName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // Tightened gate: prove BOTH composite keys drive the index descent (both appear in the SAME
            // "Index Cond" line), not one in Index Cond + the other demoted to a heap Filter. The two
            // wrappable keys are drawn from c0..c7 (none a substring of another); the lead renders as
            // "<a> =" and the trailing as "<b> <op2>", so the per-line membership test is unambiguous.
            String idxCondLine = "";
            for (String ln : planA.split("\n")) {
                if (ln.contains("Index Cond")) { idxCondLine = ln; break; }
            }
            boolean bothKeysInIndexCond = idxCondLine.contains(aName + " =") && idxCondLine.contains(bName + " " + op2);
            if (!(planA.contains(idxName) && bothKeysInIndexCond)) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_COMPOSITE");
    }

    /** Legacy mode 21: prefix LIKE via a text_pattern_ops index. */
    private void checkPrefixIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = new ArrayList<>();
        for (PostgresColumn c : table.getColumns()) {
            if (c.getType() == PostgresDataType.TEXT) cands.add(c);
        }
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        String tok = sampleLikeToken(tbl, colName, (int) Randomly.getNotCachedInteger(2, 6), false);
        if (tok == null) return;

        String idxName = "nspfx_" + tbl + "_" + colName;
        // Deepen: AND a residual Filter tree over the NON-INDEXED cols (c2/c4/c6), identical in both arms, so
        // armA becomes an index scan FEEDING a non-trivial Filter rather than a bare single Index Cond. FAULT
        // self-proof: NOT-wrap armB's (already non-sargable) primary predicate so its row set diverges while
        // the wrapped LHS keeps armB a Seq Scan (the armB gate still accepts). Ships OFF ⇒ armB ≡ armA.
        String primB = wrapped + " LIKE '" + tok + "%'";
        String armA = "SELECT * FROM " + tbl + " WHERE " + colName + " LIKE '" + tok + "%'";
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + colName + " text_pattern_ops);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // Require the prefix LIKE to descend the index as an Index Cond (text_pattern_ops emits
            // "Index Cond: ((col ~>=~ 'tok') AND (col ~<~ ...))") — not merely a Seq-Scan Filter.
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_PREFIX");
    }

    /** Legacy modes 15/16: infix LIKE via a pg_trgm GIN index (self-skips if pg_trgm absent). */
    private void checkTrigramLikeRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = new ArrayList<>();
        for (PostgresColumn c : table.getColumns()) {
            if (c.getType() == PostgresDataType.TEXT) cands.add(c);
        }
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        String tok = sampleLikeToken(tbl, colName, (int) Randomly.getNotCachedInteger(3, 7), true); // trigram needs >= 3 chars
        if (tok == null) return;

        String idxName = "nstrgm_" + tbl + "_" + colName;
        // Pattern-form variety: a pg_trgm GIN extracts the trigrams from a >=3-char literal regardless of where
        // the wildcards sit, so infix '%tok%', suffix '%tok' AND prefix 'tok%' all descend the SAME GIN as a
        // Bitmap Index Scan (verified by the gate below). Exercises three distinct LIKE shapes over one index.
        // Deepen: AND a residual Filter tree over the NON-INDEXED cols (c2/c4/c6), identical in both arms, so
        // armA becomes a GIN scan FEEDING a non-trivial Filter rather than a bare single recheck. FAULT
        // self-proof: NOT-wrap armB's (already non-sargable) primary predicate so its row set diverges while
        // the wrapped LHS keeps armB a Seq Scan (the armB gate still accepts). Ships OFF ⇒ armB ≡ armA.
        String pat = Randomly.fromOptions("%" + tok + "%", "%" + tok, tok + "%");
        String primB = wrapped + " LIKE '" + pat + "'";
        String armA = "SELECT * FROM " + tbl + " WHERE " + colName + " LIKE '" + pat + "'";
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE EXTENSION IF NOT EXISTS pg_trgm;", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin (" + colName + " gin_trgm_ops);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // Require the trigram GIN to be consumed via a Bitmap Index Scan (GIN cannot be an ordered
            // Index Scan) — a bare idxName substring is not proof the infix LIKE actually used the index.
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_TRGM");
    }

    /** Legacy mode 4: MIN/MAX index pushdown (InitPlan via Index Only Scan). */
    private void checkAggregateIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        // MIN/MAX ignore NULLs, and least/greatest(c,c) ≡ c value-for-value, so the single
        // aggregate value is identical between arms. armA lets PG fetch the extreme straight
        // from the ordered index (InitPlan / Index Only Scan, no full scan); armB's wrapper
        // blocks the match, forcing an Aggregate over a Seq Scan.
        String agg = Randomly.getBoolean() ? "min" : "max";

        String idxName = "nsagg_" + tbl + "_" + colName;
        // Deepen beyond the bare whole-table extreme: with ~50% probability (forced under FAULT) add an
        // index-usable bound on the aggregated column. PG still answers MIN/MAX via the ordered index — now an
        // InitPlan with an Index Cond (bounded Index-Only Scan + Limit 1) rather than an unbounded one —
        // exercising the bounded-extreme index path. The bound constant is embedded byte-identically in both
        // arms; armB wraps the column (non-sargable) so its arm stays an Aggregate over a Seq Scan. FAULT
        // self-proof: NOT-wrap armB's bound so the filtered set (hence the extreme) diverges. Ships OFF ⇒ armB≡armA.
        String whereA = "";
        String whereB = "";
        if (FAULT || DEEP_FORCE || Randomly.getBoolean()) {
            String bv = generateDataAwareValueForType(tbl, col);
            if (bv != null && !"NULL".equalsIgnoreCase(bv)) {
                String op = Randomly.fromOptions(">", ">=", "<", "<=");
                String primB = wrapped + " " + op + " " + bv;
                whereA = " WHERE " + colName + " " + op + " " + bv;
                whereB = " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
            }
        }
        String armA = "SELECT " + agg + "(" + colName + ") FROM " + tbl + whereA;
        String armB = "SELECT " + agg + "(" + wrapped + ") FROM " + tbl + whereB;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + colName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: extreme fetched via the MIN/MAX index transform (Result → InitPlan → Limit → Index
            // Scan), not a plain Aggregate over an index scan. Requiring InitPlan+Limit proves the
            // index actually supplied the extreme (holds with and without the optional range bound).
            if (!(planA.contains(idxName) && planA.contains("InitPlan") && planA.contains("Limit"))) return;
            // armB: plain Aggregate over a Seq Scan, no index node.
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_AGG");
    }

    /** Legacy mode 22: index use inside a scalar-subquery predicate. */
    private void checkSubqueryIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        // A DIFFERENT column of the SAME type feeds the subquery aggregate, so the RHS is a
        // stable scalar that (usually) does not ride the index-under-test — keeping armB's outer
        // scan index-independent while armA's outer lookup rides the col index.
        PostgresColumn sub = null;
        for (PostgresColumn c : table.getColumns()) {
            if (!c.getName().equals(col.getName()) && c.getType() == col.getType()) { sub = c; break; }
        }
        if (sub == null) return;
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;

        String idxName = "nssub_" + tbl + "_" + colName;
        String rhs = "(SELECT min(" + sub.getName() + ") FROM " + tbl + ")";
        // Deepen: AND a residual Filter tree over the NON-INDEXED cols (c2/c4/c6), identical in both arms, so
        // armA's outer scan FEEDS a non-trivial Filter rather than a bare single Index Cond. FAULT self-proof:
        // NOT-wrap armB's (already non-sargable) outer predicate so its row set diverges while the wrapped LHS
        // keeps armB's outer scan off the index-under-test (the armB gate still accepts). Ships OFF ⇒ armB≡armA.
        String primB = wrapped + " = " + rhs;
        String armA = "SELECT * FROM " + tbl + " WHERE " + colName + " = " + rhs;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, col, armA, armB);
        armA = deepened[0];
        armB = deepened[1];
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + colName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            // armB's outer scan must not ride the index-under-test (a subquery may use other indexes).
            if (!(planB.contains("Seq Scan") && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_SUBQ");
    }

    /** Legacy mode 11: unique-index range scan (self-skips if the column has duplicates). */
    private void checkUniqueIndexRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        // A UNIQUE index on a PARTITIONED table must include the partition key; PG rejects a plain
        // UNIQUE(col) with "unsupported UNIQUE constraint with partition key definition". That error is
        // not in the shared expected-error set, and checkException raises an AssertionError (an Error, not
        // an Exception) that the catch below cannot swallow → the thread would die. Partitioned tables add
        // nothing this shape needs, so skip them outright (mirrors the INSERT-path isPartitioned guards).
        if (table.isPartitioned()) return;
        List<PostgresColumn> cands = wrappableColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        String v = generateDataAwareValueForType(tbl, col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;

        String idxName = "nsuniq_" + tbl + "_" + colName;
        // Deepen: AND a residual Filter tree over the NON-INDEXED cols (c2/c4/c6), identical in both arms, so
        // armA becomes a unique-index Index Cond FEEDING a non-trivial Filter rather than a bare equality.
        // FAULT self-proof: NOT-wrap armB's (already non-sargable) predicate so its row set diverges while the
        // wrapped LHS keeps armB a Seq Scan (the armB gate still accepts). Ships OFF ⇒ armB ≡ armA.
        // MULTI-ROW ordered unique-leaf scan (not point equality, which gives ≤1 row): `col >= v ORDER BY col
        // LIMIT k`. The ORDER BY col + LIMIT makes the ordered unique btree the cheap plan for ANY v (an
        // open-ended `col >= v` alone goes Seq Scan whenever v is unselective, and degenerates to ≤1 row when
        // it is selective) — so armA reliably rides nsuniq as an Index Cond scan returning k>1 leaf-ordered
        // rows. col is UNIQUE (the CREATE UNIQUE INDEX above succeeded) ⇒ a TOTAL order ⇒ `ORDER BY col LIMIT k`
        // is DETERMINISTIC (no tie ambiguity) ⇒ FP-safe. armB wraps the ORDER BY key too (least(col,col) ≡ col,
        // value-identical ordering) so its sort is non-indexable → Seq Scan + Sort, never an index. FAULT
        // NOT-wrap → `least(col,col) < v` → the complement's first-k rows → diverges.
        int k = (int) Randomly.getNotCachedInteger(2, 12);
        // Operator variety over the ordered unique leaf: >= (open upper), <= (open lower) and BETWEEN SYMMETRIC
        // (bounded). All three descend nsuniq as an ordered Index Cond scan feeding the ORDER BY col LIMIT k;
        // SYMMETRIC auto-orders its two bounds, so no Java-side lo/hi comparison over opaque typed literals is
        // needed. The predicate is embedded byte-identically in both arms (armB wraps only the key).
        String rel;
        String primB;
        int variant = (int) Randomly.getNotCachedInteger(0, 3);
        if (variant == 0) {
            rel = colName + " >= " + v;
            primB = wrapped + " >= " + v;
        } else if (variant == 1) {
            rel = colName + " <= " + v;
            primB = wrapped + " <= " + v;
        } else {
            String v2 = generateDataAwareValueForType(tbl, col);
            if (v2 == null || "NULL".equalsIgnoreCase(v2)) { v2 = v; }
            rel = colName + " BETWEEN SYMMETRIC " + v + " AND " + v2;
            primB = wrapped + " BETWEEN SYMMETRIC " + v + " AND " + v2;
        }
        // FROM ONLY: the UNIQUE index is PARENT-LOCAL. If tbl is an inheritance parent (INHERITS children),
        // a plain `SELECT * FROM tbl` scans the children too, where col is NOT unique → `ORDER BY col LIMIT k`
        // has ties at the boundary → armA (index-ordered) and armB (Sort) pick different tied rows → a FALSE
        // "misses" mismatch under SELECT * (the tied rows differ in non-key cols). ONLY restricts the scan to
        // the parent's own rows — exactly the set the unique index covers — so col is strictly unique there ⇒
        // a genuine TOTAL order ⇒ deterministic LIMIT ⇒ FP-safe. On non-inherited tables ONLY is a no-op.
        String baseA = "SELECT * FROM ONLY " + tbl + " WHERE " + rel;
        String baseB = "SELECT * FROM ONLY " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepened = maybeDeepen(table, col, baseA, baseB);
        String armA = deepened[0] + " ORDER BY " + colName + " LIMIT " + k;
        String armB = deepened[1] + " ORDER BY " + wrapped + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            // CREATE UNIQUE INDEX throws if the column is not unique → caught → shape self-skips. Use a
            // local expected-error set so a non-unique column, a partition-key rejection (defence in depth
            // vs the guard above and any cache/catalog race), or an in-flight-drop race is tolerated as an
            // expected outcome rather than escalating to a thread-killing AssertionError.
            ExpectedErrors uniqErrors = new ExpectedErrors();
            uniqErrors.add("could not create unique index");
            uniqErrors.add("unsupported UNIQUE constraint with partition key definition");
            uniqErrors.add("duplicate key value");
            uniqErrors.add("relation .* does not exist");
            // Defence in depth: a TEXT-modeled column without a btree opclass (e.g. a POINT column) would
            // fail this CREATE with "has no default operator class"; tolerate it as a self-skip rather than
            // a thread-killing AssertionError. (gp is already excluded from wrappableColumns above, so this
            // is belt-and-suspenders for any future unindexable-by-btree type modeled as TEXT.)
            uniqErrors.add("has no default operator class");
            // CREATE UNIQUE INDEX is heavy DDL and can legitimately hit the per-statement timeout under load;
            // tolerate the cancellation as a self-skip rather than a thread-killing AssertionError (same
            // precedent as the shared expectedErrors and reindexErrors sets).
            uniqErrors.add("canceling statement due to statement timeout");
            uniqErrors.add("canceling statement due to user request");
            globalState.executeStatement(new SQLQueryAdapter("CREATE UNIQUE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + colName + ");", uniqErrors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_UNIQUE");
    }

    /** Legacy mode 15 (range half): int4range GiST overlap/containment. */
    private void checkRangeGistRewrite() throws Exception {
        PostgresTable table = pickNonViewTable();
        if (table == null) return;
        List<PostgresColumn> cands = new ArrayList<>();
        for (PostgresColumn c : table.getColumns()) {
            if (c.getType() == PostgresDataType.RANGE) cands.add(c);
        }
        if (cands.isEmpty()) return;
        PostgresColumn col = Randomly.fromList(cands);
        String tbl = table.getName();
        String colName = col.getName();
        // Range value-identity wrappers validated on PG 17.6 (exact incl NULL/empty/unbounded,
        // and non-sargable vs a GiST index): self-merge and self-intersection.
        String wrapped = Randomly.getBoolean()
                ? "range_merge(" + colName + ", " + colName + ")"
                : "(" + colName + " * " + colName + ")";
        int a = (int) Randomly.getNotCachedInteger(-100000, 100000);
        int b = (int) Randomly.getNotCachedInteger(-100000, 100000);
        int lo = Math.min(a, b);
        int hi = Math.max(a, b);
        String rhs = "int4range(" + lo + ", " + hi + ")";
        // armB's RHS is byte-identical to armA under normal (identity) operation; perturbed far away
        // only under fault-injection so armB becomes deliberately non-equivalent.
        String rhsB = FAULT ? "int4range(" + (lo + 1000000) + ", " + (hi + 1000001) + ")" : rhs;
        // Operator pool over range_gist_consistent strategy branches: OVERLAP(&&), CONTAINS(@>),
        // CONTAINED(<@), BEFORE(<<), AFTER(>>), ADJACENT(-|-), OVERLEFT(&<), OVERRIGHT(&>). The last five
        // are distinct consistent branches (and their empty-range handling) the prior 3-op set never hit.
        String op = Randomly.fromOptions("&&", "@>", "<@", "<<", ">>", "-|-", "&<", "&>");

        String idxName = "nsrg_" + tbl + "_" + colName;
        String armA = "SELECT * FROM " + tbl + " WHERE " + colName + " " + op + " " + rhs;
        String armB = "SELECT * FROM " + tbl + " WHERE " + wrapped + " " + op + " " + rhsB;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gist (" + colName + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_RGIST");
    }

    /**
     * Join-index shape (opens the JOIN plan family — legacy mode 5 class).
     * armA: self-join on a wrappable, indexed key with a selective equality filter on a DIFFERENT,
     *   unindexed column -> the planner uses an index scan on the join key (index-nested-loop / merge).
     * armB: BOTH join keys wrapped in the value-identity wrapper (least/greatest(e,e) etc.) -> the planner
     *   cannot match either side to the index -> the join key index is not used (hash join over seq scans).
     * Only ONE side wrapped is insufficient: the planner can still index-scan the other side, so we wrap both.
     * Soundness: least/greatest(e,e) ≡ e (incl NULL; NULL join keys are excluded identically in both arms
     *   since NULL = x is never true), so the join produces the identical pair multiset; the filter is textually
     *   identical in both arms. No ORDER BY/LIMIT -> compareResultsSorted (multiset) is sound. No GUC.
     * Gate is index-under-test-specific (armB may legitimately use OTHER indexes for the filter/plan).
     */
    private void checkJoinIndexRewrite() throws Exception {
        // Prefer the LARGEST non-view table: a bigger inner makes the hash-join alternative costlier, so the
        // planner is likelier to pick an index-nested-loop over the join key (the plan armA needs). On tiny
        // tables seq+hash is trivially cheap and the index-NLJ never wins -> gate discards (sound, no yield).
        // Restrict to idx_t<n> tables ONLY: they carry the stable identity column `cb` used for the outer pin
        // below (see the ctid-unsoundness note there). They are also the large seeded tables (12000+ rows), so
        // "largest non-view" effectively meant an idx_t table already — the restriction preserves the intent.
        List<PostgresTable> allTables = globalState.getSchema().getDatabaseTables();
        PostgresTable table = null;
        long best = -1;
        for (PostgresTable t : allTables) {
            if (t.isView() || !t.getName().startsWith("idx_t")) continue;
            long n = t.getNrRows(globalState);
            if (n > best) {
                best = n;
                table = t;
            }
        }
        if (table == null) return;
        // Join key from the TEXT-free pool: a plain-TEXT key under the DB's Windows libc collation makes the
        // index-NLJ arm miss a boundary row the seq arm finds → an environmental collation false positive, not
        // an index bug (see joinKeyColumns). Numeric keys fully exercise the index-NLJ-vs-hash-join mechanics.
        List<PostgresColumn> cands = joinKeyColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn jc = Randomly.fromList(cands);
        String jcn = jc.getName();
        String tbl = table.getName();
        String baseWrapA = nonSargableWrapFor(jc, "a." + jcn);
        String wrapB = nonSargableWrapFor(jc, "b." + jcn);
        if (baseWrapA == null || wrapB == null) return;
        // FAULT self-proof: shift ONLY armB's (a-side) join key by +1 so the joined pair multiset diverges from
        // armA while the wrapped LHS keeps armB index-free (gate still accepts). Ships OFF ⇒ wrapA ≡ a.jcn
        // identity. (+1 requires a numeric join key, which is now guaranteed: joinKeyColumns excludes TEXT, so
        // the pool is numeric/jsonb/array — the dominant numeric keys carry the proof.)
        String wrapA = FAULT ? baseWrapA + " + 1" : baseWrapA;

        // Pin the OUTER side to exactly k rows (k in 2..8) via a deterministic `cb` top-k. `cb` is a GENERATED
        // ALWAYS AS IDENTITY column (unique, NOT NULL, LOGICAL value — never changes) so `cb IN (SELECT cb ...
        // ORDER BY cb LIMIT k)` selects the SAME k rows on every execution. k>1 makes the index-nested-loop
        // probe the join-key index k times, exercising repeated index descents, while k stays small enough that
        // the planner still prefers the index-NLJ over a hash join. The pin is byte-identical in both arms and
        // the join-key wrapper is exact value-identity, so the two arms compute the same row set by construction.
        //
        // DO NOT use a ctid top-k here (the previous form). armA and armB run as SEPARATE statements/snapshots;
        // ctid is a PHYSICAL address that PostgreSQL may change between them (HOT prune, autovacuum), so
        // `ctid IN (SELECT ctid ... ORDER BY ctid LIMIT k)` can pin DIFFERENT physical rows in each arm → an
        // off-by-boundary cardinality drift that is a FALSE POSITIVE, not an index bug (observed: 2170 vs 2171).
        int k = Randomly.fromOptions(2, 3, 4, 5, 6, 7, 8);
        String outer = "(SELECT cb FROM " + tbl + " ORDER BY cb LIMIT " + k + ")";
        String idxName = "nsjoin_" + tbl + "_" + jcn;
        String armA = "SELECT * FROM " + tbl + " a JOIN " + tbl + " b ON a." + jcn + " = b." + jcn
                + " WHERE a.cb IN " + outer;
        String armB = "SELECT * FROM " + tbl + " a JOIN " + tbl + " b ON " + wrapA + " = " + wrapB
                + " WHERE a.cb IN " + outer;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + jcn + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // Tightened gate: prove armA is a true index-nested-loop (a Nested Loop whose inner rides our index
            // via an actual scan node), not merely a plan that mentions "Index" somewhere.
            boolean armARidesIdx = planA.contains(idxName) && planA.contains("Nested Loop")
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"));
            if (!armARidesIdx) return;
            // armB positive non-index gate: the wrapped join key least(jc,jc) cannot ride ANY index on the join
            // key, so the probe side MUST be sequentially scanned. Require Seq Scan (and our index absent) so a
            // silent switch to a different index is rejected — the index-vs-no-index differential actually runs.
            if (planB.contains(idxName) || !planB.contains("Seq Scan")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_JOIN");
    }

    // ==================== Mode 28 new differential axes (multi-table / index-definition / order) ========
    // Each obeys the proven skeleton (armA rides the index-under-test; armB wraps the probed column in an
    // exact value-identity function the planner cannot match → index-independent ground truth; EXPLAIN-gated;
    // NO GUC; provably-equal results). All self-skip on any missing candidate / gate miss / caught exception,
    // and only ever report via the comparator (an AssertionError, which is NOT an Exception, so it propagates
    // past the catch(Exception) guards below).

    /**
     * MULTI-TABLE axis (case 22). Cross-table correlated EXISTS semijoin between two DIFFERENT {@code idx_t}
     * tables. The outer is pinned to exactly one row via {@code min(ctid)} (deterministic, unique, index-free,
     * byte-identical in both arms — same device as {@link #checkJoinIndexRewrite}); the inner's join key is
     * index-probed in armA ({@code i.<oc> = o.<oc>}) and wrapped off-index in armB ({@code least/greatest(i.<oc>,
     * i.<oc>) = o.<oc>}). EXISTS is a SEMIJOIN, so each outer row appears AT MOST ONCE regardless of inner
     * multiplicity — the classic duplicate-multiplicity join FP is structurally excluded. The wrapper is an
     * exact value-identity incl. NULL, so the EXISTS truth value is identical row-for-row ⇒ identical set of
     * qualifying outer rows by construction. No ORDER BY/LIMIT → {@code compareResultsSorted} (multiset) is sound.
     */
    private void checkSemiJoinIndexRewrite() throws Exception {
        List<PostgresTable> all = globalState.getSchema().getDatabaseTables();
        List<PostgresTable> idxTables = new ArrayList<>();
        for (PostgresTable t : all) {
            if (!t.isView() && t.getName().startsWith("idx_t")) idxTables.add(t);
        }
        if (idxTables.size() < 2) return; // needs two distinct idx_t tables
        PostgresTable outer = Randomly.fromList(idxTables);
        PostgresTable inner = null;
        for (int tries = 0; tries < 8; tries++) {
            PostgresTable cand = Randomly.fromList(idxTables);
            if (!cand.getName().equals(outer.getName())) { inner = cand; break; }
        }
        if (inner == null) return;
        // Join key from the TEXT-free pool (see joinKeyColumns): a plain-TEXT correlation key under the DB's
        // Windows libc collation makes the index-NLJ semijoin miss a boundary row the seq arm finds → an
        // environmental collation false positive, not an index bug. Numeric keys exercise the semijoin fully.
        List<PostgresColumn> cands = joinKeyColumns(inner);
        if (cands.isEmpty()) return;
        PostgresColumn jc = Randomly.fromList(cands);
        String oc = jc.getName();
        String wrapIn = nonSargableWrapFor(jc, "i." + oc);
        if (wrapIn == null) return;
        String ot = outer.getName();
        String it = inner.getName();
        // Deepen beyond a single probe: pin the OUTER to a small FIXED set of k rows via the stable identity
        // column `cb` (GENERATED ALWAYS AS IDENTITY → unique, NOT NULL, logical value) so the semijoin performs
        // several index probes through nssemi_ (the planner keeps a nested-loop semi join with an inner Index
        // Scan for a small, cheaply-estimated outer). The outer restriction is byte-identical in both arms AND
        // deterministic across the two separate statement snapshots. FAULT self-proof: NOT-wrap the inner
        // correlation in armB so EXISTS flips for some outer rows ⇒ the row set diverges; the wrapped inner key
        // keeps armB off nssemi_ (the armB gate still accepts). Ships OFF ⇒ armB ≡ armA.
        //
        // DO NOT pin on ctid here: ctid is a PHYSICAL address PostgreSQL may change between the two arms'
        // separate snapshots (HOT prune / autovacuum), making `ctid IN (SELECT ctid ... LIMIT k)` select
        // different rows per arm → a false-positive cardinality drift (same bug fixed in checkJoinIndexRewrite).
        long k = Randomly.getNotCachedInteger(3, 8);
        String pin = "o.cb IN (SELECT cb FROM " + ot + " ORDER BY cb LIMIT " + k + ")";
        String idxName = "nssemi_" + it + "_" + oc;
        String corrB = wrapIn + " = o." + oc;
        String armA = "SELECT * FROM " + ot + " o WHERE " + pin
                + " AND EXISTS (SELECT 1 FROM " + it + " i WHERE i." + oc + " = o." + oc + ")";
        String armB = "SELECT * FROM " + ot + " o WHERE " + pin
                + " AND EXISTS (SELECT 1 FROM " + it + " i WHERE " + (FAULT ? "NOT (" + corrB + ")" : corrB) + ")";
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + it + " (" + oc + ");", errors, true));
            analyzeTolerant(it);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must probe the inner through our index via an actual scan node (not merely mention "Index");
            // armB must NOT use it (it may legitimately use other indexes elsewhere, so we only forbid OUR index).
            boolean armARidesIdx = planA.contains(idxName)
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan")
                            || planA.contains("Bitmap Index Scan"));
            if (!armARidesIdx) return;
            // Positive non-index gate: wrapped semijoin key forces the probe side to Seq Scan.
            if (planB.contains(idxName) || !planB.contains("Seq Scan")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_SEMIJOIN");
    }

    /**
     * MULTI-TABLE anti-join axis (case 50). Cross-table correlated {@code NOT EXISTS} between two DIFFERENT
     * {@code idx_t} tables — the planner's natural plan is an Anti Join whose inner rides the join-key index.
     * Mirror of {@link #checkSemiJoinIndexRewrite} with {@code EXISTS}→{@code NOT EXISTS}. The outer is pinned
     * to a small FIXED set of k rows via the stable IDENTITY column {@code cb} (never ctid — see that note),
     * byte-identical and deterministic across both arms' snapshots. The inner correlation key is index-probed
     * in armA and wrapped off-index in armB (exact value-identity incl. NULL ⇒ the NOT EXISTS truth value is
     * identical row-for-row ⇒ the same qualifying outer set by construction). Join key from the TEXT-free pool
     * (collation-free). FAULT self-proof (ships OFF): NOT-wrap the inner correlation so NOT EXISTS flips for
     * some outer rows ⇒ divergence; the wrapped inner key keeps armB off the probe index (gate still accepts).
     */
    private void checkAntiJoinIndexRewrite() throws Exception {
        List<PostgresTable> all = globalState.getSchema().getDatabaseTables();
        List<PostgresTable> idxTables = new ArrayList<>();
        for (PostgresTable t : all) {
            if (!t.isView() && t.getName().startsWith("idx_t")) idxTables.add(t);
        }
        if (idxTables.size() < 2) return; // needs two distinct idx_t tables
        PostgresTable outer = Randomly.fromList(idxTables);
        PostgresTable inner = null;
        for (int tries = 0; tries < 8; tries++) {
            PostgresTable cand = Randomly.fromList(idxTables);
            if (!cand.getName().equals(outer.getName())) { inner = cand; break; }
        }
        if (inner == null) return;
        List<PostgresColumn> cands = joinKeyColumns(inner);
        if (cands.isEmpty()) return;
        PostgresColumn jc = Randomly.fromList(cands);
        String oc = jc.getName();
        String wrapIn = nonSargableWrapFor(jc, "i." + oc);
        if (wrapIn == null) return;
        String ot = outer.getName();
        String it = inner.getName();
        long k = Randomly.getNotCachedInteger(8, 40); // wider outer set ⇒ more NOT-EXISTS rows to discriminate
        String pin = "o.cb IN (SELECT cb FROM " + ot + " ORDER BY cb LIMIT " + k + ")";
        String idxName = "nsanti_" + it + "_" + oc;
        String corrB = wrapIn + " = o." + oc;
        String armA = "SELECT * FROM " + ot + " o WHERE " + pin
                + " AND NOT EXISTS (SELECT 1 FROM " + it + " i WHERE i." + oc + " = o." + oc + ")";
        String armB = "SELECT * FROM " + ot + " o WHERE " + pin
                + " AND NOT EXISTS (SELECT 1 FROM " + it + " i WHERE " + (FAULT ? "NOT (" + corrB + ")" : corrB) + ")";
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + it + " (" + oc + ");", errors, true));
            analyzeTolerant(it);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            boolean armARidesIdx = planA.contains(idxName)
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan")
                            || planA.contains("Bitmap Index Scan"));
            if (!armARidesIdx) return;
            // Positive non-index gate: wrapped anti-join key forces the probe side to Seq Scan.
            if (planB.contains(idxName) || !planB.contains("Seq Scan")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_ANTIJOIN");
    }

    /**
     * LATERAL top-N-per-group axis (case 51). A self-LATERAL on the largest {@code idx_t} table returns the
     * top-m inner rows (by the unique IDENTITY {@code cb}) per pinned outer row — a shape a plain join cannot
     * express. The inner correlation key is index-probed in armA and wrapped off-index in armB. The outer is
     * pinned to a FIXED set of k rows via {@code cb} (deterministic, byte-identical both arms). The inner
     * {@code ORDER BY i.cb LIMIT m} makes the per-outer row set deterministic, and {@code least(oc,oc)≡oc}
     * keeps armA/armB value-identical. All projected columns are numeric ⇒ collation-free. FAULT self-proof
     * (ships OFF): {@code +1} on the inner correlation key matches a different inner group ⇒ different
     * (o.cb,i.cb) pairs ⇒ divergence. Compare as an unordered multiset.
     */
    private void checkLateralIndexRewrite() throws Exception {
        List<PostgresTable> allTables = globalState.getSchema().getDatabaseTables();
        PostgresTable table = null;
        long best = -1;
        for (PostgresTable t : allTables) {
            if (t.isView() || !t.getName().startsWith("idx_t")) continue;
            long n = t.getNrRows(globalState);
            if (n > best) {
                best = n;
                table = t;
            }
        }
        if (table == null) return;
        List<PostgresColumn> cands = joinKeyColumns(table);
        if (cands.isEmpty()) return;
        PostgresColumn jc = Randomly.fromList(cands);
        String oc = jc.getName();
        String wrapIn = nonSargableWrapFor(jc, "i." + oc);
        if (wrapIn == null) return;
        String tbl = table.getName();
        int k = (int) Randomly.getNotCachedInteger(8, 40); // wider outer set ⇒ more LATERAL groups to discriminate
        long m = globalState.getRandomly().getInteger(2, 5);
        String idxName = "nsla_" + tbl + "_" + oc;
        String corrA = "i." + oc + " = o." + oc;
        String corrB = wrapIn + " = o." + oc;
        String probeB = FAULT ? (wrapIn + " + 1 = o." + oc) : corrB;
        String pin = "o.cb IN (SELECT cb FROM " + tbl + " ORDER BY cb LIMIT " + k + ")";
        String armA = "SELECT o.cb, i.cb, i.c0 FROM " + tbl + " o JOIN LATERAL (SELECT i.cb, i.c0 FROM " + tbl
                + " i WHERE " + corrA + " ORDER BY i.cb LIMIT " + m + ") i ON true WHERE " + pin;
        String armB = "SELECT o.cb, i.cb, i.c0 FROM " + tbl + " o JOIN LATERAL (SELECT i.cb, i.c0 FROM " + tbl
                + " i WHERE " + probeB + " ORDER BY i.cb LIMIT " + m + ") i ON true WHERE " + pin;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (" + oc + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            boolean armARidesIdx = planA.contains(idxName)
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"));
            if (!armARidesIdx) return;
            // Positive non-index gate: wrapped lateral key forces the inner side to Seq Scan.
            if (planB.contains(idxName) || !planB.contains("Seq Scan")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_LATERAL");
    }

    /**
     * Ordered cross-partition Merge Append axis (case 52). On the RANGE-partitioned {@code idx_pt}, an
     * un-pruned ordered scan {@code ORDER BY c0 LIMIT k} merges every partition's local {@code c0} index via a
     * Merge Append; armB wraps the sort key ({@code least(c0,c0)≡c0}) → the index no longer supplies the order
     * → a single Sort over Append of value-identical rows. Project ONLY the sort key {@code c0}: c0 ties render
     * byte-identical in the projection, so the LIMIT boundary is tie-invisible and positional comparison is
     * total-order safe. Child index scans show per-partition names (e.g. {@code idx_pt_p1_c0_idx}), so the gate
     * keys on the structural {@code Merge Append} node, not a pinned index name. FAULT self-proof (ships OFF):
     * flip armB's direction ⇒ the top-k reverses ⇒ divergence.
     */
    private void checkMergeAppendOrderRewrite() throws Exception {
        PostgresTable table = pickPartitionedTable();
        if (table == null) return;
        PostgresColumn c0col = table.getColumns().stream()
                .filter(c -> "c0".equals(c.getName())).findFirst().orElse(null);
        if (c0col == null) return;
        String wrapped = nonSargableWrapFor(c0col, "c0");
        if (wrapped == null) return;
        long k = globalState.getRandomly().getInteger(5, 50);
        String dir = Randomly.getBoolean() ? "ASC" : "DESC";
        String dirB = FAULT ? ("ASC".equals(dir) ? "DESC" : "ASC") : dir; // FAULT flips armB's direction
        String armA = "SELECT c0 FROM idx_pt ORDER BY c0 " + dir + " LIMIT " + k;
        String armB = "SELECT c0 FROM idx_pt ORDER BY " + wrapped + " " + dirB + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: the seed builds idx_pt_c0 (propagated local index); re-create if a drop removed it.
            globalState.executeStatement(new SQLQueryAdapter(
                    "CREATE INDEX IF NOT EXISTS idx_pt_c0 ON idx_pt (c0);", errors, true));
            analyzeTolerant("idx_pt");
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take the order from a cross-partition Merge Append over per-partition c0 index scans
            // (no Sort NODE); armB's wrapped key forces an explicit Sort over an Append. NOTE: a Merge Append
            // node itself prints a "Sort Key:" PROPERTY line, so a naive !contains("Sort") check always fails
            // here -- gate on the Sort NODE's cost line ("Sort  (cost") instead, which "Sort Key:" never matches.
            boolean armARidesMerge = planA.contains("Merge Append") && !planA.contains("Sort  (cost")
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"));
            if (!armARidesMerge) return;
            if (!planB.contains("Sort  (cost")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_MERGEAPPEND", true);
    }

    /**
     * GROUPING SETS / ROLLUP / CUBE axis (case 53). Mirror of {@link #checkGroupByIndexRewrite}: a single-column
     * grouping set over the ordered {@code c0} index yields a GroupAggregate (per-group rows + one grand-total
     * NULL row); armB wraps the group key ({@code least(c0,c0)≡c0}) → Seq Scan + Sort. The three grouping-set
     * spellings {@code ROLLUP(c0)} / {@code CUBE(c0)} / {@code GROUPING SETS ((c0),())} are single-column
     * equivalent (same multiset incl. the grand-total NULL row). FAULT self-proof (ships OFF): {@code +1} on
     * the group key shifts every projected key ⇒ divergent multiset.
     */
    /** relallvisible page count of idx_gs (-1 on read failure): >0 means the VM is lit and an Index-Only
     *  Scan stops paying heap fetches — the make-or-break condition for case 53's gate. */
    private long gsRelallvisible() {
        try (Statement st = globalState.getConnection().createStatement();
             ResultSet rs = st.executeQuery("SELECT relallvisible FROM pg_class WHERE relname = 'idx_gs'")) {
            if (rs.next()) return rs.getLong(1);
        } catch (Exception e) { }
        return -1;
    }

    /** VACUUM idx_gs from a FRESH connection. The seed INSERT runs on this oracle's own connection, and a
     *  same-session VACUUM executes before RecentGlobalXmin advances past the seed's xid → relallvisible
     *  stays 0 (measured on PG 18.6) and the gate can never pass. A fresh session's VACUUM — taken after
     *  the seed transaction is long gone — marks every page all-visible. */
    private void gsVacuum() {
        try {
            String url = "jdbc:postgresql://" + globalState.getOptions().getHost() + ":"
                    + globalState.getOptions().getPort() + "/" + globalState.getDatabaseName();
            try (java.sql.Connection fresh = java.sql.DriverManager.getConnection(url,
                    globalState.getOptions().getUserName(), globalState.getOptions().getPassword());
                 Statement vst = fresh.createStatement()) {
                fresh.setAutoCommit(true);
                vst.execute("VACUUM idx_gs");
            }
        } catch (Exception e) { }
    }

    private void checkGroupingSetsRewrite() throws Exception {
        // Dedicated idx_gs table (ITEM C): the planner only produces index-ordered input for GROUPING SETS
        // (GroupAggregate over an Index-Only Scan, no Sort) when the heap scan is expensive enough to lose the
        // cost battle against the narrow index — which needs the big wide seeded table AND an all-visible VM.
        // The old version rode a shared idx_t table WITH an ORDER BY, whose top-level Sort the planner never
        // elides through a rollup GroupAggregate — the gate was unsatisfiable (0 passes in a 24h/1.2M-gate-pass
        // soak; see the silent-shape WARN). The ORDER BY is dropped: compareValueIdentityStrict is a multiset
        // comparator (it sorts both result lists), so row order is irrelevant to soundness.
        PostgresTable table = null;
        boolean hasHeapTwin = false;
        for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
            if ("idx_gs".equals(t.getName())) { table = t; }
            if ("idx_gs_heap".equals(t.getName())) hasHeapTwin = true;
        }
        if (table == null || !hasHeapTwin) return;
        // Lazy VM heal: ITEM C seeds idx_gs from THIS connection, so a same-session VACUUM would run before
        // RecentGlobalXmin advances past the seed INSERT's xid and leave relallvisible=0 (measured) — the
        // planner then keeps the hash path and this gate can never pass. By now the insert is long committed,
        // so one VACUUM lights the VM. Bounded retries: if it stays dark after a few attempts, discard rounds
        // (status quo) instead of vacuuming forever under pathological load.
        if (gsRelallvisible() <= 0) {
            if (gsVmTries >= 3) return;
            gsVmTries++;
            gsVacuum();
            if (gsRelallvisible() <= 0) return;
        }
        String tbl = table.getName();
        PostgresColumn c0col = table.getColumns().stream()
                .filter(c -> "c0".equals(c.getName())).findFirst().orElse(null);
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String keyB = FAULT ? wrap + " + 1" : wrap;
        String setKind = Randomly.fromOptions("ROLLUP (c0)", "CUBE (c0)", "GROUPING SETS ((c0), ())");
        String setKindB = setKind.replace("c0", wrap);
        String armA = "SELECT c0, count(*) FROM " + tbl + " GROUP BY " + setKind;
        // armB runs on the INDEX-LESS twin (see ITEM C): on idx_gs itself even a wrapped key rides the
        // c0 index as the cheapest full scan (measured), so the ground-truth arm would read the index
        // under test and blind the differential. idx_gs_heap holds identical rows and no index → pure
        // Seq Scan by construction.
        String armB = "SELECT " + keyB + ", count(*) FROM idx_gs_heap GROUP BY " + setKindB;
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA takes the group order from the c0 index (GroupAggregate, no Sort). If the planner picks
            // Mixed/HashAggregate — e.g. the VM lost its all-visible bits — the gate discards (sound, lower
            // yield); the ITEM C guards keep the VM lit by construction.
            boolean armARidesIdx = (planA.contains("Index Only Scan") || planA.contains("Index Scan"))
                    && !hasSortNode(planA) && planA.contains("GroupAggregate");
            if (!armARidesIdx) return;
            // armB: index-less twin → pure Seq Scan by construction; the gate asserts it stays index-free.
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GROUPINGSETS");
    }

    /**
     * TEXT btree equality/range PREDICATE axis (case 54). An equality or range WHERE predicate on {@code c7}
     * riding the plain btree {@code idx_<t>_c7btree} (Index Cond gate); armB wraps the key
     * ({@code least(c7,c7)≡c7}) → Seq Scan. {@code c7} is {@code TEXT COLLATE "C"} ⇒ deterministic byte
     * comparison ⇒ immune to the libc-collation false positive that plain-TEXT keys suffer (hence the join
     * shapes keep TEXT off their keys and TEXT differential lives only here, on c7). Distinct from case 48
     * (c7 order-only) and case 44 (c7 SP-GiST). FAULT self-proof (ships OFF): NOT-wrap armB's predicate ⇒ the
     * complement row set ⇒ divergence; the wrapped LHS keeps armB a Seq Scan (the armB gate still accepts).
     */
    private void checkTextBtreeRangeRewrite() throws Exception {
        PostgresTable table = pickGinTable("c7");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c7col = table.getColumns().stream()
                .filter(c -> "c7".equals(c.getName())).findFirst().orElse(null);
        if (c7col == null) return;
        String wrapped = nonSargableWrapFor(c7col, "c7");
        if (wrapped == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c7btree";
        String v = generateDataAwareValueForType(tbl, c7col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;
        String v2 = generateDataAwareValueForType(tbl, c7col);
        if (v2 == null || "NULL".equalsIgnoreCase(v2) || v2.equals(v)) return;
        String lo = v.compareTo(v2) <= 0 ? v : v2;
        String hi = v.compareTo(v2) <= 0 ? v2 : v;
        long k = globalState.getRandomly().getInteger(5, 50);
        String dir = Randomly.getBoolean() ? "ASC" : "DESC";
        String dirB = FAULT ? ("ASC".equals(dir) ? "DESC" : "ASC") : dir; // FAULT flips armB's top-k direction
        // armA pairs a c7 WHERE range with ORDER BY c7, so the c7 BTREE serves BOTH the range Index Cond AND the
        // order in ONE ordered Index(-Only) Scan with NO Sort (and stops early at LIMIT). This is the ONLY c7 context
        // the btree wins over the SP-GiST index (case 44): spgist answers a c7 predicate only as an UNORDERED bitmap,
        // so for ORDER BY c7 + LIMIT the planner would have to stack a Sort on spgist and prefers the btree's free
        // order instead. Thus this shape pins the btree where case 44 (spgist, WHERE-only) and case 48 (btree,
        // ORDER-only, no WHERE) structurally cannot -- a plain c7 equality/range differential is 100% redundant with
        // case 44 because spgist always wins it, so the ordered-range form is the genuinely-new btree coverage.
        String armA = "SELECT c7 FROM " + tbl + " WHERE c7 >= " + lo + " AND c7 < " + hi
                + " ORDER BY c7 " + dir + " LIMIT " + k;
        // armB wraps the key in least(c7,c7) in BOTH the filter and the sort -> non-sargable -> Seq Scan + explicit
        // Sort over the value-identical row set (least(c7,c7) == c7). Clean: dirB == dir -> identical ordered list.
        String armB = "SELECT c7 FROM " + tbl + " WHERE " + wrapped + " >= " + lo + " AND " + wrapped + " < " + hi
                + " ORDER BY " + wrapped + " " + dirB + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: the seed builds idx_<t>_c7btree; re-create if the name-unguarded drop path removed it.
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c7);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take BOTH the range Index Cond and the order from c7btree (no Sort); armB's wrap forces Sort.
            if (!(planA.contains(idxName) && planA.contains("Index Cond") && !hasSortNode(planA))) return;
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        // Band-span guard: the FAULT direction-flip only reorders a top-k that holds ≥2 DISTINCT c7 values (an
        // all-equal top-k renders byte-identical under ASC/DESC on the key-only projection → the self-proof would
        // be inert). Skipping a degenerate band is sound (lower yield), never an FP. (c7 is COLLATE "C" → the
        // HashSet's byte-equality matches the index's byte order.)
        if (new java.util.HashSet<>(rA).size() < 2) return;
        log(armA);
        log(armB);
        // Key-only (c7) projection -> c7 ties render byte-identical in the output, so the LIMIT boundary is
        // tie-invisible and positional comparison is a total order. FAULT dirB flip reverses the top-k -> divergence.
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_TEXTBTREE", true);
    }

    /**
     * INDEX-DEFINITION axis (case 23). Runs ONE controlled deterministic query, then CREATEs an equivalent
     * plain index and re-runs it; a correct planner returns the identical row set (a plain index can never
     * change visibility). The query is deliberately simple: no LIMIT, no ORDER BY,
     * no volatile funcs → the result is a deterministic multiset, so any r1≠r2 is attributable to the index
     * mutation (the bug we hunt), not query nondeterminism. No DML runs between the two executions (only index
     * DDL + ANALYZE; churn fires only at round boundaries) → identical heap snapshot. Also folds the legacy
     * UNIQUE-count invariant: creating a UNIQUE index on {@code cb} (IDENTITY → always unique, never errors)
     * must not change {@code COUNT(*)}.
     */
    /**
     * Drop an index WE created (own {@code defidx_}/{@code defuniq_} prefix only), swallowing any error. Used in
     * {@code finally} blocks so case 23/24 run a genuine create -> test -> drop cycle each round. Without this, a
     * leaked {@code defidx} makes the before/after-create differential tautological from round 2 (r1 already rides
     * defidx, so r1 == r2 by construction while the gate still passes). Never touches a seed {@code idx_<n>_*}.
     * {@code catch (Throwable)} because an operational timeout throws {@code AssertionError} (an Error) and
     * best-effort cleanup must never mask a real finding thrown by the comparator.
     */
    private void dropOwnIndexQuietly(String idxName) {
        try {
            globalState.executeStatement(new SQLQueryAdapter("DROP INDEX IF EXISTS " + idxName + ";", errors, true));
        } catch (Throwable ignored) {
            // best-effort cleanup
        }
    }

    private void checkIndexDefinitionConsistency() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        Randomly r = globalState.getRandomly();
        long v1 = r.getInteger(-32768, 32767);
        long v2 = v1 + r.getInteger(0, 200);
        // COVERING probe: project EXACTLY defidx's columns (c0, c3) over a c0 range. Only defidx (c0, c3) can
        // serve this as an Index(-Only) Scan (the prebuilt idx_<t>_c0 would need a heap fetch for c3), so after
        // CREATE the planner ADOPTS defidx -- making this a genuine (seq / idx_c0) -> defidx differential rather
        // than a no-op. A plain index can NEVER change a result set, so r1 (before) MUST equal r2 (after).
        // The try/finally guarantees defidx/defuniq are dropped every round so r1 reliably rides the pre-create
        // plan again (a leak would silently turn this shape into a tautology -- see dropOwnIndexQuietly).
        String q = "SELECT c0, c3 FROM " + tbl + " WHERE c0 BETWEEN " + v1 + " AND " + v2;
        boolean proofUniq = "1".equals(System.getProperty("idx.proof.uniqcount"));
        try {
            // IDXDEF_CREATE differential. Skipped under the UNIQCOUNT isolation proof flag so the doubly-gated,
            // low-yield UNIQCOUNT probe below is reached every round (this block's own defidx-adoption gate would
            // otherwise return first). proofUniq is false without the -D, so the shipped behavior is unchanged.
            if (!proofUniq) {
                List<String> r1;
                List<String> r2;
                try {
                    r1 = executeQuery(q);
                    if (r1 == null) return;
                    globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS defidx_" + tbl
                            + "_c0c3 ON " + tbl + " (c0, c3);", errors, true));
                    analyzeTolerantForce(tbl);
                    // Require r2 to ACTUALLY ride the new index; else this round proves nothing about defidx -> skip.
                    String planAfter = String.join("\n", getExplainPlan(q));
                    if (!(planAfter.contains("defidx_") && (planAfter.contains("Index Scan")
                            || planAfter.contains("Index Only Scan") || planAfter.contains("Bitmap Index Scan")))) return;
                    // FAULT self-proof: a per-row-false filter that STILL rides defidx (c3 is in the index, so
                    // `c3 <> c3` is an index Filter, never constant-folded) empties r2 -> r2 != r1 whenever r1 is
                    // non-empty -> must throw. Ships OFF -> r2 == r1.
                    String q2 = FAULT ? q + " AND c3 <> c3" : q;
                    r2 = executeQuery(q2);
                } catch (Exception e) {
                    return;
                }
                if (r2 == null) return;
                log(q);
                compareValueIdentityStrict(r1, r2, "IDXDEF_CREATE q: " + q, "PG_IDXDEF_CREATE");
            }

            // Real value-identity probe on the UNIQUE index (replaces the old folded COUNT(*) invariant, which
            // was both tautological — a plain/unique index never changes count(*) — and FAULT-inert — its fault
            // only perturbed the CREATE differential above, never the counts). Create defuniq on the unique cb,
            // sample k existing cb values, and run `cb IN (...)` (armA rides defuniq, live-verified Index(-Only)
            // Scan) vs the wrapped `least(cb,cb) IN (...)` (armB forced Seq Scan). Key-only projection + no LIMIT
            // ⇒ no inheritance-tie hazard; multiset compare. FAULT: NOT-wrap selects the complement row set.
            try {
                globalState.executeStatement(new SQLQueryAdapter("CREATE UNIQUE INDEX IF NOT EXISTS defuniq_" + tbl
                        + "_cb ON " + tbl + " (cb);", errors, true));
                analyzeTolerantForce(tbl);
                long k = r.getInteger(3, 12);
                List<String> cbs = executeQuery("SELECT cb FROM " + tbl + " ORDER BY cb LIMIT " + k);
                if (cbs == null || cbs.isEmpty()) return;
                String inList = String.join(", ", cbs);
                String primB = "least(cb, cb) IN (" + inList + ")";
                String whereA = "cb IN (" + inList + ")";
                String whereB = FAULT ? "NOT (" + primB + ")" : primB;
                String uqA = "SELECT cb FROM " + tbl + " WHERE " + whereA;
                String uqB = "SELECT cb FROM " + tbl + " WHERE " + whereB;
                String uplanA = String.join("\n", getExplainPlan(uqA));
                String uplanB = String.join("\n", getExplainPlan(uqB));
                // armA must ride defuniq via an index scan; armB (wrapped) must fall to a Seq Scan (no index).
                boolean uideA = uplanA.contains("defuniq_") && (uplanA.contains("Index Scan")
                        || uplanA.contains("Index Only Scan") || uplanA.contains("Bitmap Index Scan"));
                if (!uideA) return;
                if (!(uplanB.contains("Seq Scan") && !uplanB.contains("Index"))) return;
                List<String> uA = executeQuery(uqA);
                List<String> uB = executeQuery(uqB);
                if (uA == null || uB == null) return;
                log(uqA);
                log(uqB);
                compareValueIdentityStrict(uA, uB, "IDXDEF_UNIQCOUNT A: " + uqA + " | B: " + uqB,
                        "PG_IDXDEF_UNIQCOUNT");
            } catch (Exception e) {
                return;
            }
        } finally {
            dropOwnIndexQuietly("defidx_" + tbl + "_c0c3");
            dropOwnIndexQuietly("defuniq_" + tbl + "_cb");
        }
    }

    /**
     * INDEX-DEFINITION axis (case 24). Symmetric to {@link #checkIndexDefinitionConsistency}: ensures OUR own
     * {@code defidx_<tbl>_c0c3} exists, runs the controlled deterministic query, DROPs that index, and re-runs;
     * the row set must be identical. Only ever drops an index WE created — never a seed {@code idx_<n>_*} index
     * (which other shapes name-gate on). Same determinism / no-mid-DML soundness argument.
     */
    private void checkIndexDropConsistency() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        Randomly r = globalState.getRandomly();
        long v1 = r.getInteger(-32768, 32767);
        long v2 = v1 + r.getInteger(0, 200);
        // Mirror of case 23: covering (c0, c3) projection so defidx is the winning plan while it exists.
        String q = "SELECT c0, c3 FROM " + tbl + " WHERE c0 BETWEEN " + v1 + " AND " + v2;
        try {
            List<String> r1;
            List<String> r2;
            try {
                globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS defidx_" + tbl
                        + "_c0c3 ON " + tbl + " (c0, c3);", errors, true));
                analyzeTolerantForce(tbl);
                // r1 must ACTUALLY ride defidx; else dropping it proves nothing -> skip.
                String planWith = String.join("\n", getExplainPlan(q));
                if (!(planWith.contains("defidx_") && (planWith.contains("Index Scan")
                        || planWith.contains("Index Only Scan") || planWith.contains("Bitmap Index Scan")))) return;
                r1 = executeQuery(q);
                if (r1 == null) return;
                // The differential REQUIRES the drop before r2 (seq) is computed; the finally only mops up the
                // early-return / exception paths that leave defidx behind (which would starve case 23's before-plan).
                globalState.executeStatement(new SQLQueryAdapter("DROP INDEX IF EXISTS defidx_" + tbl + "_c0c3;",
                        errors, true));
                analyzeTolerant(tbl);
                // FAULT self-proof: a per-row-false filter empties r2 (now a Seq Scan) -> r2 != r1 when r1
                // non-empty -> must throw. Ships OFF -> r2 == r1.
                String q2 = FAULT ? q + " AND c3 <> c3" : q;
                // Post-drop teeth: re-EXPLAIN and confirm the DROP took effect — r2's plan must no longer
                // reference defidx. r1 already rode defidx (pre-drop gate), so a defidx-free r2 guarantees the
                // arms genuinely differ in index use. (A Seq-Scan requirement is wrong here: the <=200-wide
                // range is highly selective, so a sibling c0 index legitimately serves r2 — still a valid
                // index-change differential — and demanding Seq Scan would collapse yield to ~0.)
                String plan2 = String.join("\n", getExplainPlan(q2));
                if (plan2.contains("defidx_" + tbl + "_c0c3")) return;
                r2 = executeQuery(q2);
            } catch (Exception e) {
                return;
            }
            if (r2 == null) return;
            log(q);
            compareValueIdentityStrict(r1, r2, "IDXDEF_DROP q: " + q, "PG_IDXDEF_DROP");
        } finally {
            dropOwnIndexQuietly("defidx_" + tbl + "_c0c3");
        }
    }

    /**
     * ORDER-SENSITIVE axis (case 25). armA takes its order from a composite seed index ({@code idx_<n>_c0c1}
     * or {@code idx_<n>_c0c1c3}) with NO Sort node; armB wraps each key in {@code least(k,k)} so the index
     * cannot provide order → an explicit Sort (ground-truth order). Compared POSITIONALLY. Soundness vs ties:
     * the projection is EXACTLY the ORDER BY keys, so any two rows that tie on the keys are byte-identical in
     * the output — tie permutations (and the LIMIT boundary) are invisible, making the projected sequence
     * deterministic WITHOUT a unique tie-breaker. {@code least(c,c) ≡ c} in value, order, and rendering for
     * INT (c0/c1/c3 are NOT NULL). Uniform direction only, so the btree provides the order by a forward or
     * backward scan (mixed direction would force a Sort and simply fail the gate — sound, no FP).
     */
    private void checkCompositeOrderByIndexRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        String sfx = tbl.substring("idx_t".length());
        boolean three = Randomly.getBoolean();
        String keys = three ? "c0, c1, c3" : "c0, c1";
        String idxName = three ? "idx_" + sfx + "_c0c1c3" : "idx_" + sfx + "_c0c1";
        boolean asc = Randomly.getBoolean();
        String dir = asc ? "ASC" : "DESC";
        long k = globalState.getRandomly().getInteger(1, 200);
        String ob = "c0 " + dir + ", c1 " + dir + (three ? ", c3 " + dir : "");
        // FAULT self-proof (ships OFF): flip armB's sort direction so the top-k row sequence diverges while the
        // wrapper still forces an explicit Sort (the armB gate still accepts). armB ≡ armA when OFF.
        String dirB = FAULT ? (asc ? "DESC" : "ASC") : dir;
        String obW = "least(c0, c0) " + dirB + ", least(c1, c1) " + dirB
                + (three ? ", least(c3, c3) " + dirB : "");
        // B3 depth: ~50% of rounds add an identical OFFSET m (0..20) before LIMIT in BOTH arms. OFFSET is
        // absorbed by the Limit node (no Sort added), so armA's `!hasSortNode` gate holds; the projection is the
        // ordered keys themselves, so any boundary ties render byte-identically ⇒ the window skip stays FP-safe.
        String limOff = " LIMIT " + k + (Randomly.getBoolean()
                ? " OFFSET " + globalState.getRandomly().getInteger(0, 21) : "");
        String armA = "SELECT " + keys + " FROM " + tbl + " ORDER BY " + ob + limOff;
        String armB = "SELECT " + keys + " FROM " + tbl + " ORDER BY " + obW + limOff;
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && !hasSortNode(planA))) return;
            if (!(planB.contains("Sort  (cost") && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_ORD_COMPOSITE", true);
    }

    /**
     * ORDER-SENSITIVE axis (case 26). Uses {@code cb} (IDENTITY, UNIQUE, NOT NULL) as a TOTAL order key with
     * FULL projection ({@code SELECT *}) — this catches wrong-heap-tuple-in-order bugs the key-only shape
     * (case 25) cannot, since it inspects every column, not just the ordered keys. armA scans the dedicated
     * {@code nsordu_<tbl>_cb} btree in order with NO Sort; armB wraps the key ({@code least(cb,cb)}) → explicit
     * Sort. Compared POSITIONALLY. Soundness vs ties: {@code cb} is unique+not-null ⇒ a TOTAL order ⇒ no ties
     * anywhere (including at the LIMIT boundary) ⇒ a deterministic full-row sequence in both arms.
     * {@code least(cb,cb) ≡ cb} exact identity (INT).
     */
    private void checkUniqueOrderByIndexRewrite() throws Exception {
        PostgresTable table = pickBrinCbTable();
        if (table == null) return;
        String tbl = table.getName();
        boolean asc = Randomly.getBoolean();
        String dir = asc ? "ASC" : "DESC";
        String idxName = "nsordu_" + tbl + "_cb_" + (asc ? "a" : "d");
        long k = globalState.getRandomly().getInteger(1, 200);
        String armA = "SELECT * FROM " + tbl + " ORDER BY cb " + dir + " LIMIT " + k;
        // FAULT self-proof (ships OFF): flip armB's sort direction so the top-k row sequence diverges while the
        // wrapper still forces an explicit Sort (the armB gate still accepts). armB ≡ armA when OFF.
        String dirB = FAULT ? (asc ? "DESC" : "ASC") : dir;
        String armB = "SELECT * FROM " + tbl + " ORDER BY least(cb, cb) " + dirB + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (cb " + dir + ");", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && !hasSortNode(planA))) return;
            if (!(planB.contains("Sort  (cost") && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_ORD_UNIQUE", true);
    }

    /**
     * LEVER-3 UPPER-NODE (case 29). GROUP BY grouping over the indexed key. The index has only ever been a
     * leaf scan or scalar-aggregate input in the other shapes; here it feeds a GroupAggregate / HashAggregate.
     * armA groups by {@code c0} riding {@code idx_<t>_c0} (Index/Index-Only Scan → GroupAggregate over ordered
     * input, no Seq Scan); armB groups by the exact value-identity {@code least(c0,c0)} (non-sargable → Seq
     * Scan + aggregate). The grouping keys are row-for-row identical ({@code least(c0,c0) ≡ c0} incl. NULL) and
     * the aggregate is {@code count(*)} (no column argument → no aggregate-side asymmetry), so the (key,count)
     * multiset is provably equal → any mismatch is a real index bug driving choose_hashed_grouping /
     * index-ordered-input GroupAggregate. Order-insensitive → {@code compareValueIdentityStrict} (multiset). FAULT
     * shifts the grouped/projected key by {@code +1} (a bijection that still forces a Seq Scan, so the armB
     * gate accepts it) → every projected key differs → the (key,count) multiset diverges → must throw.
     */
    private void checkGroupByIndexRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c0")) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c0";
        String keyB = FAULT ? wrap + " + 1" : wrap;
        // ORDER BY the grouping key: forces armA to GroupAggregate over the ordered Index-Only Scan (avoids
        // the explicit Sort a HashAggregate would need), making the index-under-GroupAggregate path win
        // regardless of c0 cardinality; armB's wrapped key still can't match the index → Seq Scan + Sort.
        String armA = "SELECT c0, count(*) FROM " + tbl + " GROUP BY c0 ORDER BY c0";
        String armB = "SELECT " + keyB + ", count(*) FROM " + tbl + " GROUP BY " + keyB + " ORDER BY " + keyB;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c0);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take index-ORDERED input to the GroupAggregate: an Index(-Only) Scan with NO Sort.
            // In this single-table query that combination can only arise from a c0-ordered index (ANY c0 index
            // — prebuilt idx_<t>_c0 / _c0desc / _c0c1, the covering index, or an nsbm_ clone created by the
            // bitmap shape), so gate on the STRUCTURE (index scan + no Sort), NOT a pinned index name: pinning
            // one name silently discards the round whenever the planner picks an equally valid sibling c0
            // index. armB's ORDER BY on the wrapped key can never be index-ordered, so it ALWAYS carries a
            // Sort. The Sort is the reliable discriminator; FP-safety rests only on least(c0,c0)≡c0.
            if (!((planA.contains("Index Only Scan") || planA.contains("Index Scan")) && !hasSortNode(planA)
                    && planA.contains("GroupAggregate"))) return;
            // armB's mandatory Sort IS the positive non-index-order confirmation (the wrapped key can never be
            // index-ordered). Do NOT additionally pin the index name: armB legitimately index-only-scans a c0
            // index to FEED that Sort, so a name-pin over-rejects valid rounds (proven inert on the sibling
            // merge-join shape). FP-safety rests on the Sort + least(c0,c0)≡c0.
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GROUPBY");
    }

    /**
     * LEVER-3 UPPER-NODE (case 30). DISTINCT over the indexed key. armA {@code SELECT DISTINCT c0 ... ORDER BY c0}
     * rides a c0 index as a {@code Unique} over an ordered index scan (NO Sort — PG 17.6 has no DISTINCT skip
     * scan); armB {@code SELECT DISTINCT least(c0,c0)} (non-sargable → Seq Scan + Sort + HashAggregate/Unique).
     * The projection is the key ONLY (no other column can diverge) and {@code least(c0,c0) ≡ c0} exactly (incl.
     * NULL), so the distinct set is provably equal → any mismatch is a real index bug driving sorted
     * Unique-over-index vs hash-distinct. The {@code Unique}-node gate proves the sorted (index-ordered) DISTINCT
     * path, not a HashAggregate. Compared with {@code compareValueIdentityStrict} (multiset-strict). FAULT shifts
     * the distinct expression by {@code +1} (still non-sargable → armB gate accepts) → the set shifts → must throw.
     */
    private void checkDistinctIndexRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c0")) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c0";
        String keyB = FAULT ? wrap + " + 1" : wrap;
        // ORDER BY the distinct key: forces armA to Unique over the ordered Index-Only Scan (no Sort), so the
        // index-under-Unique path wins regardless of c0 cardinality; armB's wrapped key → Seq Scan + Sort.
        String armA = "SELECT DISTINCT c0 FROM " + tbl + " ORDER BY c0";
        String armB = "SELECT DISTINCT " + keyB + " FROM " + tbl + " ORDER BY " + keyB;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c0);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA takes index-ORDERED input to Unique: an Index(-Only) Scan with NO Sort. In this single-table
            // query that can only come from a c0-ordered index (ANY c0 index — prebuilt idx_<t>_c0 / _c0desc /
            // _c0c1, the covering index, or an nsbm_ clone from the bitmap shape), so gate on the STRUCTURE
            // (index scan + no Sort), NOT a pinned index name, which would discard the round whenever an
            // equally valid sibling c0 index wins. armB's ORDER BY on the wrapped key can never be
            // index-ordered → it ALWAYS carries a Sort. FP-safety rests only on least(c0,c0)≡c0.
            if (!((planA.contains("Index Only Scan") || planA.contains("Index Scan")) && !hasSortNode(planA)
                    && planA.contains("Unique"))) return;
            // armB's mandatory Sort is the positive non-index-order confirmation (wrapped key can't be
            // index-ordered). Do NOT pin idxName: armB legitimately index-only-scans a c0 index to FEED the Sort.
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_DISTINCT");
    }

    /**
     * LEVER-3 UPPER-NODE (case 31). Window function over index-provided ordering. Uses the UNIQUE column
     * {@code cb} (IDENTITY, NOT NULL ⇒ a TOTAL order, no ties anywhere) via {@code pickBrinCbTable}. The window
     * function is randomized: a ranking func (row_number/rank/dense_rank, no frame) or a framed aggregate
     * (count(*)/sum(c1) with {@code ROWS BETWEEN n PRECEDING AND CURRENT ROW}). armA's {@code OVER (ORDER BY cb)}
     * rides a dedicated {@code nswin_<tbl>_cb} btree so the index satisfies BOTH the window ORDER BY and the
     * outer ORDER BY → WindowAgg over an index scan with NO Sort; armB wraps the window order in
     * {@code least(cb,cb)} (not index-matchable) → a Sort feeds the WindowAgg. Because {@code cb} is unique the
     * window output {@code w} is a deterministic function of {@code cb} ⇒ identical {@code (cb, w)} sequence in
     * both arms (both finally ordered by bare {@code cb}), FP-safe. Order-sensitive → {@code compareResultsOrdered}
     * (positional). FAULT flips the window order to {@code least(cb,cb) DESC} in armB only (direction, not
     * {@code +1} which stays rank/frame-monotone under the index) → the per-row window value diverges → must throw.
     */
    private void checkWindowIndexRewrite() throws Exception {
        PostgresTable table = pickBrinCbTable();
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "nswin_" + tbl + "_cb";
        // Randomize the window function: ranking funcs (no frame allowed) vs framed aggregates. Both arms use the
        // SAME func; armB differs only in the window ORDER BY expression (least(cb,cb)[ DESC]). cb is UNIQUE NOT
        // NULL ⇒ a total order ⇒ the per-row window value is a deterministic function of cb in both arms.
        boolean useAgg = Randomly.getBoolean();
        String fn;
        String frame = "";
        if (useAgg) {
            fn = Randomly.fromOptions("count(*)", "sum(c1)");
            int n = Randomly.fromOptions(1, 2, 3, 4);
            frame = " ROWS BETWEEN " + n + " PRECEDING AND CURRENT ROW";
        } else {
            fn = Randomly.fromOptions("row_number()", "rank()", "dense_rank()");
        }
        String winB = (FAULT ? "least(cb, cb) DESC" : "least(cb, cb)") + frame;
        String armA = "SELECT cb, c0, c1, " + fn + " OVER (ORDER BY cb" + frame + ") w FROM " + tbl + " ORDER BY cb";
        String armB = "SELECT cb, c0, c1, " + fn + " OVER (ORDER BY " + winB + ") w FROM " + tbl + " ORDER BY cb";
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (cb);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("WindowAgg") && !hasSortNode(planA))) return;
            if (!(planB.contains("WindowAgg") && hasSortNode(planB))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_WINDOW", true);
    }

    /**
     * LEVER-3 UPPER-NODE (case 35). Incremental Sort fed by an index-ordered prefix. armA
     * {@code SELECT c0,c1,cb ... ORDER BY c0,c1,cb LIMIT k} rides {@code idx_<sfx>_c0} for the c0 PREFIX → an
     * Incremental Sort finishes the (c1,cb) tail within each c0 group; armB wraps the prefix key in
     * {@code least(c0,c0)} (not index-matchable) → a single full Sort. The {@code LIMIT} is what makes the
     * planner PREFER the Incremental Sort for armA (it can stop after k rows without sorting the whole table);
     * without it, a full Sort over a Seq Scan is cheaper and the gate never fires. {@code cb} is UNIQUE NOT
     * NULL (pickBrinCbTable), so {@code (c0,c1,cb)} is a TOTAL order — no tie non-determinism — so the top-k is
     * a deterministic function of the data; {@code least(c0,c0) ≡ c0} ⇒ the identical k-row sequence in both
     * arms by construction. Order-sensitive under a total order → compareResultsOrdered (positional, already
     * strict). FAULT flips the prefix to {@code least(c0,c0) DESC} in armB only (direction, not +1 which stays
     * ascending) → the top-k picks the OPPOSITE end → the sequence diverges → positional mismatch → must throw.
     */
    private void checkIncrementalSortRewrite() throws Exception {
        PostgresTable table = pickBrinCbTable();
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c0";
        String prefixB = FAULT ? "least(c0, c0) DESC" : "least(c0, c0)";
        // LIMIT makes Incremental Sort the cheaper plan for armA (early stop). Same k in both arms; under the
        // total order (c0,c1,cb) the top-k is deterministic, so the LIMIT is FP-safe for the ordered compare.
        long k = Randomly.getNotCachedInteger(20, 200);
        String armA = "SELECT c0, c1, c2, c5, cb FROM " + tbl + " ORDER BY c0, c1, cb LIMIT " + k;
        String armB = "SELECT c0, c1, c2, c5, cb FROM " + tbl + " ORDER BY " + prefixB + ", c1, cb LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c0);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: the c0 index supplies the ORDER BY prefix → Incremental Sort over an Index(-Only) Scan.
            // armB: the wrapped prefix is not index-ordered → a single full Sort (NOT Incremental Sort).
            if (!(planA.contains("Incremental Sort")
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan")))) return;
            if (!(hasSortNode(planB) && !planB.contains("Incremental Sort"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_INCRSORT", true);
    }

    /**
     * LEVER-3 UPPER-NODE (case 36). Index-ordered inputs feed a Merge Join. CROSS-TABLE equi-join on the
     * indexed key c0 between two DISTINCT index-friendly tables (idx_t0 / idx_t1), both owning {@code
     * idx_<sfx>_c0}: armA {@code ... ON a.c0 = b.c0} lets both sides ride a c0-ordered Index(-Only) Scan → a
     * Merge Join with NO Sort (the index supplies the order); armB wraps the left join key {@code
     * least(a.c0,a.c0)} (not index-matchable) so the planner can no longer merge on an index-ordered input. A
     * cross-table join of two large c0-ordered scans is likelier to pick a Merge Join than an equi-sized
     * SELF-join (where a Hash Join almost always wins). No ORDER BY ⇒ the join output is a SET → multiset
     * equality via compareValueIdentityStrict. {@code least(a.c0,a.c0) ≡ a.c0} for every row incl. NULL (a NULL
     * c0 never equi-joins in EITHER arm) ⇒ the matched-row multiset is identical by construction ⇒ any mismatch
     * is a real index/merge-join bug. FAULT shifts the left key to {@code least(a.c0,a.c0) + 1 = b.c0} → a
     * different set of rows matches → multiset mismatch → must throw. YIELD: the planner may still prefer a Hash
     * Join; the gate then discards the round (FP-safe — it never flags).
     */
    private void checkMergeJoinRewrite() throws Exception {
        // Gather DISTINCT index-friendly base tables (idx_t0 / idx_t1) that own a wrappable c0.
        List<PostgresTable> cands = new ArrayList<>();
        for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
            if (t.isView() || t.isPartitioned()) continue;
            if (!t.getName().startsWith("idx_t")) continue;
            PostgresColumn c0 = null;
            for (PostgresColumn c : t.getColumns()) {
                if (c.getName().equals("c0")) { c0 = c; break; }
            }
            if (c0 != null && nonSargableWrapFor(c0, "a.c0") != null) cands.add(t);
        }
        if (cands.size() < 2) return;
        PostgresTable ta = Randomly.fromList(cands);
        PostgresTable tb = null;
        for (PostgresTable t : cands) {
            if (t != ta) { tb = t; break; }
        }
        if (tb == null) return;
        String a = ta.getName();
        String b = tb.getName();
        PostgresColumn c0a = null;
        for (PostgresColumn c : ta.getColumns()) {
            if (c.getName().equals("c0")) { c0a = c; break; }
        }
        String wrap = nonSargableWrapFor(c0a, "a.c0");
        if (wrap == null) return;
        String idxA = "idx_" + a.substring("idx_t".length()) + "_c0";
        String idxB = "idx_" + b.substring("idx_t".length()) + "_c0";
        String keyB = FAULT ? wrap + " + 1" : wrap;
        String armA = "SELECT a.c0, b.c1 FROM " + a + " a JOIN " + b + " b ON a.c0 = b.c0";
        String armB = "SELECT a.c0, b.c1 FROM " + a + " a JOIN " + b + " b ON " + keyB + " = b.c0";
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxA
                    + " ON " + a + " (c0);", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxB
                    + " ON " + b + " (c0);", errors, true));
            analyzeTolerant(a);
            analyzeTolerant(b);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: both inputs c0-ordered via a c0 index → Merge Join with NO Sort.
            if (!(planA.contains("Merge Join")
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"))
                    && !hasSortNode(planA))) return;
            // armB must NOT be an index-ordered merge too: the wrapped key can't ride a c0 index, so a correct
            // planner either sorts for the merge or switches strategy. Discard if armB is still a no-Sort merge.
            // Do NOT also pin idxA: armB legitimately index-only-scans a-side c0 to feed its Sort for the merge,
            // so a name-pin over-rejects every valid round (proven to make FAULT inert).
            if (planB.contains("Merge Join") && !hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_MERGEJOIN");
    }

    /**
     * PAYLOAD axis (case 37). Fixes the SELECT-* blind spot: every other shape projects {@code *}, so a bug in
     * an INDEX-STORED payload (an INCLUDE column served without a heap fetch) is invisible. The prebuilt
     * {@code idx_<t>_cover ON (c0) INCLUDE (c3, c4)} lets armA {@code SELECT c0, c3, c4 ... WHERE c0 = V} be an
     * Index Only Scan that returns c3/c4 straight from the index; armB wraps the key {@code least(c0,c0) = V}
     * (not index-matchable) → a Seq Scan that returns c3/c4 from the HEAP. The seed VACUUM set the visibility
     * map all-visible (no mid-round DML), so the Index Only Scan is actually chosen and reads the index payload;
     * any index/heap payload divergence for a visible row is a real index bug. SET (no ORDER BY) →
     * compareValueIdentityStrict. FAULT NOT-wraps armB's predicate → the complement row set → must throw.
     */
    private void checkIndexOnlyPayloadRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c0")) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_cover";
        // A MODERATE in-domain range (not equality): with many matching rows a plain Index Scan would fetch
        // c3,c4 from the heap for every row, so the planner decisively prefers the cover's Index Only Scan
        // (no heap). Equality (1 row) makes a narrow single-key index cheaper, so the cover is rarely chosen.
        int lo = (int) Randomly.getNotCachedInteger(-32768, 32000);
        int hi = lo + (int) Randomly.getNotCachedInteger(200, 4000);
        String primA = "c0 >= " + lo + " AND c0 <= " + hi;
        String primB = wrap + " >= " + lo + " AND " + wrap + " <= " + hi;
        String armA = "SELECT c0, c3, c4 FROM " + tbl + " WHERE " + primA;
        // armB must read the c3,c4 payload from the HEAP, not from any index. Wrapping c0 in least/greatest
        // alone is NOT enough: the projection {c0,c3,c4} is fully covered, so the planner serves armB as a
        // full Index Only Scan on idx_<t>_cover with the non-sargable term as a Filter — both arms would then
        // read the payload from the SAME index, making the differential tautological. The value-neutral
        // (always-true, NULL-safe) term `c5 IS NOT DISTINCT FROM c5` references c5, which no covering index
        // holds, so an index-only scan is structurally impossible → the planner must Seq Scan the heap.
        String primBHeap = "(" + (FAULT ? "NOT (" + primB + ")" : primB) + ") AND c5 IS NOT DISTINCT FROM c5";
        String armB = "SELECT c0, c3, c4 FROM " + tbl + " WHERE " + primBHeap;
        List<String> rA;
        List<String> rB;
        try {
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must be an Index ONLY Scan on the covering index (payload from the index, no heap fetch) —
            // only idx_<t>_cover covers {c0,c3,c4}. armB must be an index-free Seq Scan (payload from the heap).
            if (!(planA.contains("Index Only Scan") && planA.contains(idxName))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_IOPAYLOAD");
    }

    /**
     * KNN axis (case 38). GiST nearest-neighbour distance ordering — a path no other shape covers. armA
     * {@code ... ORDER BY gp <-> point '(px,py)', cb LIMIT k} rides the {@code idx_<t>_gpgist} GiST index as a
     * KNN Index Scan (plan shows an "Order By:" on the index node) returning rows in ascending distance; armB
     * replaces the column with the exact value-identity {@code point(gp[0], gp[1])} (gp's coords are
     * integer-valued float8, 0..999, so the reconstruction is bit-exact), which the planner cannot match to the
     * GiST index → a Sort. The distance is computed from identical operands in both arms ⇒ bit-identical; {@code
     * cb} (UNIQUE NOT NULL) is a total tie-breaker so equidistant points have a DETERMINISTIC order and {@code
     * LIMIT k} cuts both arms at the identical k rows. Order-sensitive → compareResultsOrdered (positional).
     * FAULT shifts ONLY armB's target to {@code point '(px+1,py)'} → the nearest-k ordering diverges → must throw.
     */
    private void checkKnnOrderRewrite() throws Exception {
        PostgresTable table = pickGinTable("gp");
        if (table == null) return;
        String tbl = table.getName();
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_gpgist";
        int px = (int) Randomly.getNotCachedInteger(0, 1000);
        int py = (int) Randomly.getNotCachedInteger(0, 1000);
        int k = (int) Randomly.getNotCachedInteger(1, 11);
        String target = "point '(" + px + "," + py + ")'";
        String targetB = FAULT ? "point '(" + (px + 1) + "," + py + ")'" : target;
        String distA = "gp <-> " + target;
        String distB = "point(gp[0], gp[1]) <-> " + targetB;
        String armA = "SELECT cb, c0, c1, (" + distA + ") AS d FROM " + tbl + " ORDER BY " + distA + ", cb LIMIT " + k;
        String armB = "SELECT cb, c0, c1, (" + distB + ") AS d FROM " + tbl + " ORDER BY " + distB + ", cb LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gist(gp);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: the GiST index supplies the distance ("Order By:") order; armB: the reconstructed point
            // forces a Sort and must NOT ride the KNN index.
            if (!(planA.contains(idxName) && planA.contains("Order By"))) return;
            if (!(planB.contains("Sort  (cost") && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_KNN", true);
    }

    /**
     * ROW-COMPARATOR axis (case 39). Composite row comparison descent — a path no scalar shape covers. armA
     * {@code ... WHERE (c0, c1) > (x, y)} rides a c0,c1-leading composite index ({@code idx_<t>_c0c1} /
     * {@code _c0c1c3}) as a single multi-column Index Cond ({@code ROW(c0,c1) > ROW(x,y)} — a true two-key
     * boundary descent, not a c0-only range + filter); armB wraps ONLY the leading key
     * {@code (least(c0,c0), c1) > (x, y)} (not index-matchable) → a Seq Scan. c0/c1 are INT NOT NULL and
     * {@code least(c0,c0) ≡ c0} exactly ⇒ the row sets are provably equal ⇒ any mismatch is a real
     * composite-index row-comparator bug. SET (no ORDER BY) → compareValueIdentityStrict. FAULT NOT-wraps armB's
     * (non-sargable) predicate → the complement row set → must throw.
     */
    private void checkRowComparisonRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        PostgresColumn c1col = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c0")) c0col = c;
            else if (c.getName().equals("c1")) c1col = c;
        }
        if (c0col == null || c1col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String x = generateDataAwareValueForType(tbl, c0col);
        String y = generateDataAwareValueForType(tbl, c1col);
        if (x == null || "NULL".equalsIgnoreCase(x) || y == null || "NULL".equalsIgnoreCase(y)) return;
        // Row-comparator operator variety: every row-comparison operator descends the composite index as a single
        // ROW(...) Index Cond (not a c0-only range + filter). Both arms use the SAME op ⇒ value-identity holds.
        String op = Randomly.fromOptions(">", ">=", "<", "<=");
        String primB = "(" + wrap + ", c1) " + op + " (" + x + ", " + y + ")";
        String armA = "SELECT * FROM " + tbl + " WHERE (c0, c1) " + op + " (" + x + ", " + y + ")";
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        List<String> rA;
        List<String> rB;
        try {
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride a c0,c1-leading composite index as a row-comparison Index Cond; armB's wrapped
            // leading key forces an index-free Seq Scan.
            if (!(planA.contains("_c0c1") && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_ROWCMP");
    }

    /**
     * GIN-INTERSECTION axis (case 40). Multi-element containment {@code @>} forcing a GIN posting-list
     * INTERSECTION (two required entries), a path the single-entry GIN shapes (16/17/19) don't exercise. On a
     * random pick: jsonb {@code gj @> '{"k": V, "gN": true}'} (two object keys) rides a gj GIN (jsonb_ops
     * {@code idx_<t>_gjgin} OR jsonb_path_ops {@code idx_<t>_gjpgin} — both index {@code @>}); array
     * {@code ga @> ARRAY[x, y]} (two elements) rides {@code idx_<t>_gagin}. armB wraps the column in the exact
     * value-identity {@code least(gj,gj)} / {@code least(ga,ga)} (total btree order → returns the same type, so
     * {@code @>} still applies, incl. NULL → SQL NULL on both operands → 3VL-false in BOTH arms), which the
     * planner cannot match to a GIN index → a Seq Scan. Row sets provably equal → any mismatch is a real GIN
     * bug. SET → compareValueIdentityStrict. FAULT NOT-wraps armB → the complement (non-NULL) row set → throws.
     */
    private void checkGinContainmentRewrite() throws Exception {
        boolean jsonb = Randomly.getBoolean();
        String colName = jsonb ? "gj" : "ga";
        PostgresTable table = pickGinTable(colName);
        if (table == null) return;
        String tbl = table.getName();
        String armA;
        String primB;
        if (jsonb) {
            long v = Randomly.getNotCachedInteger(0, 100);
            long g = Randomly.getNotCachedInteger(0, 100);
            String rhs = "'{\"k\": " + v + ", \"g" + g + "\": true}'::jsonb";
            armA = "SELECT * FROM " + tbl + " WHERE gj @> " + rhs;
            primB = "least(gj, gj) @> " + rhs;
        } else {
            long x = Randomly.getNotCachedInteger(0, 100);
            long y = Randomly.getNotCachedInteger(0, 100);
            String rhs = "ARRAY[" + x + ", " + y + "]";
            armA = "SELECT * FROM " + tbl + " WHERE ga @> " + rhs;
            primB = "least(ga, ga) @> " + rhs;
        }
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride a GIN index via a Bitmap Index Scan (GIN's only plan shape); armB wrapped → Seq.
            boolean armAIndexed = planA.contains("Bitmap Index Scan")
                    && (jsonb ? (planA.contains("_gjgin") || planA.contains("_gjpgin")) : planA.contains("_gagin"));
            if (!armAIndexed) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_GINCONT");
    }

    /**
     * CROSS-TYPE / implicit-cast axis (case 42). All other scalar shapes compare the indexed column to a
     * literal of its OWN type; this one compares the int4 column {@code c0} to a {@code ::bigint} (int8)
     * literal. PostgreSQL's integer btree operator family provides the native cross-type {@code int4 <op> int8}
     * operators, so {@code c0 <op> v::bigint} keeps {@code c0} bare and still rides {@code idx_<t>_c0*} as an
     * Index Cond (the planner does NOT cast {@code c0} up to numeric here, which would strip sargability — that
     * variant just misses the gate and is skipped). armB wraps ONLY the key in the exact value-identity
     * {@code least(c0,c0)}, which the planner cannot match to any index → a Seq Scan; the int4↔int8 comparison
     * is mathematically identical in both arms for every int4 value, so the row sets are provably equal → any
     * post-gate mismatch is a real cross-type-operator / index bug. {@code v} is sampled from an actual heap
     * {@code c0} so the equality reliably rides a selective Index Cond (a random range bound mostly went Seq
     * Scan → ~0 gate yield) and the NOT-wrap FAULT self-proof fires on every gated round.
     * SET → {@link #compareValueIdentityStrict}. Ships with FAULT OFF ⇒ armB ≡ armA.
     */
    private void checkCrossTypeCastRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = table.getColumns().stream()
                .filter(c -> "c0".equals(c.getName())).findFirst().orElse(null);
        if (c0col == null) return;
        // Sample an ACTUAL c0 so armA's equality is maximally selective → the planner reliably picks the
        // cross-type Index Cond (a random range bound mostly went Seq Scan → ~0 gate yield), and the probe
        // matches ≥1 row so the FAULT NOT-wrap set genuinely differs. Fall back to a bounded random int.
        long v;
        try {
            List<String> vr = executeQuery(
                    "SELECT c0 FROM " + tbl + " WHERE c0 IS NOT NULL ORDER BY random() LIMIT 1");
            if (vr != null && !vr.isEmpty() && vr.get(0) != null && !vr.get(0).trim().isEmpty()) {
                v = Long.parseLong(vr.get(0).trim());
            } else {
                v = globalState.getRandomly().getInteger(0, 32767);
            }
        } catch (Exception e) {
            return; // c0 not integer-ish here → skip cleanly
        }
        // ~50% of rounds probe a NARROW cross-type RANGE around the sampled v (a wide/random range mostly went
        // Seq Scan → ~0 gate yield, per the equality lesson); a small window keeps armA selective enough to ride
        // the cross-type Index Cond. Both bounds are ::bigint; armB wraps ONLY c0 (value-identity).
        String primB;
        String armA;
        if (Randomly.getBoolean()) {
            long window = globalState.getRandomly().getInteger(0, 50);
            String lo = (v - window) + "::bigint";
            String hi = (v + window) + "::bigint";
            armA = "SELECT * FROM " + tbl + " WHERE c0 BETWEEN " + lo + " AND " + hi;
            primB = "least(c0, c0) BETWEEN " + lo + " AND " + hi;
        } else {
            String rhs = v + "::bigint"; // force the int4 = int8 cross-type operator on the RHS literal
            armA = "SELECT * FROM " + tbl + " WHERE c0 = " + rhs;
            primB = "least(c0, c0) = " + rhs;
        }
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        List<String> rA;
        List<String> rB;
        try {
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride a c0 btree via the cross-type Index Cond; require the Index Cond LINE to reference
            // c0 specifically (not merely "idx_" anywhere, which a decoy index on another column could satisfy).
            // c0..c7/cb are mutually non-substring, so a plain contains on the cond line is unambiguous.
            boolean armARidesC0 = false;
            for (String pl : planA.split("\n")) {
                if (pl.contains("Index Cond") && pl.contains("c0")) { armARidesC0 = true; break; }
            }
            if (!armARidesC0) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_CAST");
    }

    /**
     * FULL-TEXT GIN axis (case 43). The only shape that exercises a functional GIN over
     * {@code to_tsvector('english', c5)} — a whole index-access behavior with zero prior coverage. armA rides the
     * runtime-built {@code tsvidx_<t>_c5} via a {@code @@ plainto_tsquery} match (GIN's only plan shape, a Bitmap
     * Index Scan); armB wraps the indexed expression's INPUT in the exact value-identity {@code least(c5,c5)≡c5}
     * (text, NOT NULL) — the planner cannot match the functional index on the wrapped input → a pure heap Seq
     * Scan (index-independent ground truth). The query lexeme is sampled from {@code ts_stat} ordered by the LEAST
     * document frequency, so it is GUARANTEED present (armA matches ≥1 row ⇒ gate + FAULT fire) AND selective
     * enough that the planner reliably picks the Bitmap Index Scan over a Seq Scan. {@code quote_literal} makes it
     * a ready SQL literal. FAULT self-proof: NOT-wrap armB's predicate so its match set flips to the complement ⇒
     * the row set diverges while the wrapped input keeps armB a Seq Scan. Ships OFF ⇒ armB ≡ armA.
     */
    private void checkTsvectorRewrite() throws Exception {
        PostgresTable table = pickGinTable("c5");
        if (table == null) return;
        String tbl = table.getName();
        // Sample a lexeme GUARANTEED present in to_tsvector('english', c5), ordered by LEAST doc frequency so the
        // query is selective (reliable Bitmap Index Scan rather than a Seq Scan). quote_literal → ready literal.
        String word;
        try {
            List<String> wr = executeQuery(
                    "SELECT quote_literal(word) FROM ts_stat('SELECT to_tsvector(''english'', c5) FROM "
                            + tbl + "') ORDER BY ndoc ASC, word LIMIT 1");
            if (wr == null || wr.isEmpty() || wr.get(0) == null || wr.get(0).trim().isEmpty()) return;
            word = wr.get(0).trim();
        } catch (Exception e) {
            return; // no indexable lexeme (all-empty / all-stopword c5) → skip cleanly
        }
        String idxName = "tsvidx_" + tbl + "_c5";
        // Operator-form variety: the query lexeme (a single normalized token from ts_stat) matches identically
        // under every tsquery constructor, so BOTH arms use the SAME one ⇒ value-identity holds; a bad parse
        // just skips the round (the EXPLAIN/exec is caught). Widens coverage of the GIN @@ match machinery.
        String tsqFn = Randomly.fromOptions("plainto_tsquery", "to_tsquery", "phraseto_tsquery",
                "websearch_to_tsquery");
        String tsq = tsqFn + "('english', " + word + ")";
        String primB = "to_tsvector('english', least(c5, c5)) @@ " + tsq;
        String armA = "SELECT * FROM " + tbl + " WHERE to_tsvector('english', c5) @@ " + tsq;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin(to_tsvector('english', c5));", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // GIN is accessed only via a Bitmap Index Scan; require the functional index by name.
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_TSV");
    }

    /**
     * SP-GiST axis (case 44). The only shape that exercises an SP-GiST (radix-tree) text index — a whole access
     * method with zero prior coverage. armA rides the prebuilt {@code idx_<t>_c7spgist} (the SOLE index on
     * {@code c7}, so equality has nothing else to ride) via an Index Cond; armB wraps {@code c7} in the exact
     * value-identity {@code least(c7,c7)≡c7} (text COLLATE "C", NOT NULL) → unmatchable → Seq Scan. The probe
     * {@code v} is sampled from an ACTUAL c7 (via {@code quote_literal} → ready literal) so armA matches ≥1 row
     * and the FAULT NOT-wrap set genuinely differs. FAULT self-proof: NOT-wrap armB's predicate. Ships OFF ⇒
     * armB ≡ armA. {@code compareValueIdentityStrict} tags PG_NS_SPGIST.
     */
    private void checkSpGistTextRewrite() throws Exception {
        PostgresTable table = pickGinTable("c7");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c7col = table.getColumns().stream()
                .filter(c -> "c7".equals(c.getName())).findFirst().orElse(null);
        if (c7col == null) return;
        // Sample up to 2 ACTUAL c7 values (as SQL literals) so armA matches ≥1 row and (for the range variant)
        // bounds a non-empty band. Fewer than 2 → fall back to the equality variant.
        java.util.List<String> lits = new java.util.ArrayList<>();
        try {
            List<String> vr = executeQuery(
                    "SELECT quote_literal(c7) FROM " + tbl + " WHERE c7 IS NOT NULL ORDER BY random() LIMIT 2");
            if (vr != null) {
                for (String s : vr) {
                    if (s != null && !s.trim().isEmpty()) {
                        lits.add(s.trim());
                    }
                }
            }
        } catch (Exception e) {
            return;
        }
        if (lits.isEmpty()) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c7spgist";
        String wrapped = nonSargableWrapFor(c7col, "c7");
        if (wrapped == null) return;
        // Variant selector: equality (as before) or a prefix/band RANGE between two sampled literals, which exercises
        // SP-GiST text's ordered (>=/<=) descent. least/greatest of the two constants fold at plan time so armA's
        // bounds are plan-time constants → c7 >= lo AND c7 <= hi rides the spgist Index Cond; the literal bounds are
        // byte-identical in both arms so both compute the SAME band. c7 is COLLATE "C" (explicit) and beats the
        // literals' implicit collation in the >=/<= comparison, so the band is deterministic byte order. armB wraps
        // the key (least(c7,c7)≡c7) in every term → not a plan-time constant on the LHS → Seq Scan.
        String predA;
        String primB;
        if (lits.size() >= 2 && Randomly.getBoolean()) { // range band
            String lo = "least(" + lits.get(0) + ", " + lits.get(1) + ")";
            String hi = "greatest(" + lits.get(0) + ", " + lits.get(1) + ")";
            predA = "c7 >= " + lo + " AND c7 <= " + hi;
            primB = wrapped + " >= " + lo + " AND " + wrapped + " <= " + hi;
        } else { // single equality
            predA = "c7 = " + lits.get(0);
            primB = wrapped + " = " + lits.get(0);
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + predA;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: the seed builds idx_<t>_c7spgist, but a prior shape in this DB may have dropped it;
            // IF NOT EXISTS re-creates it harmlessly (ExpectedErrors + caught).
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING spgist(c7);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_SPGIST");
    }

    /**
     * MIXED ASC/DESC composite-ordering axis (case 45). The only shape that exercises an index-provided sort with
     * mixed key directions. armA takes its order from the prebuilt {@code idx_<t>_mixord2 (c4 ASC, c0 DESC, cb ASC)}
     * with NO Sort node; armB wraps the LEAD key in both the WHERE and the ORDER BY ({@code least(c4,c4)≡c4}) → the
     * index no longer supplies the order → an explicit Sort over value-identical rows. The LEAD is the heavily-
     * duplicated c4 (~500 rows per hot value): the probe restricts to the 3 hottest c4 values and takes the
     * first-k by {@code (c4 ASC, c0 DESC, cb ASC)}, so the top-k lands inside dense c4 groups and the SECOND key
     * c0 is what actually orders it — crossing the c4 boundaries also exercises the ASC-then-DESC transition. The
     * projection {@code (c4, c0, cb)} with the unique IDENTITY {@code cb} is a TOTAL order, so positional
     * comparison is permutation-free ({@code totalOrder=true}). FAULT self-proof: flip the SECOND key's direction
     * in armB ({@code DESC→ASC}); because the top-k is inside one c4 group, flipping c0 reorders it ⇒ both the
     * order and (under LIMIT) the row set differ. Ships OFF ⇒ armB ≡ armA.
     */
    private void checkMixedOrderRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c4col = table.getColumns().stream()
                .filter(c -> "c4".equals(c.getName())).findFirst().orElse(null);
        if (c4col == null) return;
        String wrapped = nonSargableWrapFor(c4col, "c4");
        if (wrapped == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_mixord2";
        // Sample the 3 heaviest-duplicated c4 values at runtime so the top-k lands in dense groups regardless of
        // the per-table seed. Fewer than 3 distinct values -> too small a table to form the shape -> skip.
        List<String> hot = executeQuery(
                "SELECT c4 FROM " + tbl + " GROUP BY c4 ORDER BY count(*) DESC, c4 LIMIT 3");
        if (hot == null || hot.size() < 3) return;
        String inList = String.join(", ", hot);
        long k = globalState.getRandomly().getInteger(5, 50);
        String dir2 = FAULT ? "ASC" : "DESC"; // normal is DESC on the 2nd key c0; FAULT flips it ⇒ divergent top-k
        // B3 depth: ~50% of rounds add an identical OFFSET m (0..20) before LIMIT in BOTH arms. The trailing cb
        // (unique IDENTITY) makes the order TOTAL ⇒ no boundary ties ⇒ the window [m, m+k) is deterministic in
        // both arms even with the full projection ⇒ FP-safe. OFFSET rides the Limit node, adding no Sort.
        String limOff = " LIMIT " + k + (Randomly.getBoolean()
                ? " OFFSET " + globalState.getRandomly().getInteger(0, 21) : "");
        String armA = "SELECT c4, c0, c1, c5, cb FROM " + tbl + " WHERE c4 IN (" + inList
                + ") ORDER BY c4 ASC, c0 DESC, cb ASC" + limOff;
        String armB = "SELECT c4, c0, c1, c5, cb FROM " + tbl + " WHERE " + wrapped + " IN (" + inList
                + ") ORDER BY " + wrapped + " ASC, c0 " + dir2 + ", cb ASC" + limOff;
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take the order from mixord2 (no Sort node); armB's wrapped lead key forces an explicit
            // Sort. Gate on the Sort COST line ("Sort  (cost", two spaces) — a Merge Append etc. prints a decoy
            // "Sort Key:" property line that fools a bare contains("Sort").
            if (!(planA.contains(idxName) && !planA.contains("Sort  (cost"))) return;
            if (!planB.contains("Sort  (cost")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_MIXORD", true);
    }

    /**
     * HETEROGENEOUS BitmapAnd axis (case 46). The only shape that exercises a BitmapAnd combining a btree bitmap
     * with a GIN bitmap. armA restricts a {@code c0} RANGE (rides the prebuilt {@code idx_<t>_c0} btree bitmap)
     * AND a {@code gj @> '{"k":V}'} containment (rides the {@code idx_<t>_gjgin} GIN bitmap) → the planner AND-s
     * the two bitmaps (a BitmapAnd). A moderate c0 range (not a point) keeps neither index clearly dominant, so
     * the planner actually combines them. armB wraps BOTH indexed keys ({@code least(c0,c0)} and {@code least(gj,gj)},
     * each an exact value-identity) → neither index usable → Seq Scan. FAULT self-proof: NOT-wrap the whole armB
     * predicate ⇒ the row set flips to the complement while staying a Seq Scan. Ships OFF ⇒ armB ≡ armA. Sound-but
     * -low-yield is acceptable: if the planner prefers a single index + filter the gate simply discards the round.
     */
    private void checkHeteroBitmapRewrite() throws Exception {
        PostgresTable table = pickGinTable("gj");
        if (table == null) return;
        String tbl = table.getName();
        long center;
        try {
            List<String> vr = executeQuery(
                    "SELECT c0 FROM " + tbl + " WHERE c0 IS NOT NULL ORDER BY random() LIMIT 1");
            if (vr != null && !vr.isEmpty() && vr.get(0) != null && !vr.get(0).trim().isEmpty()) {
                center = Long.parseLong(vr.get(0).trim());
            } else {
                center = globalState.getRandomly().getInteger(-32768, 32767);
            }
        } catch (Exception e) {
            return;
        }
        // Moderate c0 band (~hundreds–thousand rows) so neither index alone dominates ⇒ the planner AND-s both
        // bitmaps. gj @> '{"k":V}' is ~1% (the gj DEFAULT seeds 'k' over 0..99).
        long window = globalState.getRandomly().getInteger(500, 4000);
        long lo = center - window;
        long hi = center + window;
        long jv = Randomly.getNotCachedInteger(0, 100);
        String jrhs = "'{\"k\":" + jv + "}'::jsonb";
        String primB = "least(c0, c0) BETWEEN " + lo + " AND " + hi + " AND least(gj, gj) @> " + jrhs;
        String armA = "SELECT * FROM " + tbl + " WHERE c0 BETWEEN " + lo + " AND " + hi + " AND gj @> " + jrhs;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        String[] deepPair = maybeDeepenC0(table, armA, armB); armA = deepPair[0]; armB = deepPair[1]; // ③ deepen
        String[] envPair = applyEnvelope(armA, armB); armA = envPair[0]; armB = envPair[1]; // envelope (experimental)
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must AND a btree bitmap on c0 with the gj GIN bitmap; confirm BOTH arms — the old
            // BitmapAnd+gjgin check left the btree(c0) side unverified. A "Bitmap Index Scan" line referencing
            // c0 pins the second arm regardless of which c0 btree the planner chose. armB must ride no index.
            boolean btreeC0Arm = false;
            for (String pl : planA.split("\n")) {
                if (pl.contains("Bitmap Index Scan") && pl.contains("c0")) { btreeC0Arm = true; break; }
            }
            if (!(planA.contains("BitmapAnd") && planA.contains("gjgin") && btreeC0Arm)) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_HETBITMAP");
    }

    /**
     * NULLS-PLACEMENT axis (case 47). The ONLY shape that exercises index-provided NULL ordering: the ~85%-NULL
     * {@code c2} column has a single index {@code idx_<t>_c2nulls (c2 DESC NULLS LAST)}. armA takes its
     * NULLS-LAST DESC order from that index (NO Sort); armB wraps the lead key in {@code least(c2,c2)} (an exact
     * value-identity INCLUDING NULL, since {@code least(NULL,NULL)=NULL}) so the planner cannot match the
     * functional expression to the plain-column index → an explicit Sort (ground-truth order). A small {@code
     * LIMIT k} top-k is where NULLS LAST vs FIRST diverges: with NULLS LAST the top-k are the largest NON-NULL
     * values; a NULL-misplacement bug would surface NULLs into that window and diverge from the Sort. Projection
     * is EXACTLY the sole ORDER BY key (c2), so equal-c2 ties AND the LIMIT boundary render identically → the
     * positional comparison is permutation-free without a unique tiebreak (the case-25 tie-invisibility argument).
     * FAULT self-proof (ships OFF): flip armB's NULLS placement to FIRST ⇒ its top-k becomes k NULL rows,
     * diverging from armA's non-null top-k ⇒ must throw. armB ≡ armA when OFF.
     */
    private void checkNullsOrderRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c2col = table.getColumns().stream()
                .filter(c -> "c2".equals(c.getName())).findFirst().orElse(null);
        if (c2col == null) return;
        String wrapped = nonSargableWrapFor(c2col, "c2");
        if (wrapped == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c2nulls";
        long k = globalState.getRandomly().getInteger(5, 50);
        String nullsB = FAULT ? "NULLS FIRST" : "NULLS LAST"; // FAULT flips placement ⇒ NULLs invade armB's top-k
        String armA = "SELECT c2 FROM " + tbl + " ORDER BY c2 DESC NULLS LAST LIMIT " + k;
        String armB = "SELECT c2 FROM " + tbl + " ORDER BY " + wrapped + " DESC " + nullsB + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take NULLS-LAST order from c2nulls (no Sort); armB's wrapped lead key forces a Sort.
            if (!(planA.contains(idxName) && !hasSortNode(planA))) return;
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_NULLSORD", true);
    }

    /**
     * TEXT index-provided ordering axis (case 48). The only shape that exercises an ordered scan over a TEXT key —
     * case 1 (checkOrderByIndexRewrite) deferred TEXT because its generic order wrapper has no COLLATE-aware form.
     * The target is {@code c7}, declared {@code TEXT COLLATE "C"}, so its btree {@code idx_<t>_c7btree} orders by
     * raw byte value: deterministic and immune to the ICU/locale collation nondeterminism that the amcheck path had
     * to seal. armA takes its order from that btree with NO Sort; armB wraps the key ({@code least(c7,c7)≡c7},
     * collation-"C"-preserving) → the planner cannot match the functional expression to the plain-column index →
     * an explicit Sort over value-identical rows. The projection is EXACTLY the sole ORDER BY key {@code c7}, so
     * equal-c7 ties AND the LIMIT boundary render byte-identically → the positional comparison is permutation-free
     * without a unique tiebreak (the case-25/47 tie-invisibility argument). FAULT self-proof (ships OFF): flip armB's
     * sort direction ⇒ the first-k rows reverse ⇒ must throw. armB ≡ armA when OFF.
     */
    private void checkTextOrderCollateRewrite() throws Exception {
        PostgresTable table = pickGinTable("c7");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c7col = table.getColumns().stream()
                .filter(c -> "c7".equals(c.getName())).findFirst().orElse(null);
        if (c7col == null) return;
        String wrapped = nonSargableWrapFor(c7col, "c7");
        if (wrapped == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_c7btree";
        long k = globalState.getRandomly().getInteger(5, 50);
        String dir = Randomly.getBoolean() ? "ASC" : "DESC";
        String dirB = FAULT ? ("ASC".equals(dir) ? "DESC" : "ASC") : dir; // FAULT flips armB's direction
        String armA = "SELECT c7 FROM " + tbl + " ORDER BY c7 " + dir + " LIMIT " + k;
        String armB = "SELECT c7 FROM " + tbl + " ORDER BY " + wrapped + " " + dirB + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: the seed builds idx_<t>_c7btree, but the name-unguarded drop path may have removed it.
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c7);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take the order from c7btree (no Sort); armB's wrapped key forces an explicit Sort.
            if (!(planA.contains(idxName) && !hasSortNode(planA))) return;
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_TEXTORD", true);
    }

    /**
     * COMBINED mixed-direction + NULLS-placement ordering axis (case 49). The only shape whose index-provided order
     * combines a mixed-direction composite with a NULLABLE key carrying explicit NULLS placement — a combination
     * neither case 45 (mixed-dir, both keys NOT NULL, no NULLS axis) nor case 47 (single-column NULLS) covers. The
     * NULLABLE key {@code c2} LEADS the index {@code idx_<t>_mixnulls (c2 DESC NULLS LAST, c0 DESC, cb ASC)} so its
     * NULLS placement dominates the top-k (c2 is ~65-85% NULL): leading with c2 is deliberate — an earlier design put
     * c2 second behind the near-unique c0, which made the NULLS flip inert (c0 alone fixed the top-k, so the FAULT
     * never diverged and the NULLS axis was never exercised). armA takes the full 3-key order from the composite index
     * with NO Sort; armB wraps the LEAD key ({@code least(c2,c2)≡c2} incl. NULL) → the index no longer supplies the
     * order → an explicit Sort over value-identical rows. The projection {@code (c2, c0, cb)} with the unique IDENTITY
     * {@code cb} is a TOTAL order, so positional comparison is permutation-free ({@code totalOrder=true}) and the LIMIT
     * boundary is unambiguous. FAULT self-proof (ships OFF): flip armB's NULLS placement on the lead c2 key
     * (LAST→FIRST) ⇒ the whole ~65-85% NULL block migrates from the tail into the top-k ⇒ the first-k rows diverge
     * massively ⇒ must throw. armB ≡ armA when OFF.
     */
    private void checkCompositeNullsOrderRewrite() throws Exception {
        PostgresTable table = pickGinTable("c2");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c2col = table.getColumns().stream()
                .filter(c -> "c2".equals(c.getName())).findFirst().orElse(null);
        if (c2col == null) return;
        String wrapped = nonSargableWrapFor(c2col, "c2");
        if (wrapped == null) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_mixnulls";
        long k = globalState.getRandomly().getInteger(5, 50);
        String nullsB = FAULT ? "NULLS FIRST" : "NULLS LAST"; // FAULT flips the lead c2 placement ⇒ NULLs invade top-k
        String armA = "SELECT c2, c0, c1, c5, cb FROM " + tbl + " ORDER BY c2 DESC NULLS LAST, c0 DESC, cb ASC LIMIT " + k;
        String armB = "SELECT c2, c0, c1, c5, cb FROM " + tbl + " ORDER BY " + wrapped + " DESC " + nullsB
                + ", c0 DESC, cb ASC LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: the seed builds idx_<t>_mixnulls, but the name-unguarded drop path may have removed it.
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (c2 DESC NULLS LAST, c0 DESC, cb ASC);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must take the combined order from mixnulls (no Sort); armB's wrapped lead key forces a Sort.
            if (!(planA.contains(idxName) && !hasSortNode(planA))) return;
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_MIXNULLS", true);
    }

    /** Pick the RANGE-partitioned {@code idx_pt} parent if ITEM-B seeding ran — the sole target of the
     *  partition-pruning + local-index differential (case 33). Returns null otherwise. */
    private PostgresTable pickPartitionedTable() {
        for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
            if ("idx_pt".equals(t.getName())) return t;
        }
        return null;
    }

    /** Pick a LIST- or HASH-partitioned sibling table (idx_ptl / idx_pth) for case 61, or null if neither
     *  exists yet (their seed setup is best-effort). When both exist, choose one at random. */
    private PostgresTable pickListOrHashPartTable() {
        List<PostgresTable> hits = new ArrayList<>();
        for (PostgresTable t : globalState.getSchema().getDatabaseTables()) {
            if ("idx_ptl".equals(t.getName()) || "idx_pth".equals(t.getName())) hits.add(t);
        }
        return hits.isEmpty() ? null : Randomly.fromList(hits);
    }

    /**
     * ITEM B (case 33). PARTITION PRUNING + PROPAGATED (LOCAL) INDEX, unified across RANGE ({@code idx_pt}),
     * LIST ({@code idx_ptl}) and HASH ({@code idx_pth}) strategies (formerly also case 61). Each partitioned
     * table carries a propagated index on the NON-partition-key column {@code c0} (PG materializes a matching
     * per-partition child index). A strategy-specific pk-prune predicate (RANGE: a {@code pk} range matching
     * one child's bounds, or none = scan all children; LIST: {@code pk IN (1,2,3)} → one child; HASH:
     * {@code pk = V} → static hash-modulus pruning to one child) is NEVER wrapped and is byte-identical in both
     * arms, so BOTH arms prune to the exact same child set. armA {@code [pk-prune] AND c0 = V} rides a
     * per-partition c0 Index(-Only/Bitmap) Scan after pruning; armB wraps ONLY the c0 key {@code least(c0,c0) =
     * V} (not index-matchable) → a per-partition Seq Scan. Within the pruned child set {@code least(c0,c0) ≡ c0}
     * for every row incl. NULL ⇒ the row sets are provably equal ⇒ any mismatch is a real partition-/local-
     * index bug. No ORDER BY ⇒ SET → compareValueIdentityStrict (multiset). The gate confirms pruning really
     * happened (a pruned-out RANGE child must be absent; LIST/HASH: strictly fewer than the full child set
     * present). FAULT shifts armB to {@code least(c0,c0) + 1 = V} → a different row set → must throw.
     */
    private void checkPartitionPruneRewrite() throws Exception {
        // Choose a partition strategy whose table exists: RANGE (idx_pt) or LIST/HASH (idx_ptl/idx_pth).
        List<PostgresTable> cands = new ArrayList<>();
        PostgresTable rangeT = pickPartitionedTable();
        if (rangeT != null) cands.add(rangeT);
        PostgresTable lhT = pickListOrHashPartTable();
        if (lhT != null) cands.add(lhT);
        if (cands.isEmpty()) return;
        PostgresTable table = Randomly.fromList(cands);
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("c0".equals(c.getName())) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String v = generateDataAwareValueForType(tbl, c0col);
        if (v == null || "NULL".equalsIgnoreCase(v)) return;
        String keyB = FAULT ? wrap + " + 1" : wrap;

        // Strategy-specific pk-prune predicate (always ends in a trailing " AND " when present, or "" = scan
        // all), the local c0 index name, and the prune-verification child set. The pk predicate is NEVER
        // wrapped, so pruning is identical across both arms ⇒ the differential stays sound regardless.
        String pkPred;
        String localIdx;
        String[] prunedOutChildren = null; // RANGE prune mode: these children MUST be absent in armA's plan
        String[] allChildren = null;       // LIST/HASH: full child set; prune ⇒ strictly fewer present
        if ("idx_pt".equals(tbl)) {
            localIdx = "idx_pt_c0";
            // "prune" → pk range matches ONLY p1's bounds; "all" → no pk predicate → Append over every child.
            String mode = Randomly.fromOptions("prune", "prune", "all");
            if ("prune".equals(mode)) {
                pkPred = "pk >= 0 AND pk < 1000000 AND ";
                prunedOutChildren = new String[] { "idx_pt_p0", "idx_pt_p2" };
            } else {
                pkPred = "";
            }
        } else if ("idx_ptl".equals(tbl)) {
            localIdx = "idx_ptl_c0";
            pkPred = "pk IN (1, 2, 3) AND ";
            allChildren = new String[] { "idx_ptl_p0", "idx_ptl_p1", "idx_ptl_p2", "idx_ptl_pdef" };
        } else { // idx_pth — HASH: sample an ACTUAL pk so the pruned-to child holds rows (c0=V can then match)
            localIdx = "idx_pth_c0";
            long pv;
            try {
                List<String> pr = executeQuery(
                        "SELECT pk FROM " + tbl + " WHERE pk IS NOT NULL ORDER BY random() LIMIT 1");
                if (pr == null || pr.isEmpty() || pr.get(0) == null || pr.get(0).trim().isEmpty()) return;
                pv = Long.parseLong(pr.get(0).trim());
            } catch (Exception e) {
                return;
            }
            pkPred = "pk = " + pv + " AND ";
            allChildren = new String[] { "idx_pth_p0", "idx_pth_p1", "idx_pth_p2", "idx_pth_p3" };
        }

        String armA = "SELECT * FROM " + tbl + " WHERE " + pkPred + "c0 = " + v;
        String armB = "SELECT * FROM " + tbl + " WHERE " + pkPred + keyB + " = " + v;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + localIdx + " ON "
                    + tbl + " (c0);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride a (per-partition) c0 index; armB must be an index-free (seq) scan.
            if (!(planA.contains("Index Cond")
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan")
                        || planA.contains("Bitmap Index Scan")))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            // VERIFY pruning actually happened (sound either way, but keep the shape honestly labeled).
            if (prunedOutChildren != null) {
                for (String ch : prunedOutChildren) {
                    if (planA.contains(ch)) return; // a pruned-out child survived → not the prune path → skip
                }
            } else if (allChildren != null) {
                int present = 0;
                for (String ch : allChildren) {
                    if (planA.contains(ch)) present++;
                }
                if (present < 1 || present >= allChildren.length) return;
            }
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_PARTPRUNE");
    }

    /**
     * G1 (case 55) — MEMOIZE inner-index-probe caching (PG14+). A self-join on ONE idx_t table (so even a
     * single-table DB qualifies): the outer {@code o} is pinned to a deterministic {@code cb} top-k and
     * presents the heavily-duplicated, low-cardinality {@code c4} as the probe value; the inner {@code i}
     * probes the indexed {@code i.c0} (idx_&lt;n&gt;_c0) via {@code i.c0 = o.c4}. The repeated probe keys let
     * the planner cap the inner index scan with a Memoize node under a Nested Loop. armB wraps ONLY the inner
     * join key — {@code least(i.c0,i.c0) = o.c4} — which no index on c0 can serve, so the inner falls to a Seq
     * Scan and Memoize disappears (the planner switches to a hash join). The outer pin ({@code o.cb IN (SELECT
     * cb FROM tbl ORDER BY cb LIMIT k)}) is byte-identical in both arms and the wrapper is an exact
     * value-identity incl. NULL (a NULL c0 never equals anything in either arm), so the joined
     * {@code (i.cb, i.c0)} multiset is provably equal ⇒ any mismatch is a real Memoize/index bug. No ORDER BY
     * ⇒ multiset compare (compareValueIdentityStrict). Numeric join key only (collation-free, and the +1 FAULT
     * shift needs arithmetic). Sparse-but-sound: Memoize is cost-chosen (enable_memoize is default-on,
     * un-forceable without a banned GUC), so rounds where it isn't picked self-skip at the gate. FAULT
     * self-proof: shift the inner probe by +1 ({@code least(i.c0,i.c0) + 1 = o.c4}) so the matched multiset
     * diverges while the wrapped key keeps armB a Seq Scan (the armB gate still accepts).
     */
    private void checkMemoizeRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("c0".equals(c.getName())) { c0col = c; break; }
        }
        if (c0col == null) return;
        String baseWrap = nonSargableWrapFor(c0col, "i.c0");
        if (baseWrap == null) return;
        // FAULT: +1 numeric shift on the inner probe (least(c0,c0)+1 = o.c4 ⇒ matches i.c0 = o.c4-1), so the
        // joined multiset diverges while armB stays a non-index Filter; ships OFF ⇒ byte-identity wrap.
        String innerKeyB = FAULT ? baseWrap + " + 1" : baseWrap;
        // A plain equi-join self-join on 12000 rows is always a Hash Join (hashing the whole inner is cheap) —
        // Memoize is never cost-chosen. A correlated LATERAL + LIMIT cannot be hashed, so it forces a
        // parameterized Nested Loop; when the outer presents MANY rows with FEW distinct cache keys the planner
        // caps the inner index probe with a Memoize node. c4 is seeded dense (~70% in [-8,8], skewSmallMagnitude)
        // so the band predicate yields ~8500 outer rows over ~17 distinct c4 values — exactly the shape Memoize
        // wins on. The inner probes OUR always-present idx_<n>_c0 via a sargable Index Cond (c0 = o.c4). This is
        // the Memoize-node variant of the LATERAL shape (case 51 pins a SMALL outer, never memoizes); here the
        // differential is a cached sargable index SEARCH (armA) vs a non-sargable full-scan Filter (armB).
        long m = globalState.getRandomly().getInteger(2, 5); // LIMIT; ORDER BY i.cb (unique) ⇒ no tie-truncation
        String corrA = "i.c0 = o.c4";
        String corrB = innerKeyB + " = o.c4";
        String armA = "SELECT o.cb, i.cb, i.c0 FROM " + tbl + " o JOIN LATERAL (SELECT i.cb, i.c0 FROM " + tbl
                + " i WHERE " + corrA + " ORDER BY i.cb LIMIT " + m + ") i ON true WHERE o.c4 BETWEEN -8 AND 8";
        String armB = "SELECT o.cb, i.cb, i.c0 FROM " + tbl + " o JOIN LATERAL (SELECT i.cb, i.c0 FROM " + tbl
                + " i WHERE " + corrB + " ORDER BY i.cb LIMIT " + m + ") i ON true WHERE o.c4 BETWEEN -8 AND 8";
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA gate: a Memoize cache keyed on the outer join value feeding a sargable c0 index SEARCH. The
            // Index Cond text pins the SEARCH (not a Filter) regardless of which c0 index the planner picks.
            boolean armARidesMemoize = planA.contains("Memoize") && planA.contains("Cache Key: o.c4")
                    && planA.contains("Index Cond: (c0 = o.c4)");
            if (!armARidesMemoize) return;
            // armB positive non-index gate: the wrap collapses the sargable probe to a Filter, so the specific
            // c0 Index Cond MUST be gone (the inner now full-scans + filters). Reject rounds where it survives.
            if (planB.contains("Index Cond: (c0 = o.c4)")) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_MEMOIZE");
    }

    /**
     * DISTINCT ON index-ordered first-row-per-group. armA rides the composite (c0,c1) btree so the
     * {@code DISTINCT ON (c0) ... ORDER BY c0, c1} needs NO Sort — the Unique node walks the index-ordered
     * stream and emits the min-c1 row per c0 group. armB wraps c0 in BOTH the DISTINCT ON key and the leading
     * ORDER BY ({@code least(c0,c0)}): the wrap is non-sargable so the index can no longer supply the order and
     * the planner must insert a Sort. The Sort node is itself the positive non-index confirmation — the index
     * is still SCANNED (Index Only Scan feeds the Sort), so we deliberately do NOT pin {@code !idxname} here
     * (that would be unsound for a Sort-based shape). Projecting only the ordered keys (c0,c1) makes the result
     * immune to intra-(c0,c1) tie truncation. Output is one row per distinct c0, ordered by c0 ⇒ a total order.
     * FAULT flips the c1 tiebreak to DESC in armB only ⇒ keeps the MAX-c1 row per group ⇒ c1 diverges on every
     * c0 group that has >1 row.
     */
    private void checkDistinctOnRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("c0".equals(c.getName())) { c0col = c; break; }
        }
        if (c0col == null) return;
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        String idxc0c1 = "idx_" + tbl.substring("idx_t".length()) + "_c0c1";
        String tieB = FAULT ? "DESC" : "ASC"; // FAULT: flip the per-group tiebreak so the kept row changes
        String armA = "SELECT DISTINCT ON (c0) c0, c1 FROM " + tbl + " ORDER BY c0 ASC, c1 ASC";
        String armB = "SELECT DISTINCT ON (" + wrap + ") c0, c1 FROM " + tbl
                + " ORDER BY " + wrap + " ASC, c1 " + tieB;
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: the (c0,c1) index supplies the DISTINCT-ON order with NO Sort.
            if (!planA.contains(idxc0c1) || hasSortNode(planA)) return;
            // armB positive non-index gate: the wrapped DISTINCT-ON/ORDER-BY key cannot ride the index, so a
            // Sort MUST appear. (The index may still be scanned to FEED the Sort — that is expected and sound.)
            if (!hasSortNode(planB)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_DISTINCTON", true);
    }

    /**
     * Set-operation (UNION / INTERSECT / EXCEPT) whose two scan inputs each ride a c0-family index. armA runs
     * two selective {@code c0 BETWEEN} range sub-selects — each served by an Index (Only) Scan on a c0 index —
     * and combines them with a random set operator. armB wraps the {@code c0} range key in both WHEREs with the
     * proven identity {@code least(c0,c0)}: non-sargable, so both inputs fall to Seq Scan and no c0 index is used.
     * The projected columns (c0, c1) are byte-identical between the arms (only the range KEY is wrapped), and
     * every set operator de-duplicates / is order-undefined, so the two arms must produce the same SET. We pin the
     * c0-family index substring on armA and require its total absence + a Seq Scan on armB — a strong positive
     * non-index confirmation. FAULT NOT-wraps the first side's predicate in armB only ({@code NOT(least(c0,c0)
     * BETWEEN a AND b)}): that side's row set flips to its complement, so the set-op output diverges while armB
     * stays Seq Scan.
     */
    private void checkSetOpInputRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("c0".equals(c.getName())) { c0col = c; break; }
        }
        if (c0col == null) return;
        List<String> sampled = sampleColumnValues(tbl, "c0", 4);
        if (sampled == null || sampled.size() < 2) return;
        long v1;
        long v2;
        try {
            v1 = Long.parseLong(sampled.get(0).trim());
            v2 = Long.parseLong(sampled.get(1).trim());
        } catch (Exception e) {
            return;
        }
        String wrap = nonSargableWrapFor(c0col, "c0");
        if (wrap == null) return;
        long span = globalState.getRandomly().getInteger(1, 60);
        long a1 = v1;
        long b1 = v1 + span;
        long a2 = v2;
        long b2 = v2 + span;
        String[] ops = { "INTERSECT", "EXCEPT", "UNION" };
        String op = ops[(int) globalState.getRandomly().getInteger(0, ops.length)];
        String idxc0 = "idx_" + tbl.substring("idx_t".length()) + "_c0"; // matches the whole c0 index family
        String pred1A = "c0 BETWEEN " + a1 + " AND " + b1;
        String pred2A = "c0 BETWEEN " + a2 + " AND " + b2;
        String pred1B = wrap + " BETWEEN " + a1 + " AND " + b1;
        String pred2B = wrap + " BETWEEN " + a2 + " AND " + b2;
        if (FAULT) {
            pred1B = "NOT(" + pred1B + ")"; // perturb side 1's set so the set-op result diverges
        }
        String armA = "(SELECT c0, c1 FROM " + tbl + " WHERE " + pred1A + ") " + op
                + " (SELECT c0, c1 FROM " + tbl + " WHERE " + pred2A + ")";
        String armB = "(SELECT c0, c1 FROM " + tbl + " WHERE " + pred1B + ") " + op
                + " (SELECT c0, c1 FROM " + tbl + " WHERE " + pred2B + ")";
        List<String> rA;
        List<String> rB;
        try {
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            boolean armAIndex = planA.contains(idxc0)
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"));
            if (!armAIndex) return;
            if (!planB.contains("Seq Scan") || planB.contains(idxc0)) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsSorted(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_SETOP");
    }

    /**
     * NULLS NOT DISTINCT unique index (PG15+). Create-on-demand (like case 13) a UNIQUE index on {@code cb}
     * (IDENTITY ⇒ always distinct ⇒ the build never errors) with the PG15+ {@code NULLS NOT DISTINCT} clause, in
     * a {@code try{…}finally{dropOwnIndexQuietly}} so we only ever drop the index WE created. armA rides this
     * index for an ordered unique-leaf top-k ({@code cb >= v ORDER BY cb LIMIT k}); {@code cb} is UNIQUE NOT NULL
     * ⇒ a TOTAL order ⇒ the LIMIT is deterministic. {@code FROM ONLY} restricts to the parent's own rows (the
     * NULLS-NOT-DISTINCT index is parent-local; a bare scan over an inheritance hierarchy would see colliding
     * per-child IDENTITY cb values → boundary ties → a false mismatch under the differential — same hazard case 13
     * seals). armB wraps the {@code cb} key in BOTH the WHERE and the ORDER BY with {@code least(cb,cb)}: non-
     * sargable ⇒ Seq Scan + Sort, no index. Projecting (cb, c0) is byte-identical between arms (only the key is
     * wrapped). FAULT NOT-wraps armB's predicate ({@code NOT(least(cb,cb) >= v)}) → the complement's first-k rows
     * → diverges, while armB stays Seq Scan.
     *
     * Documented limitation: this exercises the PG15+ NULLS-NOT-DISTINCT index BUILD + SCAN path, but NOT the
     * NULL-equality data path ({@code cb} has no NULLs; a NULL-bearing unique column is infeasible under random
     * concurrent 12000-row seeding). Sound; narrow. Deeper NULL-data coverage is a seed-redesign follow-up.
     */
    private void checkNullsNotDistinctRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        if (table.isPartitioned()) return; // a UNIQUE index on a partitioned table must include the partition key
        String tbl = table.getName();
        PostgresColumn cbcol = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("cb".equals(c.getName())) { cbcol = c; break; }
        }
        if (cbcol == null) return;
        String wrap = nonSargableWrapFor(cbcol, "cb");
        if (wrap == null) return;
        List<String> sampled = sampleColumnValues(tbl, "cb", 5);
        if (sampled == null || sampled.isEmpty()) return;
        String v = sampled.get((int) Randomly.getNotCachedInteger(0, sampled.size())).trim();
        if (v.isEmpty()) return;
        int k = (int) Randomly.getNotCachedInteger(2, 12);
        String rel;
        String primB;
        if (Randomly.getBoolean()) {
            rel = "cb >= " + v;
            primB = wrap + " >= " + v;
        } else {
            rel = "cb <= " + v;
            primB = wrap + " <= " + v;
        }
        String idxName = "nsnnd_" + tbl + "_cb";
        String armA = "SELECT cb, c0 FROM ONLY " + tbl + " WHERE " + rel + " ORDER BY cb LIMIT " + k;
        String armB = "SELECT cb, c0 FROM ONLY " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB)
                + " ORDER BY " + wrap + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            ExpectedErrors uniqErrors = new ExpectedErrors();
            uniqErrors.add("could not create unique index");
            uniqErrors.add("unsupported UNIQUE constraint with partition key definition");
            uniqErrors.add("duplicate key value");
            uniqErrors.add("relation .* does not exist");
            uniqErrors.add("canceling statement due to statement timeout");
            uniqErrors.add("canceling statement due to user request");
            globalState.executeStatement(new SQLQueryAdapter("CREATE UNIQUE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " (cb) NULLS NOT DISTINCT;", uniqErrors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Index Cond"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        } finally {
            dropOwnIndexQuietly(idxName);
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_NND");
    }

    /**
     * Multicolumn GIN over BOTH container columns {@code gin(ga, gj)} (case 59). A single multi-key GIN index
     * can serve a conjunction of containment predicates in one Bitmap Index Scan (the two per-column entry
     * sets are ANDed inside the index), a code path the two single-key GINs ({@code gagin}/{@code gjgin})
     * never exercise — the two-column GIN build (one posting tree per column, interleaved keys) and the
     * ANDed-within-the-index scan are both distinct from any single-key GIN. armA rides the seeded
     * {@code idx_<n>_mcgin} via {@code ga @> ARRAY[n] AND gj @> '{"k":m}'} (gated on that index name + a
     * Bitmap Index Scan). armB wraps BOTH container columns in their exact value-identity ({@code least(ga,ga)}
     * / {@code least(gj,gj)} — identity on a total order; a NULL container yields SQL NULL on both operands →
     * 3VL-false in BOTH arms), which the planner cannot match to the GIN → a pure heap Seq Scan
     * (index-independent ground truth). Row sets provably equal → any mismatch is a real multicol-GIN bug.
     * n,m ∈ [0,99] match the DEFAULT key space (selective). FAULT: {@code NOT}-wrap the primary (array)
     * containment on armB → its matched set diverges while armB stays a Seq Scan.
     */
    private void checkMultiColGinRewrite() throws Exception {
        PostgresTable table = pickGinTable("ga");
        if (table == null) return;
        String tbl = table.getName();
        // require the companion jsonb column too (same seed table carries both)
        boolean hasGj = false;
        for (PostgresColumn c : table.getColumns()) {
            if ("gj".equals(c.getName())) { hasGj = true; break; }
        }
        if (!hasGj) return;
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_mcgin";
        long n = Randomly.getNotCachedInteger(0, 100);
        long m = Randomly.getNotCachedInteger(0, 100);
        String contA = "ga @> ARRAY[" + n + "]";
        String contB = "gj @> '{\"k\":" + m + "}'";
        String wrapA = "least(ga, ga) @> ARRAY[" + n + "]";
        String wrapB = "least(gj, gj) @> '{\"k\":" + m + "}'";
        if (FAULT) {
            wrapA = "NOT(" + wrapA + ")";
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + contA + " AND " + contB;
        String armB = "SELECT * FROM " + tbl + " WHERE " + wrapA + " AND " + wrapB;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin(ga, gj);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_MCGIN");
    }

    /**
     * BRIN minmax_multi-opclass equality / range (case 60). Distinct from both {@link #checkBrinRewrite}
     * (plain {@code minmax} on the correlated cb) and {@link #checkBrinBloomRewrite} ({@code bloom}, equality
     * only): the {@code int4_minmax_multi_ops} opclass (built-in PG 14+) keeps up to 32 sub-ranges per block
     * range instead of a single [min,max], so it prunes an UNCORRELATED column where plain minmax degenerates
     * to the full span. Targets the dedicated {@code cm} column, whose SOLE index is the prebuilt
     * {@code idx_<n>_cmm} — cm has NO btree and NO other BRIN, so `cm = v` / `cm BETWEEN a AND b` has nothing
     * else to ride and the planner MUST choose the minmax_multi BRIN (a Bitmap Index Scan). cm is uncorrelated,
     * moderate-cardinality (~4000 distinct → ~3 rows/value). {@code v} is sampled from an actual heap cm so
     * armA reliably matches ≥1 row (gate + FAULT fire). armB wraps cm in the exact value-identity
     * {@code least/greatest(cm,cm)} (cm is NOT NULL via DEFAULT) → a pure heap Seq Scan. Row sets provably
     * equal → any mismatch is a real BRIN-minmax_multi bug. FAULT: {@code NOT}-wrap armB's predicate so its row
     * set diverges while the wrapped LHS keeps armB a Seq Scan.
     */
    private void checkBrinMinmaxMultiRewrite() throws Exception {
        PostgresTable table = pickGinTable("cm");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn col = null;
        for (PostgresColumn c : table.getColumns()) {
            if ("cm".equals(c.getName())) { col = c; break; }
        }
        if (col == null) return;
        String colName = "cm";
        String idxName = "idx_" + tbl.substring("idx_t".length()) + "_cmm";
        String wrapped = nonSargableWrapFor(col, colName);
        if (wrapped == null) return;
        // Sample up to 4 ACTUAL cm values so armA matches ≥1 row (gate passes, FAULT NOT-wrap set genuinely differs).
        java.util.List<Long> vs = new java.util.ArrayList<>();
        try {
            List<String> vr = executeQuery(
                    "SELECT cm FROM " + tbl + " WHERE cm IS NOT NULL ORDER BY random() LIMIT 4");
            if (vr != null) {
                for (String s : vr) {
                    if (s != null && !s.trim().isEmpty()) {
                        vs.add(Long.parseLong(s.trim()));
                    }
                }
            }
        } catch (Exception e) {
            return;
        }
        if (vs.isEmpty()) {
            vs.add(Randomly.getNotCachedInteger(0, 3999));
        }
        // Variant selector: single equality, IN-list, or BETWEEN range. minmax_multi serves equality AND range
        // (unlike bloom, which is equality-only); the range path is the headline minmax_multi strength. armB wraps
        // the key in every term (least(cm,cm)≡cm) → not index-matchable → Seq Scan. All variants value-identity-sound.
        int variant = (vs.size() >= 2) ? Randomly.fromOptions(0, 1, 2) : Randomly.fromOptions(0, 2);
        String predA;
        String primB;
        if (variant == 1) { // IN-list
            StringBuilder inList = new StringBuilder();
            for (int i = 0; i < vs.size(); i++) {
                if (i > 0) inList.append(", ");
                inList.append(vs.get(i));
            }
            predA = colName + " IN (" + inList + ")";
            primB = wrapped + " IN (" + inList + ")";
        } else if (variant == 2) { // BETWEEN range (minmax_multi's distinguishing strength)
            long v = vs.get(0);
            long span = Randomly.getNotCachedInteger(1, 300);
            predA = colName + " BETWEEN " + v + " AND " + (v + span);
            primB = wrapped + " BETWEEN " + v + " AND " + (v + span);
        } else { // single equality
            predA = colName + " = " + vs.get(0);
            primB = wrapped + " = " + vs.get(0);
        }
        String armA = "SELECT * FROM " + tbl + " WHERE " + predA;
        String armB = "SELECT * FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        List<String> rA;
        List<String> rB;
        try {
            // Self-heal: a prior shape in this DB may have dropped this prebuilt index; IF NOT EXISTS re-creates it.
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING brin(" + colName + " int4_minmax_multi_ops) WITH (pages_per_range=1);",
                    errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_BRINMM");
    }

    /**
     * COUNT index-only aggregate axis (case 63 / B3). Exercises an index path with zero prior coverage: a bare
     * {@code count(*)} answered from a c0 btree range as an Index Only Scan (the row count is served from the index
     * tuples, no per-row heap fetch). armA counts rows in a {@code c0 BETWEEN lo AND hi} window riding a c0 btree
     * Index (Only) Scan; armB wraps ONLY the key in the exact value-identity {@code least(c0,c0) ≡ c0}, which the
     * planner cannot match → an Aggregate over a Seq Scan (index-independent ground truth). The two bounds are
     * sampled from ACTUAL c0 values and ordered via Math.min/max so the window is non-empty (armA counts ≥1 ⇒ the
     * gate and the FAULT self-proof both fire). count(*) is mathematically identical in both arms for every row ⇒
     * any post-gate count divergence is a real index/aggregate bug. FAULT self-proof: NOT-wrap armB's range so it
     * counts the strict complement → a different count → MUST throw. SET → {@link #compareValueIdentityStrict}.
     * Ships with FAULT OFF ⇒ armB ≡ armA.
     */
    private void checkCountIndexOnlyRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = table.getColumns().stream()
                .filter(c -> "c0".equals(c.getName())).findFirst().orElse(null);
        if (c0col == null) return;
        // Sample two ACTUAL c0 values so the range covers real rows (armA count ≥1 → gate + FAULT fire). Order the
        // bounds so lo ≤ hi regardless of which sample is larger. Skip cleanly if too few non-NULL c0 rows / c0 is
        // not integer-ish here (picked table where c0 is a non-numeric type).
        long a;
        long b;
        try {
            List<String> vr = executeQuery(
                    "SELECT c0 FROM " + tbl + " WHERE c0 IS NOT NULL ORDER BY random() LIMIT 2");
            if (vr != null && vr.size() >= 2 && vr.get(0) != null && vr.get(1) != null
                    && !vr.get(0).trim().isEmpty() && !vr.get(1).trim().isEmpty()) {
                a = Long.parseLong(vr.get(0).trim());
                b = Long.parseLong(vr.get(1).trim());
            } else {
                return;
            }
        } catch (Exception e) {
            return;
        }
        long lo = Math.min(a, b);
        long hi = Math.max(a, b);
        String primB = "least(c0, c0) BETWEEN " + lo + " AND " + hi;
        String armA = "SELECT count(*) FROM " + tbl + " WHERE c0 BETWEEN " + lo + " AND " + hi;
        String armB = "SELECT count(*) FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB);
        List<String> rA;
        List<String> rB;
        try {
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride a c0 btree range as an Index Cond (Index Only Scan / Index Scan on c0); require the
            // Index Cond LINE to reference c0 specifically (c0..c7/cb are mutually non-substring → unambiguous).
            // armB's least(c0,c0) is unmatchable → Aggregate over a Seq Scan, no index node.
            boolean armARidesC0 = false;
            for (String pl : planA.split("\n")) {
                if (pl.contains("Index Cond") && pl.contains("c0")) { armARidesC0 = true; break; }
            }
            if (!armARidesC0) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_COUNTIO");
    }

    /**
     * EXPRESSION-INDEX ORDERED-SCAN axis (case 62 / A2). The functional index {@code idx_<t>_expr ON (ABS(c0))} is
     * exercised for the FIRST time as an ORDER-PROVIDING scan (case 41 only uses it as an equality/range Index
     * Cond). armA takes its order straight from the ordered expression index — {@code ORDER BY abs(c0) ASC LIMIT k}
     * becomes an Index (Only) Scan + Limit with NO Sort node; armB wraps ONLY the ORDER BY key in the exact
     * value-identity {@code abs(least(c0,c0)) ≡ abs(c0)}, which cannot be matched to the ABS(c0) index expression →
     * an explicit Sort (index-independent ground truth). CRUCIAL tie-safety: the SELECT list projects EXACTLY the
     * ordered key {@code abs(c0)}, so rows that tie on the sort key are byte-identical in the output — any tie
     * reorder between the index scan and the Sort yields an identical row list, so strict positional comparison
     * ({@code totalOrder=true}) is sound and raises zero false positives. FAULT self-proof: flip armB's sort
     * direction to DESC so it returns the top-k LARGEST abs values instead of the smallest → the ordered row lists
     * genuinely differ → MUST throw (a {@code +N} offset would not reorder; a direction flip is the proven
     * ORDER-shape perturbation). Ships with FAULT OFF ⇒ armB ≡ armA.
     */
    private void checkExprOrderByRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = table.getColumns().stream()
                .filter(c -> "c0".equals(c.getName())).findFirst().orElse(null);
        if (c0col == null) return;
        // Confirm c0 is integer-ish here (ABS applies) by sampling one abs(c0); skip cleanly otherwise (e.g. a
        // picked table where c0 is a non-numeric type → the ABS(c0) expression index would not exist / apply).
        try {
            List<String> vr = executeQuery(
                    "SELECT abs(c0) FROM " + tbl + " WHERE c0 IS NOT NULL ORDER BY random() LIMIT 1");
            if (vr == null || vr.isEmpty() || vr.get(0) == null || vr.get(0).trim().isEmpty()) return;
            Long.parseLong(vr.get(0).trim());
        } catch (Exception e) {
            return;
        }
        long k = globalState.getRandomly().getInteger(1, 50);
        // armB wraps ONLY the ORDER BY key; SELECT list is byte-identical to armA (projects the sort key abs(c0)).
        // FAULT flips armB's direction (ASC→DESC) so the top-k set genuinely differs; a value-identity wrapper
        // alone would keep armB ≡ armA.
        String dirB = FAULT ? "DESC" : "ASC";
        String armA = "SELECT abs(c0) FROM " + tbl + " ORDER BY abs(c0) ASC LIMIT " + k;
        String armB = "SELECT abs(c0) FROM " + tbl + " ORDER BY abs(least(c0, c0)) " + dirB + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: order supplied by the expression index (Index/Index Only Scan using idx_<t>_expr), no Sort.
            if (!(planA.contains("_expr")
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"))
                    && !hasSortNode(planA))) return;
            // armB: the wrapped key is unmatchable → an explicit Sort NODE, and the expression index is not used.
            if (!(hasSortNode(planB) && !planB.contains("_expr"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_EXPRORDER", true);
    }

    /**
     * DML SCAN-PATH axis (case 64 / A1). The genuinely-new surface is the index scan that feeds a {@code
     * ModifyTable} node — every other shape probes a read-only SELECT, so the index→Delete path had ZERO coverage.
     * armA deletes a selective {@code c0 BETWEEN lo AND hi} window riding a c0 btree Index Scan under a Delete node;
     * armB wraps ONLY the key in the exact value-identity {@code least(c0,c0) ≡ c0}, which the planner cannot match
     * → a Delete over a Seq Scan (index-independent ground truth). Both arms RETURNING the stable unique key {@code
     * cb}; the deleted-row multisets are provably equal for every row ⇒ any post-gate divergence is a real index /
     * ModifyTable bug.
     *
     * FP-SAFETY (critical): the shape would permanently mutate the per-thread database, so BOTH arms run inside a
     * transaction that is ALWAYS rolled back. On the raw per-thread JDBC connection (single-threaded, private DB,
     * no concurrent writer — same precondition the VACUUM blocks rely on) autocommit is forced OFF; armA executes
     * and is immediately rolled back, restoring the EXACT pre-DELETE snapshot; armB then executes against that
     * identical snapshot and is rolled back too. A {@code finally} rolls back unconditionally and restores the
     * prior autocommit mode, so a thrown/aborted arm can never leave a wedged transaction or lose a row. Because no
     * COMMIT ever runs and the two arms observe byte-identical table state, a surviving row-set difference is a
     * real bug, not a write-ordering artifact. The EXPLAIN gate runs BEFORE the autocommit flip and is free
     * (EXPLAIN without ANALYZE does not execute the DELETE).
     *
     * FAULT self-proof: NOT-wrap armB's range so it deletes (and RETURNS) the strict complement set → the RETURNING
     * cb multisets diverge → MUST throw. (armB stays a Seq Scan, still rolled back.) Ships with FAULT OFF ⇒ armB ≡
     * armA. SET → {@link #compareValueIdentityStrict}.
     */
    private void checkDeleteScanRewrite() throws Exception {
        PostgresTable table = pickGinTable("c0");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c0col = table.getColumns().stream()
                .filter(c -> "c0".equals(c.getName())).findFirst().orElse(null);
        if (c0col == null) return;
        // Sample an ACTUAL c0 and probe a NARROW window around it so the DELETE reliably rides a selective Index
        // Scan (a wide/random range goes Seq Scan → ~0 gate yield) and matches ≥1 row (gate + FAULT fire). Skip
        // cleanly if c0 is not integer-ish here or there is no non-NULL c0.
        long v;
        try {
            List<String> vr = executeQuery(
                    "SELECT c0 FROM " + tbl + " WHERE c0 IS NOT NULL ORDER BY random() LIMIT 1");
            if (vr != null && !vr.isEmpty() && vr.get(0) != null && !vr.get(0).trim().isEmpty()) {
                v = Long.parseLong(vr.get(0).trim());
            } else {
                return;
            }
        } catch (Exception e) {
            return;
        }
        long window = globalState.getRandomly().getInteger(0, 500);
        long lo = v - window;
        long hi = v + window;
        String primB = "least(c0, c0) BETWEEN " + lo + " AND " + hi;
        String armA = "DELETE FROM " + tbl + " WHERE c0 BETWEEN " + lo + " AND " + hi + " RETURNING cb";
        String armB = "DELETE FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + primB + ")" : primB) + " RETURNING cb";
        // EXPLAIN gate FIRST, while autocommit is still on (EXPLAIN of a DELETE does not execute it).
        String planA = String.join("\n", getExplainPlan(armA));
        String planB = String.join("\n", getExplainPlan(armB));
        // armA: the Delete is fed by a c0 btree Index Scan (require the Index Cond LINE to reference c0; c0..c7/cb
        // are mutually non-substring → unambiguous). armB: least(c0,c0) unmatchable → Delete over a Seq Scan.
        boolean armARidesC0 = false;
        for (String pl : planA.split("\n")) {
            if (pl.contains("Index Cond") && pl.contains("c0")) { armARidesC0 = true; break; }
        }
        if (!armARidesC0) return;
        if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
        // Run BOTH arms inside an always-rolled-back transaction on the raw per-thread connection.
        java.sql.Connection rawCon;
        try (Statement st = globalState.getConnection().createStatement()) {
            rawCon = st.getConnection();
        } catch (Exception e) {
            return;
        }
        List<String> rA = null;
        List<String> rB = null;
        boolean flipped = false;
        boolean oldAutoCommit = true;
        try {
            oldAutoCommit = rawCon.getAutoCommit();
            rawCon.setAutoCommit(false);
            flipped = true;
            rA = executeQuery(armA);
            rawCon.rollback();           // restore the exact pre-DELETE snapshot
            rB = executeQuery(armB);
            rawCon.rollback();
        } catch (Throwable t) {
            return;                      // expected-error / skip — finally restores state, never a thread kill
        } finally {
            try { rawCon.rollback(); } catch (Throwable ignore) { }
            if (flipped) {
                try { rawCon.setAutoCommit(oldAutoCommit); } catch (Throwable ignore) { }
            }
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_DMLSCAN");
    }

    /**
     * Contrib bloom index AM (case 65, tag {@code PG_NS_BLOOM}). The {@code bloom} extension's signature-based
     * index ({@code USING bloom}) is a lossy, always-recheck, multi-column equality index — a genuinely
     * independent access method (blbuild/blinsert/blgetbitmap) that scans EVERY index tuple applying a
     * per-row signature filter and is reached only via a Bitmap Index Scan + Recheck. It is NOT the built-in
     * BRIN {@code int4_bloom_ops} opclass exercised by case 21 ({@code checkBrinBloomRewrite}); that is a
     * different AM. We build it on {@code (c3, c6)}: the only two base columns with NO standalone equality
     * index — c3 (INT NOT NULL) appears only non-leading inside the composite {@code (c0,c1,c3)} and as an
     * INCLUDE payload of {@code idx_<t>_cover}; c6 (TEXT, nullable) carries no index at all. Every other INT
     * column has a competing leading btree (c0/c1/c2/c4) or a BRIN equality path (cu/cm) that would win the
     * cost race and starve the bloom gate — verified empirically. On {@code (c3, c6)} the planner's only
     * choices are the bloom Bitmap Index Scan or a Seq Scan.
     * <p>Bloom resolves equality through a hashed signature, so c6 text equality is collation-INDEPENDENT —
     * this shape never performs a collation-ordered btree equality-descent on text, so the libc/Windows
     * non-C collation off-by-one hazard (which bars TEXT from the ordering-sensitive differentials) does not
     * apply; equality under the deterministic default collation returns the identical row set in both arms.
     * <p>armA = equality conjunction on {@code (c3, c6)} with both constants drawn from ONE real heap row
     * (both NOT NULL) so armA matches >=1 row and the FAULT complement genuinely differs. armB wraps BOTH
     * keys in the value-identity wrapper — wrapping only one is insufficient because bloom can serve ANY
     * SUBSET of its indexed columns, so a single residual unwrapped key would keep the bloom path alive and
     * the armB Seq-Scan gate would never pass. Every other byte is identical ⇒ armB is a value-identity twin
     * ⇒ 0 FP by construction. Multiset compare over the {@code cb} projection (order-insensitive).
     * <p>FAULT self-proof: NOT-wrap the whole (already non-sargable) predicate ⇒ complement row set ⇒ the two
     * cb multisets must diverge ⇒ a real non-INSERT AssertionError. Still a Seq Scan (armB gate still accepts).
     */
    private void checkBloomRewrite() throws Exception {
        PostgresTable table = pickGinTable("c6");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c3 = null;
        PostgresColumn c6 = null;
        for (PostgresColumn c : table.getColumns()) {
            if (c.getName().equals("c3")) c3 = c;
            else if (c.getName().equals("c6")) c6 = c;
        }
        if (c3 == null || c6 == null) return;
        String w3 = nonSargableWrapFor(c3, "c3");
        String w6 = nonSargableWrapFor(c6, "c6");
        if (w3 == null || w6 == null) return;
        // Draw the two equality constants from a SINGLE real row (both NOT NULL) so armA matches >=1 row and
        // the FAULT complement genuinely differs. Skip cleanly if no such row.
        String v3;
        String v6;
        try {
            List<String> rr = executeQuery("SELECT c3, c6 FROM " + tbl
                    + " WHERE c3 IS NOT NULL AND c6 IS NOT NULL ORDER BY random() LIMIT 1");
            if (rr == null || rr.isEmpty() || rr.get(0) == null) return;
            String[] parts = rr.get(0).split(" \\|\\|\\| ", -1);
            if (parts.length < 2) return;
            String raw3 = parts[0].trim();
            String raw6 = parts[1]; // text: do NOT trim (trailing/leading spaces are part of the value)
            if (raw3.isEmpty()) return;
            v3 = quoteValueForSQL(raw3, c3); // INT → bare numeric literal
            v6 = quoteValueForSQL(raw6, c6); // TEXT → escaped, single-quoted literal
            if (v3 == null || v6 == null) return;
        } catch (Exception e) {
            return;
        }
        String idxName = "nsbloom_" + tbl;
        String predB = w3 + " = " + v3 + " AND " + w6 + " = " + v6;
        String armA = "SELECT cb FROM " + tbl + " WHERE c3 = " + v3 + " AND c6 = " + v6;
        String armB = "SELECT cb FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + predB + ")" : predB);
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(new SQLQueryAdapter("CREATE EXTENSION IF NOT EXISTS bloom;", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING bloom (c3, c6);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA must ride the bloom index as a Bitmap Index Scan (bloom is lossy ⇒ always Bitmap + Recheck,
            // never a plain/ordered Index Scan); armB's two wrapped keys leave no bloom-usable qual ⇒ Seq Scan.
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_BLOOM");
    }

    /**
     * Contrib btree_gist scalar KNN AM (case 66, tag {@code PG_NS_BTGISTKNN}). The {@code btree_gist} extension
     * adds GiST opclasses for scalar types, including a distance operator {@code <->} on {@code int4}
     * (gist_int4_ops), so a plain scalar column can serve a nearest-neighbour ORDER-BY as a distance-ordered
     * {@code Index [Only] Scan} ({@code Order By: (c3 <-> v)}) with NO Sort node. This is a different surface
     * from case 38 ({@code checkKnnOrderRewrite}), which does 2-D {@code point} KNN on the built-in GiST
     * {@code gp}; here the KNN runs over a SCALAR int via the contrib opclass. Built on {@code c3} — the only
     * INT column with no standalone btree (every other INT column has a leading btree that offers a cheaper
     * ordered path and would starve this gate).
     * <p>TIE-SAFETY (critical): KNN distance is symmetric, so two rows at {@code v+d} and {@code v-d} tie on
     * distance but differ in {@code c3} — projecting {@code c3} would make the output order-dependent and
     * manufacture false positives. We therefore project the DISTANCE itself ({@code c3 <-> v}): equidistant
     * rows render an identical value, so any order among a tie group yields byte-identical output ⇒ the strict
     * positional comparator is sound. armB wraps ONLY the key, in BOTH the SELECT distance and the ORDER BY
     * distance ({@code least(c3,c3) ≡ c3} ⇒ identical distances), forcing an explicit Sort over a Seq Scan.
     * <p>FAULT self-proof: flip armB's distance order to {@code DESC} (farthest-k instead of nearest-k) ⇒ the
     * top-k multiset genuinely differs ⇒ a real non-INSERT AssertionError. armB stays a Sort+Seq Scan (gate
     * still accepts). A value-identity wrapper alone would leave armB ≡ armA, so the direction flip is the
     * proven ORDER-shape perturbation (mirrors case 62).
     */
    private void checkBtreeGistKnnRewrite() throws Exception {
        PostgresTable table = pickGinTable("c3");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c3 = table.getColumns().stream()
                .filter(c -> "c3".equals(c.getName())).findFirst().orElse(null);
        if (c3 == null) return;
        String wrap = nonSargableWrapFor(c3, "c3");
        if (wrap == null) return;
        // Anchor from a real c3 value so a nearest set exists; confirm c3 is integer-ish (the <-> opclass applies).
        String v;
        try {
            List<String> vr = executeQuery(
                    "SELECT c3 FROM " + tbl + " WHERE c3 IS NOT NULL ORDER BY random() LIMIT 1");
            if (vr == null || vr.isEmpty() || vr.get(0) == null || vr.get(0).trim().isEmpty()) return;
            v = vr.get(0).trim();
            Long.parseLong(v);
        } catch (Exception e) {
            return;
        }
        long k = globalState.getRandomly().getInteger(1, 50);
        String idxName = "nsbgistknn_" + tbl;
        String distA = "c3 <-> " + v;
        String distB = wrap + " <-> " + v;
        // Project the DISTANCE (tie-safe); armB wraps the key in both the projection and the ORDER BY key.
        String armA = "SELECT (" + distA + ") FROM " + tbl + " ORDER BY " + distA + " ASC LIMIT " + k;
        String armB = "SELECT (" + distB + ") FROM " + tbl + " ORDER BY " + distB + " " + (FAULT ? "DESC" : "ASC")
                + " LIMIT " + k;
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(
                    new SQLQueryAdapter("CREATE EXTENSION IF NOT EXISTS btree_gist;", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gist (c3);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            // armA: distance order supplied by the btree_gist KNN index (Index/Index Only Scan), no Sort.
            if (!(planA.contains(idxName)
                    && (planA.contains("Index Scan") || planA.contains("Index Only Scan"))
                    && !hasSortNode(planA))) return;
            // armB: the wrapped key is unmatchable → an explicit Sort NODE, and the KNN index is not used.
            if (!(hasSortNode(planB) && !planB.contains(idxName))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareResultsOrdered(rA, rB, armA, armB, "PG_NS_BTGISTKNN", true);
    }

    /**
     * Contrib btree_gin scalar equality AM (case 67, tag {@code PG_NS_BTGIN}). The {@code btree_gin} extension
     * adds GIN opclasses for scalar types, so a plain {@code int4} column can be served by a GIN index that
     * resolves equality through posting-list lookup under a {@code Bitmap Index Scan} + Recheck. This is a
     * third, internally-distinct access method from case 65 (bloom signatures) and case 66 (btree_gist tree):
     * GIN entry tree + posting lists / the {@code gin_btree} consistent function. Built on {@code c3} — the
     * only INT column with no standalone btree (see case 65 rationale).
     * <p>armA = {@code c3 = v} (v from a real heap row so >=1 row matches); armB wraps ONLY the key in the
     * value-identity {@code least/greatest/coalesce/CASE(c3) ≡ c3}, unmatchable by the GIN opclass ⇒ a Seq
     * Scan (index-independent ground truth). Every other byte identical ⇒ value-identity twin ⇒ 0 FP.
     * Multiset compare over the {@code cb} projection.
     * <p>NOTE on cross-shape competition: in a full mix the bloom/btree_gist/btree_gin indexes may all exist on
     * one table and compete for {@code c3 = v}; the gate is name-pinned to {@code nsbgin_<t>}, so a shape whose
     * c3 index loses the cost race simply SKIPS (gate fails) — never a false positive.
     * <p>FAULT self-proof: NOT-wrap the predicate ⇒ complement row set ⇒ divergent cb multiset ⇒ a real
     * non-INSERT AssertionError. Still a Seq Scan (armB gate still accepts).
     */
    private void checkBtreeGinRewrite() throws Exception {
        PostgresTable table = pickGinTable("c3");
        if (table == null) return;
        String tbl = table.getName();
        PostgresColumn c3 = table.getColumns().stream()
                .filter(c -> "c3".equals(c.getName())).findFirst().orElse(null);
        if (c3 == null) return;
        String wrap = nonSargableWrapFor(c3, "c3");
        if (wrap == null) return;
        String v;
        try {
            List<String> vr = executeQuery(
                    "SELECT c3 FROM " + tbl + " WHERE c3 IS NOT NULL ORDER BY random() LIMIT 1");
            if (vr == null || vr.isEmpty() || vr.get(0) == null || vr.get(0).trim().isEmpty()) return;
            v = vr.get(0).trim();
            Long.parseLong(v);
        } catch (Exception e) {
            return;
        }
        String idxName = "nsbgin_" + tbl;
        String predB = wrap + " = " + v;
        String armA = "SELECT cb FROM " + tbl + " WHERE c3 = " + v;
        String armB = "SELECT cb FROM " + tbl + " WHERE " + (FAULT ? "NOT (" + predB + ")" : predB);
        List<String> rA;
        List<String> rB;
        try {
            globalState.executeStatement(
                    new SQLQueryAdapter("CREATE EXTENSION IF NOT EXISTS btree_gin;", errors, true));
            globalState.executeStatement(new SQLQueryAdapter("CREATE INDEX IF NOT EXISTS " + idxName
                    + " ON " + tbl + " USING gin (c3);", errors, true));
            analyzeTolerant(tbl);
            String planA = String.join("\n", getExplainPlan(armA));
            String planB = String.join("\n", getExplainPlan(armB));
            if (!(planA.contains(idxName) && planA.contains("Bitmap Index Scan"))) return;
            if (!(planB.contains("Seq Scan") && !planB.contains("Index"))) return;
            rA = executeQuery(armA);
            rB = executeQuery(armB);
        } catch (Exception e) {
            return;
        }
        if (rA == null || rB == null) return;
        log(armA);
        log(armB);
        compareValueIdentityStrict(rA, rB, "A: " + armA + " | B: " + armB, "PG_NS_BTGIN");
    }

    // ==================== P0: EXPLAIN Plan Verification ====================

    /**
     * Get the EXPLAIN plan for a query in PostgreSQL.
     * Uses EXPLAIN (FORMAT TEXT) which returns one plan node per row.
     * Each row contains the node type, relations, and cost info.
     */
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
        if (PLANSIG != null) logPlanSig(queryString, plan);
        return plan;
    }

    /** Ablation-only: append "<ENV|BARE>\t<sorted node-class multiset>" for one plan. Gated by idx.plansig.
     *  Only plan NODE lines (those carrying "(cost=") contribute; qual/detail lines (Filter:/Index Cond:/
     *  Sort Key:) and embedded-newline data fragments are excluded, so the signature is pure node structure. */
    private void logPlanSig(String queryString, List<String> plan) {
        if (plan.isEmpty()) return;
        java.util.TreeMap<String, Integer> m = new java.util.TreeMap<>();
        for (String rawLine : plan) {
            String line = rawLine.replaceAll("[\\r\\n]+", " ");
            int cost = line.indexOf("(cost=");
            if (cost < 0) continue;                            // only real node lines carry a cost estimate
            String s = line.substring(0, cost);
            s = s.replaceAll("^\\s*->\\s*", "").trim();
            s = s.replaceAll("\\s+on\\s+.*$", "").trim();      // drop "on <rel>" (table-agnostic class)
            s = s.replaceAll("\\s+using\\s+.*$", "").trim();   // drop "using <index>"
            if (s.isEmpty()) continue;
            m.merge(s, 1, Integer::sum);
        }
        if (m.isEmpty()) return;
        StringBuilder sig = new StringBuilder();
        for (java.util.Map.Entry<String, Integer> e : m.entrySet()) {
            if (sig.length() > 0) sig.append(",");
            sig.append(e.getKey()).append("*").append(e.getValue());
        }
        String tag = queryString.contains("__env") ? "ENV" : "BARE";
        synchronized (PLANSIG_LOCK) {
            try (java.io.FileWriter fw = new java.io.FileWriter(PLANSIG, true)) {
                fw.write(tag + "\t" + sig + "\n");
            } catch (Exception ignore) {
            }
        }
    }

    /**
     * Check if two PostgreSQL EXPLAIN plans are different.
     * Compares the operator node types by extracting the first non-whitespace
     * token from each plan line (e.g., "Seq Scan", "Index Scan", "Bitmap Heap Scan").
     * Ignores cost/row estimates which can vary between settings.
     */
    private boolean plansAreDifferent(List<String> plan1, List<String> plan2) {
        if (plan1.isEmpty() || plan2.isEmpty()) return true; // Can't verify, assume different
        // Compare extracted node types
        List<String> nodes1 = extractPlanNodes(plan1);
        List<String> nodes2 = extractPlanNodes(plan2);
        if (nodes1.size() != nodes2.size()) return true;
        return !nodes1.equals(nodes2);
    }

    /**
     * Extract plan node types from EXPLAIN output.
     * Each line like "  ->  Seq Scan on t0  (cost=..." becomes "Seq Scan on t0"
     * We strip the arrow prefix and cost info to get just the node type + relation.
     */
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


    // ==================== Mode 16: tsvector GIN Full-Text Search (P0 - PostgreSQL-specific) ====================


    /** Internal query execution that returns null on error (for sampling) */
    private List<String> execInternal(String query) {
        try {
            return ComparatorHelper.getResultSetAllColumnsAsString(query, errors, globalState, " ||| ");
        } catch (Exception e) {
            return null;
        }
    }

    // ==================== Mode 17: Optimizer Config Pairwise ====================


    // ==================== Mode 18: SQL Semantic Equivalence ====================


    // ==================== P0: COUNT(*) Aggregate Fallback ====================

    /**
     * P0: When compareResultsSorted/Strict filters out a difference (e.g., LIMIT without
     * ORDER BY), use COUNT(*) as a deterministic fallback to still detect bugs.
     * COUNT(*) is not affected by row ordering or LIMIT — if the counts differ
     * between two plans, one plan has a genuine bug.
     */

    /**
     * P0: Wrap a query in SELECT COUNT(*) FROM (original_query) to get a deterministic result.
     * Uses subquery wrapping which is safe for any query structure (subqueries, UNION, etc.).
     * The COUNT(*) counts rows returned by the original query (including any LIMIT).
     * This is correct for our purpose: verifying that two plans return the same number of rows.
     */
    private String wrapInCountStar(String query) {
        // Remove trailing semicolon
        String q = query.endsWith(";") ? query.substring(0, query.length() - 1) : query;
        // Safe wrapping: treat the entire original query as a subquery
        return "SELECT COUNT(*) FROM (" + q + ") AS cnt_sub;";
    }

    // ==================== Mode 19: Deterministic Index Query (P4) ====================

    /**
     * Sample actual column values from a table for deterministic WHERE conditions.
     */
    private List<String> sampleColumnValues(String tableName, String colName, int limit) {
        try {
            String query = "SELECT " + colName + " FROM " + tableName
                    + " WHERE " + colName + " IS NOT NULL LIMIT " + limit + ";";
            return execInternal(query);
        } catch (Exception e) {
            return null;
        }
    }

    /**
     * Find a column that has a UNIQUE index (acts as deterministic key for WHERE).
     * In PG, PostgresColumn doesn't have isPrimaryKey(), so we look for unique single-column indexes.
     */
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

    /**
     * Quote a value for SQL, handling type-specific escaping.
     */
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

    /**
     * Build a deterministic query targeting this table's indexes.
     * Uses unique column for WHERE to guarantee data match across plans.
     */
    /**
     * Build a deterministic query using index columns for WHERE.
     * 7 query templates covering diverse index scan patterns:
     *   0: SELECT * with equality/range ORDER BY col LIMIT 50
     *   1: SELECT COUNT(*) with equality/range
     *   2: SELECT * LIMIT 10
     *   3: SELECT * with BETWEEN range scan
     *   4: SELECT * with IN list
     *   5: SELECT col covering index scan ORDER BY col
     *   6: SELECT * with multi-column composite index conditions
     */
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


    // ==================== Mode 20: NULL Index Handling ====================


    // ==================== Mode 21: Prefix Index (SUBSTRING Function Index) ====================


    // ==================== Mode 22: Subquery + Index ====================


    // ==================== Mode 23: Index Cond Pushdown (ICP Equivalent) ====================


    // ==================== Mode 24: BRIN Index (Block Range Index) ====================


    // ==================== Phase 3: Index Effectiveness Check ====================

    /**
     * Phase 3: Verify that the target index is actually used in the EXPLAIN plan.
     * Checks for index name in the plan output AND that the scan type
     * is not "Seq Scan" when an index was requested.
     *
     * Reference: MySQL isIndexEffectivelyUsed() method.
     */
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
