package idxdiff.tidb;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import idxdiff.IgnoreMeException;
import idxdiff.Randomly;
import idxdiff.common.gen.CERTGenerator;
import idxdiff.common.gen.TLPWhereGenerator;
import idxdiff.common.gen.UntypedExpressionGenerator;
import idxdiff.common.schema.AbstractTables;
import idxdiff.tidb.TiDBProvider.TiDBGlobalState;
import idxdiff.tidb.TiDBSchema.TiDBColumn;
import idxdiff.tidb.TiDBSchema.TiDBCompositeDataType;
import idxdiff.tidb.TiDBSchema.TiDBDataType;
import idxdiff.tidb.TiDBSchema.TiDBTable;
import idxdiff.tidb.ast.TiDBAggregate;
import idxdiff.tidb.ast.TiDBAggregate.TiDBAggregateFunction;
import idxdiff.tidb.ast.TiDBBinaryBitOperation;
import idxdiff.tidb.ast.TiDBBinaryBitOperation.TiDBBinaryBitOperator;
import idxdiff.tidb.ast.TiDBBinaryComparisonOperation;
import idxdiff.tidb.ast.TiDBBinaryComparisonOperation.TiDBComparisonOperator;
import idxdiff.tidb.ast.TiDBBinaryLogicalOperation;
import idxdiff.tidb.ast.TiDBBinaryLogicalOperation.TiDBBinaryLogicalOperator;
import idxdiff.tidb.ast.TiDBCase;
import idxdiff.tidb.ast.TiDBCastOperation;
import idxdiff.tidb.ast.TiDBColumnReference;
import idxdiff.tidb.ast.TiDBConstant;
import idxdiff.tidb.ast.TiDBExpression;
import idxdiff.tidb.ast.TiDBFunctionCall;
import idxdiff.tidb.ast.TiDBFunctionCall.TiDBFunction;
import idxdiff.tidb.ast.TiDBJoin;
import idxdiff.tidb.ast.TiDBJoin.JoinType;
import idxdiff.tidb.ast.TiDBOrderingTerm;
import idxdiff.tidb.ast.TiDBRegexOperation;
import idxdiff.tidb.ast.TiDBRegexOperation.TiDBRegexOperator;
import idxdiff.tidb.ast.TiDBSelect;
import idxdiff.tidb.ast.TiDBTableReference;
import idxdiff.tidb.ast.TiDBUnaryPostfixOperation;
import idxdiff.tidb.ast.TiDBUnaryPostfixOperation.TiDBUnaryPostfixOperator;
import idxdiff.tidb.ast.TiDBUnaryPrefixOperation;
import idxdiff.tidb.ast.TiDBUnaryPrefixOperation.TiDBUnaryPrefixOperator;

public class TiDBExpressionGenerator extends UntypedExpressionGenerator<TiDBExpression, TiDBColumn>
        implements TLPWhereGenerator<TiDBSelect, TiDBJoin, TiDBExpression, TiDBTable, TiDBColumn>,
        CERTGenerator<TiDBSelect, TiDBJoin, TiDBExpression, TiDBTable, TiDBColumn> {

    private enum Gen {
        UNARY_PREFIX, //
        UNARY_POSTFIX, //
        CONSTANT, //
        COLUMN, //
        COMPARISON, REGEX, FUNCTION, BINARY_LOGICAL, BINARY_BIT, CAST, DEFAULT, CASE
        // BINARY_ARITHMETIC
    }

    private final TiDBGlobalState globalState;

    private List<TiDBTable> tables;

    public TiDBExpressionGenerator(TiDBGlobalState globalState) {
        this.globalState = globalState;
    }

    @Override
    public TiDBExpression generateConstant() {
        TiDBDataType type = TiDBDataType.getRandom();
        if (Randomly.getBooleanWithRatherLowProbability()) {
            return TiDBConstant.createNullConstant();
        }
        switch (type) {
        case INT:
            return TiDBConstant.createIntConstant(globalState.getRandomly().getInteger());
        case BLOB:
        case TEXT:
            return TiDBConstant.createStringConstant(globalState.getRandomly().getString());
        case BOOL:
            return TiDBConstant.createBooleanConstant(Randomly.getBoolean());
        case FLOATING:
            return TiDBConstant.createFloatConstant(globalState.getRandomly().getDouble());
        case CHAR:
            return TiDBConstant.createStringConstant(globalState.getRandomly().getChar());
        case DECIMAL:
        case NUMERIC:
            return TiDBConstant.createIntConstant(globalState.getRandomly().getInteger());
        case DATE:
            return TiDBConstant.createStringConstant(generateRandomDateString());
        default:
            throw new AssertionError();
        }
    }

    @Override
    public List<TiDBExpression> generateOrderBys() {
        List<TiDBExpression> expressions = super.generateOrderBys();
        List<TiDBExpression> newExpressions = new ArrayList<>();
        for (TiDBExpression expr : expressions) {
            TiDBExpression newExpr = expr;
            if (Randomly.getBoolean()) {
                newExpr = new TiDBOrderingTerm(expr, Randomly.getBoolean());
            }
            newExpressions.add(newExpr);
        }
        return newExpressions;
    }

    @Override
    public TiDBExpression negatePredicate(TiDBExpression predicate) {
        return new TiDBUnaryPrefixOperation(predicate, TiDBUnaryPrefixOperator.NOT);
    }

    @Override
    public TiDBExpression isNull(TiDBExpression expr) {
        return new TiDBUnaryPostfixOperation(expr, TiDBUnaryPostfixOperator.IS_NULL);
    }

    public TiDBExpression generateConstant(TiDBDataType type) {
        if (Randomly.getBooleanWithRatherLowProbability()) {
            return TiDBConstant.createNullConstant();
        }
        switch (type) {
        case INT:
            return TiDBConstant.createIntConstant(globalState.getRandomly().getInteger());
        case BLOB:
        case TEXT:
            return TiDBConstant.createStringConstant(globalState.getRandomly().getString());
        case BOOL:
            return TiDBConstant.createBooleanConstant(Randomly.getBoolean());
        case FLOATING:
            return TiDBConstant.createFloatConstant(globalState.getRandomly().getDouble());
        case CHAR:
            return TiDBConstant.createStringConstant(globalState.getRandomly().getChar());
        case DECIMAL:
        case NUMERIC:
            return TiDBConstant.createIntConstant(globalState.getRandomly().getInteger());
        case DATE:
            return TiDBConstant.createStringConstant(generateRandomDateString());
        default:
            throw new AssertionError();
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

    @Override
    public TiDBExpressionGenerator setTablesAndColumns(AbstractTables<TiDBTable, TiDBColumn> tables) {
        this.columns = tables.getColumns();
        this.tables = tables.getTables();

        return this;
    }

    @Override
    public TiDBExpression generateBooleanExpression() {
        return generateExpression();
    }

    @Override
    public TiDBSelect generateSelect() {
        return new TiDBSelect();
    }

    @Override
    public List<TiDBJoin> getRandomJoinClauses() {
        List<TiDBExpression> tableList = tables.stream().map(t -> new TiDBTableReference(t))
                .collect(Collectors.toList());
        List<TiDBJoin> joins = TiDBJoin.getJoins(tableList, globalState);
        tables = tableList.stream().map(t -> ((TiDBTableReference) t).getTable()).collect(Collectors.toList());
        return joins;
    }

    @Override
    public List<TiDBExpression> getTableRefs() {
        return tables.stream().map(t -> new TiDBTableReference(t)).collect(Collectors.toList());
    }

    @Override
    public List<TiDBExpression> generateFetchColumns(boolean shouldCreateDummy) {
        if (shouldCreateDummy && Randomly.getBoolean()) {
            return List.of(new TiDBColumnReference(
                    new TiDBColumn("*", new TiDBCompositeDataType(TiDBDataType.INT), false, false, false)));
        }
        return Randomly.nonEmptySubset(this.columns).stream().map(c -> new TiDBColumnReference(c))
                .collect(Collectors.toList());
    }

    @Override
    protected TiDBExpression generateExpression(int depth) {
        if (depth >= globalState.getOptions().getMaxExpressionDepth() || Randomly.getBoolean()) {
            return generateLeafNode();
        }
        if (allowAggregates && Randomly.getBoolean()) {
            allowAggregates = false;
            TiDBAggregateFunction func = TiDBAggregateFunction.getRandom();
            List<TiDBExpression> args = generateExpressions(func.getNrArgs());
            return new TiDBAggregate(args, func);
        }
        switch (Randomly.fromOptions(Gen.values())) {
        case DEFAULT:
            if (globalState.getSchema().getDatabaseTables().isEmpty()) {
                throw new IgnoreMeException();
            }
            TiDBColumn column = Randomly.fromList(columns);
            if (column.hasDefault()) {
                return new TiDBFunctionCall(TiDBFunction.DEFAULT, Arrays.asList(new TiDBColumnReference(column)));
            }
            throw new IgnoreMeException();
        case UNARY_POSTFIX:
            return new TiDBUnaryPostfixOperation(generateExpression(depth + 1), TiDBUnaryPostfixOperator.getRandom());
        case UNARY_PREFIX:
            TiDBUnaryPrefixOperator rand = TiDBUnaryPrefixOperator.getRandom();
            return new TiDBUnaryPrefixOperation(generateExpression(depth + 1), rand);
        case COLUMN:
            return generateColumn();
        case CONSTANT:
            return generateConstant();
        case COMPARISON:
            return new TiDBBinaryComparisonOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBComparisonOperator.getRandom());
        case REGEX:
            return new TiDBRegexOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBRegexOperator.getRandom());
        case FUNCTION:
            TiDBFunction func = TiDBFunction.getRandom();
            return new TiDBFunctionCall(func, generateSafeFunctionArgs(func, depth));
        case BINARY_BIT:
            return new TiDBBinaryBitOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBBinaryBitOperator.getRandom());
        case BINARY_LOGICAL:
            return new TiDBBinaryLogicalOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBBinaryLogicalOperator.getRandom());
        case CAST:
            return new TiDBCastOperation(generateExpression(depth + 1), Randomly.fromOptions("BINARY", // https://github.com/tidb-challenge-program/bug-hunting-issue/issues/52
                    "CHAR", "DATE", "DATETIME", "TIME", // https://github.com/tidb-challenge-program/bug-hunting-issue/issues/13
                    "DECIMAL", "SIGNED", "UNSIGNED" /* https://github.com/pingcap/tidb/issues/16028 */));
        case CASE:
            int nr = Randomly.fromOptions(1, 2);
            return new TiDBCase(generateExpression(depth + 1), generateExpressions(nr, depth + 1),
                    generateExpressions(nr, depth + 1), generateExpression(depth + 1));
        default:
            throw new AssertionError();
        }
    }

    @Override
    protected TiDBExpression generateColumn() {
        TiDBColumn column = Randomly.fromList(columns);
        return new TiDBColumnReference(column);
    }

    @Override
    public String generateExplainQuery(TiDBSelect select) {
        return "EXPLAIN " + select.asString();
    }

    @Override
    public boolean mutate(TiDBSelect select) {
        List<Function<TiDBSelect, Boolean>> mutators = new ArrayList<>();

        mutators.add(this::mutateJoin);
        mutators.add(this::mutateWhere);
        if (!TiDBBugs.bug38319) {
            mutators.add(this::mutateGroupBy);
            mutators.add(this::mutateHaving);
        }
        mutators.add(this::mutateAnd);
        if (!TiDBBugs.bug51525) {
            mutators.add(this::mutateOr);
        }
        mutators.add(this::mutateLimit);
        // mutators.add(this::mutateDistinct);

        return Randomly.fromList(mutators).apply(select);
    }

    boolean mutateJoin(TiDBSelect select) {
        if (select.getJoinList().isEmpty()) {
            return false;
        }
        TiDBJoin join = (TiDBJoin) Randomly.fromList(select.getJoinList());
        if (join.getJoinType() == JoinType.NATURAL) {
            return false;
        }

        // CROSS does not need ON Condition, while other joins do
        // To avoid Null pointer, generating a new new condition when mutating CROSS to
        // other joins
        if (join.getJoinType() == JoinType.CROSS) {
            List<TiDBColumn> columns = new ArrayList<>();
            columns.addAll(((TiDBTableReference) join.getLeftTable()).getTable().getColumns());
            columns.addAll(((TiDBTableReference) join.getRightTable()).getTable().getColumns());
            TiDBExpressionGenerator joinGen2 = new TiDBExpressionGenerator(globalState).setColumns(columns);
            join.setOnCondition(joinGen2.generateExpression());
        }

        JoinType newJoinType = TiDBJoin.JoinType.INNER;
        if (join.getJoinType() == JoinType.LEFT || join.getJoinType() == JoinType.RIGHT) { // No invarient relation
                                                                                           // between LEFT and RIGHT
                                                                                           // join
            newJoinType = JoinType.getRandomExcept(JoinType.NATURAL, JoinType.LEFT, JoinType.RIGHT);
        } else {
            newJoinType = JoinType.getRandomExcept(JoinType.NATURAL, join.getJoinType());
        }
        assert newJoinType != JoinType.NATURAL; // Natural Join is not supported for CERT
        boolean increase = join.getJoinType().ordinal() < newJoinType.ordinal();
        join.setJoinType(newJoinType);
        if (newJoinType == JoinType.CROSS) {
            join.setOnCondition(null);
        }
        return increase;
    }

    boolean mutateWhere(TiDBSelect select) {
        boolean increase = select.getWhereClause() != null;
        if (increase) {
            select.setWhereClause(null);
        } else {
            select.setWhereClause(generateExpression());
        }
        return increase;
    }

    boolean mutateHaving(TiDBSelect select) {
        if (select.getGroupByExpressions().isEmpty()) {
            select.setGroupByExpressions(select.getFetchColumns());
            select.setHavingClause(generateExpression());
            return false;
        } else {
            if (select.getHavingClause() == null) {
                select.setHavingClause(generateExpression());
                return false;
            } else {
                select.setHavingClause(null);
                return true;
            }
        }
    }

    boolean mutateAnd(TiDBSelect select) {
        if (select.getWhereClause() == null) {
            select.setWhereClause(generateExpression());
        } else {
            TiDBExpression newWhere = new TiDBBinaryLogicalOperation(select.getWhereClause(), generateExpression(),
                    TiDBBinaryLogicalOperator.AND);
            select.setWhereClause(newWhere);
        }
        return false;
    }

    boolean mutateOr(TiDBSelect select) {
        if (select.getWhereClause() == null) {
            select.setWhereClause(generateExpression());
            return false;
        } else {
            TiDBExpression newWhere = new TiDBBinaryLogicalOperation(select.getWhereClause(), generateExpression(),
                    TiDBBinaryLogicalOperator.OR);
            select.setWhereClause(newWhere);
            return true;
        }
    }

    boolean mutateLimit(TiDBSelect select) {
        boolean increase = select.getLimitClause() != null;
        if (increase) {
            select.setLimitClause(null);
        } else {
            select.setLimitClause(generateConstant(TiDBDataType.INT));
        }
        return increase;
    }

    private boolean mutateGroupBy(TiDBSelect select) {
        boolean increase = !select.getGroupByExpressions().isEmpty();
        if (increase) {
            select.clearGroupByExpressions();
            select.clearHavingClause();
        } else {
            select.setGroupByExpressions(select.getFetchColumns());
        }
        return increase;
    }

    // ===================== Type-Aware Expression Generation =====================
    // These methods generate expressions that produce values compatible with a
    // target TiDBDataType, preventing "cannot convert datum" errors in UPDATE SET.

    /**
     * Generates an expression whose result type is compatible with the given expected type.
     * Used for UPDATE SET clause and other contexts where type compatibility matters.
     */
    public TiDBExpression generateExpression(TiDBDataType expectedType) {
        return generateExpression(expectedType, 0);
    }

    /**
     * Internal recursive method for type-aware expression generation.
     * At leaf level, generates constants or selects columns of compatible types.
     * At non-leaf level, selects only operations that can produce the expected type.
     */
    private TiDBExpression generateExpression(TiDBDataType expectedType, int depth) {
        if (depth >= globalState.getOptions().getMaxExpressionDepth() || Randomly.getBoolean()) {
            return generateTypeCompatibleLeaf(expectedType);
        }

        Gen[] compatibleOps = getCompatibleOperations(expectedType);
        switch (Randomly.fromOptions(compatibleOps)) {
        case CONSTANT:
            return generateConstant(expectedType);
        case COLUMN:
            return generateTypeCompatibleColumn(expectedType);
        case CAST: {
            // CAST can convert any inner expression to the target type
            return new TiDBCastOperation(generateExpression(depth + 1), getCastTargetForType(expectedType));
        }
        case CASE: {
            int nr = Randomly.fromOptions(1, 2);
            // CASE switchCondition (untyped), conditions (untyped), expressions (typed), elseExpr (typed)
            return new TiDBCase(generateExpression(depth + 1),
                    generateExpressionsOfType(nr, depth + 1, expectedType),
                    generateExpressionsOfType(nr, depth + 1, expectedType),
                    generateExpression(expectedType, depth + 1));
        }
        case FUNCTION: {
            TiDBFunction func = TiDBFunction.getRandom();
            return new TiDBFunctionCall(func, generateSafeFunctionArgs(func, depth));
        }
        case COMPARISON:
            return new TiDBBinaryComparisonOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBComparisonOperator.getRandom());
        case BINARY_BIT:
            return new TiDBBinaryBitOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBBinaryBitOperator.getRandom());
        case BINARY_LOGICAL:
            return new TiDBBinaryLogicalOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBBinaryLogicalOperator.getRandom());
        case UNARY_PREFIX: {
            TiDBUnaryPrefixOperator rand = TiDBUnaryPrefixOperator.getRandom();
            return new TiDBUnaryPrefixOperation(generateExpression(depth + 1), rand);
        }
        case UNARY_POSTFIX:
            return new TiDBUnaryPostfixOperation(generateExpression(depth + 1), TiDBUnaryPostfixOperator.getRandom());
        case REGEX:
            return new TiDBRegexOperation(generateExpression(depth + 1), generateExpression(depth + 1),
                    TiDBRegexOperator.getRandom());
        case DEFAULT:
            if (globalState.getSchema().getDatabaseTables().isEmpty()) {
                throw new IgnoreMeException();
            }
            TiDBColumn column = Randomly.fromList(columns);
            if (column.hasDefault()) {
                return new TiDBFunctionCall(TiDBFunction.DEFAULT, Arrays.asList(new TiDBColumnReference(column)));
            }
            throw new IgnoreMeException();
        default:
            return generateConstant(expectedType);
        }
    }

    /**
     * Generates a leaf node (constant or column) compatible with the expected type.
     */
    private TiDBExpression generateTypeCompatibleLeaf(TiDBDataType expectedType) {
        if (Randomly.getBoolean()) {
            return generateConstant(expectedType);
        } else {
            TiDBExpression colExpr = generateTypeCompatibleColumn(expectedType);
            if (colExpr != null) {
                return colExpr;
            }
            // No compatible column found; fall back to constant
            return generateConstant(expectedType);
        }
    }

    /**
     * Selects a column whose type is compatible with the expected type.
     * Returns null if no compatible column exists.
     */
    private TiDBExpression generateTypeCompatibleColumn(TiDBDataType expectedType) {
        List<TiDBColumn> compatibleColumns = columns.stream()
                .filter(c -> expectedType.isCompatibleWith(c.getType().getPrimitiveDataType()))
                .collect(Collectors.toList());

        if (compatibleColumns.isEmpty()) {
            return null;
        }
        return new TiDBColumnReference(Randomly.fromList(compatibleColumns));
    }

    /**
     * Returns the set of Gen operations that can produce values compatible with the expected type.
     */
    private Gen[] getCompatibleOperations(TiDBDataType expectedType) {
        switch (expectedType) {
        case INT:
        case BOOL:
            // Numeric/boolean: support arithmetic, comparison, bit, logical operations
            return new Gen[] { Gen.CONSTANT, Gen.COLUMN, Gen.COMPARISON, Gen.BINARY_BIT, Gen.BINARY_LOGICAL,
                    Gen.CAST, Gen.UNARY_PREFIX, Gen.UNARY_POSTFIX, Gen.CASE, Gen.FUNCTION };
        case FLOATING:
        case DECIMAL:
        case NUMERIC:
            // Numeric: similar to INT but skip bit operations (result is always integer)
            return new Gen[] { Gen.CONSTANT, Gen.COLUMN, Gen.COMPARISON, Gen.CAST, Gen.UNARY_PREFIX, Gen.CASE,
                    Gen.FUNCTION };
        case TEXT:
        case CHAR:
        case BLOB:
            // String types: accept all operations (MySQL converts everything to string)
            return Gen.values();
        case DATE:
            // DATE: only safe operations (constant, column, CAST, CASE)
            // Numeric/bit/logical operations produce non-DATE results
            return new Gen[] { Gen.CONSTANT, Gen.COLUMN, Gen.CAST, Gen.CASE };
        default:
            return new Gen[] { Gen.CONSTANT, Gen.COLUMN, Gen.CAST };
        }
    }

    /**
     * Maps a TiDBDataType to the corresponding SQL CAST target type string.
     */
    private String getCastTargetForType(TiDBDataType type) {
        switch (type) {
        case DATE:
            return "DATE";
        case INT:
        case BOOL:
            return "SIGNED";
        case FLOATING:
            return "DECIMAL";
        case DECIMAL:
        case NUMERIC:
            return "DECIMAL";
        case TEXT:
        case CHAR:
            return "CHAR";
        case BLOB:
            return "BINARY";
        default:
            return "CHAR";
        }
    }

    /**
     * Generates function arguments with special handling for functions that can
     * produce non-UTF-8 binary output (UNHEX, FROM_BASE64). For these functions,
     * we constrain the arguments to ensure the output is always valid UTF-8,
     * avoiding charset conversion errors in JDBC.
     */
    private List<TiDBExpression> generateSafeFunctionArgs(TiDBFunction func, int depth) {
        switch (func) {
        case UNHEX:
            // UNHEX produces binary bytes; ensure input is a hex string that maps to
            // ASCII-safe bytes (0x20-0x7E) to guarantee valid UTF-8 output
            return List.of(TiDBConstant.createStringConstant(generateSafeHexString()));
        case FROM_BASE64:
            // FROM_BASE64 decodes to arbitrary bytes; ensure the base64 string decodes
            // to ASCII-safe bytes to guarantee valid UTF-8 output
            return List.of(TiDBConstant.createStringConstant(generateSafeBase64String()));
        default:
            return generateExpressions(func.getNrArgs(), depth);
        }
    }

    /**
     * Generates a random hex string where each byte pair maps to a printable ASCII
     * character (0x20-0x7E), ensuring UNHEX output is always valid UTF-8.
     */
    private static String generateSafeHexString() {
        int byteCount = 1 + (int) (Math.random() * 8);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < byteCount; i++) {
            int b = 0x20 + (int) (Math.random() * 95); // printable ASCII: 0x20-0x7E
            sb.append(String.format("%02X", b));
        }
        return sb.toString();
    }

    /**
     * Generates a valid Base64 string that, when decoded by FROM_BASE64, produces
     * printable ASCII bytes, ensuring the output is always valid UTF-8.
     */
    private static String generateSafeBase64String() {
        int byteCount = 1 + (int) (Math.random() * 8);
        byte[] bytes = new byte[byteCount];
        for (int i = 0; i < byteCount; i++) {
            bytes[i] = (byte) (0x20 + (int) (Math.random() * 95)); // printable ASCII: 0x20-0x7E
        }
        return java.util.Base64.getEncoder().encodeToString(bytes);
    }

    /**
     * Generates a list of type-compatible expressions.
     */
    private List<TiDBExpression> generateExpressionsOfType(int count, int depth, TiDBDataType expectedType) {
        List<TiDBExpression> exprs = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            exprs.add(generateExpression(expectedType, depth));
        }
        return exprs;
    }
}
