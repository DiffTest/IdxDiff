package idxdiff.mariadb.gen;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import idxdiff.Randomly;
import idxdiff.common.gen.NoRECGenerator;
import idxdiff.common.schema.AbstractTables;
import idxdiff.mariadb.MariaDBProvider;
import idxdiff.mariadb.MariaDBSchema.MariaDBColumn;
import idxdiff.mariadb.MariaDBSchema.MariaDBDataType;
import idxdiff.mariadb.MariaDBSchema.MariaDBTable;
import idxdiff.mariadb.ast.MariaDBAggregate;
import idxdiff.mariadb.ast.MariaDBAggregate.MariaDBAggregateFunction;
import idxdiff.mariadb.ast.MariaDBBetweenOperation;
import idxdiff.mariadb.ast.MariaDBBinaryOperator;
import idxdiff.mariadb.ast.MariaDBBinaryOperator.MariaDBBinaryComparisonOperator;
import idxdiff.mariadb.ast.MariaDBCaseOperator;
import idxdiff.mariadb.ast.MariaDBCastOperation;
import idxdiff.mariadb.ast.MariaDBCastOperation.MariaDBCastType;
import idxdiff.mariadb.ast.MariaDBColumnName;
import idxdiff.mariadb.ast.MariaDBConstant;
import idxdiff.mariadb.ast.MariaDBExists;
import idxdiff.mariadb.ast.MariaDBExpression;
import idxdiff.mariadb.ast.MariaDBFunction;
import idxdiff.mariadb.ast.MariaDBFunctionName;
import idxdiff.mariadb.ast.MariaDBInOperation;
import idxdiff.mariadb.ast.MariaDBJoin;
import idxdiff.mariadb.ast.MariaDBOrderByTerm;
import idxdiff.mariadb.ast.MariaDBOrderByTerm.MariaDBOrder;
import idxdiff.mariadb.ast.MariaDBPostfixUnaryOperation;
import idxdiff.mariadb.ast.MariaDBPostfixUnaryOperation.MariaDBPostfixUnaryOperator;
import idxdiff.mariadb.ast.MariaDBSelectStatement;
import idxdiff.mariadb.ast.MariaDBSelectStatement.MariaDBSelectType;
import idxdiff.mariadb.ast.MariaDBTableReference;
import idxdiff.mariadb.ast.MariaDBText;
import idxdiff.mariadb.ast.MariaDBUnaryPrefixOperation;
import idxdiff.mariadb.ast.MariaDBUnaryPrefixOperation.MariaDBUnaryPrefixOperator;

public class MariaDBExpressionGenerator
        implements NoRECGenerator<MariaDBSelectStatement, MariaDBJoin, MariaDBExpression, MariaDBTable, MariaDBColumn> {

    private final Randomly r;
    private List<MariaDBTable> targetTables = new ArrayList<>();
    private List<MariaDBColumn> columns = new ArrayList<>();

    public MariaDBExpressionGenerator(Randomly r) {
        this.r = r;
    }

    public static MariaDBConstant getRandomConstant(Randomly r) {
        MariaDBDataType option = Randomly.fromOptions(MariaDBDataType.values());
        return getRandomConstant(r, option);
    }

    public static MariaDBConstant getRandomConstant(Randomly r, MariaDBDataType option) throws AssertionError {
        if (Randomly.getBooleanWithSmallProbability()) {
            return MariaDBConstant.createNullConstant();
        }
        switch (option) {
        case REAL:
            // FIXME: bug workaround for MDEV-21032
            return MariaDBConstant.createIntConstant(r.getInteger());
        case INT:
            return MariaDBConstant.createIntConstant(r.getInteger());
        case VARCHAR:
            return MariaDBConstant.createTextConstant(r.getString());
        case BOOLEAN:
            return MariaDBConstant.createBooleanConstant(Randomly.getBoolean());
        default:
            throw new AssertionError(option);
        }
    }

    /**
     * Generate a random constant using the enhanced constant types (hex, bit,
     * scientific, decimal, date, timestamp, negative int, empty string, etc.)
     */
    public static MariaDBConstant getRandomEnhancedConstant(Randomly r) {
        return MariaDBConstant.getRandomConstantValue(r);
    }

    public MariaDBExpressionGenerator setColumns(List<MariaDBColumn> columns) {
        this.columns = columns;
        return this;
    }

    private enum ExpressionType {
        LITERAL, COLUMN, BINARY_COMPARISON, UNARY_POSTFIX_OPERATOR, UNARY_PREFIX_OPERATOR, FUNCTION, IN,
        BETWEEN, CASE_OP, CAST_OP, EXISTS_OP
    }

    public MariaDBExpression getRandomExpression(int depth) {
        if (depth >= MariaDBProvider.MAX_EXPRESSION_DEPTH || Randomly.getBoolean()) {
            if (Randomly.getBoolean() || columns.isEmpty()) {
                // Randomly choose between original and enhanced constant generation
                if (Randomly.getBooleanWithSmallProbability()) {
                    return getRandomEnhancedConstant(r);
                }
                return getRandomConstant(r);
            } else {
                return getRandomColumn();
            }
        }
        List<ExpressionType> expressionTypes = new ArrayList<>(Arrays.asList(ExpressionType.values()));
        if (columns.isEmpty()) {
            expressionTypes.remove(ExpressionType.COLUMN);
            expressionTypes.remove(ExpressionType.EXISTS_OP);
        }
        ExpressionType expressionType = Randomly.fromList(expressionTypes);
        switch (expressionType) {
        case COLUMN:
            return getRandomColumn();
        case LITERAL:
            // Randomly choose between original and enhanced constant generation
            if (Randomly.getBooleanWithSmallProbability()) {
                return getRandomEnhancedConstant(r);
            }
            return getRandomConstant(r);
        case BINARY_COMPARISON:
            return new MariaDBBinaryOperator(getRandomExpression(depth + 1), getRandomExpression(depth + 1),
                    MariaDBBinaryComparisonOperator.getRandom());
        case UNARY_PREFIX_OPERATOR:
            return new MariaDBUnaryPrefixOperation(getRandomExpression(depth + 1),
                    MariaDBUnaryPrefixOperator.getRandom());
        case UNARY_POSTFIX_OPERATOR:
            return new MariaDBPostfixUnaryOperation(MariaDBPostfixUnaryOperator.getRandom(),
                    getRandomExpression(depth + 1));
        case FUNCTION:
            MariaDBFunctionName func = MariaDBFunctionName.getRandom();
            return new MariaDBFunction(func, getArgs(func, depth + 1));
        case IN:
            return new MariaDBInOperation(getRandomExpression(depth + 1), getSmallNumberRandomExpressions(depth + 1),
                    Randomly.getBoolean());
        case BETWEEN:
            return new MariaDBBetweenOperation(getRandomExpression(depth + 1), getRandomExpression(depth + 1),
                    getRandomExpression(depth + 1), Randomly.getBoolean());
        case CASE_OP:
            return generateCaseExpression(depth);
        case CAST_OP:
            return new MariaDBCastOperation(getRandomExpression(depth + 1), MariaDBCastType.getRandom());
        case EXISTS_OP:
            return generateExistsExpression(depth);
        default:
            throw new AssertionError(expressionType);
        }
    }

    private MariaDBExpression generateCaseExpression(int depth) {
        int nrBranches = Randomly.smallNumber() + 1;
        List<MariaDBExpression> whenExprs = new ArrayList<>();
        List<MariaDBExpression> thenExprs = new ArrayList<>();
        for (int i = 0; i < nrBranches; i++) {
            whenExprs.add(getRandomExpression(depth + 1));
            thenExprs.add(getRandomExpression(depth + 1));
        }
        MariaDBExpression elseExpr = Randomly.getBoolean() ? getRandomExpression(depth + 1) : null;
        // With or without switch condition
        MariaDBExpression switchCondition = Randomly.getBoolean() ? getRandomExpression(depth + 1) : null;
        return new MariaDBCaseOperator(switchCondition, whenExprs, thenExprs, elseExpr);
    }

    private MariaDBExpression generateExistsExpression(int depth) {
        MariaDBSelectStatement subSelect = new MariaDBSelectStatement();
        MariaDBColumn dummyCol = new MariaDBColumn("0", MariaDBDataType.INT, false, 0);
        subSelect.setFetchColumns(Arrays.asList(new MariaDBColumnName(dummyCol)));
        if (!targetTables.isEmpty()) {
            MariaDBTable randomTable = Randomly.fromList(targetTables);
            subSelect.setFromList(Arrays.asList(new MariaDBTableReference(randomTable)));
        } else {
            // No target tables available — use a simple constant select without FROM
            subSelect.setFetchColumns(Arrays.asList(MariaDBConstant.createIntConstant(1)));
            // Must set fromList to avoid IllegalStateException in visitor
            subSelect.setFromList(Collections.emptyList());
        }
        subSelect.setWhereClause(getRandomExpression(depth + 1));
        return new MariaDBExists(subSelect);
    }

    private List<MariaDBExpression> getSmallNumberRandomExpressions(int depth) {
        List<MariaDBExpression> expressions = new ArrayList<>();
        for (int i = 0; i < Randomly.smallNumber() + 1; i++) {
            expressions.add(getRandomExpression(depth + 1));
        }
        return expressions;
    }

    private List<MariaDBExpression> getArgs(MariaDBFunctionName func, int depth) {
        List<MariaDBExpression> expressions = new ArrayList<>();
        for (int i = 0; i < func.getNrArgs(); i++) {
            expressions.add(getRandomExpression(depth + 1));
        }
        if (func.isVariadic()) {
            for (int i = 0; i < Randomly.smallNumber(); i++) {
                expressions.add(getRandomExpression(depth + 1));
            }
        }
        return expressions;
    }

    private MariaDBExpression getRandomColumn() {
        MariaDBColumn randomColumn = Randomly.fromList(columns);
        return new MariaDBColumnName(randomColumn);
    }

    public MariaDBExpression getRandomExpression() {
        return getRandomExpression(0);
    }

    /**
     * Generate a random ORDER BY term.
     */
    public MariaDBOrderByTerm getRandomOrderByTerm() {
        MariaDBExpression expr;
        if (Randomly.getBoolean() && !columns.isEmpty()) {
            expr = getRandomColumn();
        } else {
            expr = getRandomExpression();
        }
        return new MariaDBOrderByTerm(expr, MariaDBOrder.getRandomOrder());
    }

    /**
     * Generate a list of random ORDER BY terms.
     */
    public List<MariaDBOrderByTerm> getRandomOrderByTerms() {
        List<MariaDBOrderByTerm> terms = new ArrayList<>();
        int nr = Randomly.smallNumber() + 1;
        for (int i = 0; i < nr; i++) {
            terms.add(getRandomOrderByTerm());
        }
        return terms;
    }

    @Override
    public MariaDBExpressionGenerator setTablesAndColumns(AbstractTables<MariaDBTable, MariaDBColumn> targetTables) {
        this.targetTables = targetTables.getTables();
        this.columns = targetTables.getColumns();
        return this;
    }

    @Override
    public List<MariaDBExpression> getTableRefs() {
        List<MariaDBExpression> tableRefs = new ArrayList<>();
        for (MariaDBTable t : targetTables) {
            MariaDBTableReference tableRef = new MariaDBTableReference(t);
            tableRefs.add(tableRef);
        }
        return tableRefs;
    }

    @Override
    public MariaDBExpression generateBooleanExpression() {
        return getRandomExpression();
    }

    @Override
    public MariaDBSelectStatement generateSelect() {
        return new MariaDBSelectStatement();
    }

    @Override
    public List<MariaDBJoin> getRandomJoinClauses() {
        return MariaDBJoin.getRandomJoinClauses(targetTables, r);
    }

    @Override
    public String generateOptimizedQueryString(MariaDBSelectStatement select, MariaDBExpression whereCondition,
            boolean shouldUseAggregate) {
        if (shouldUseAggregate) {
            MariaDBAggregate aggr = new MariaDBAggregate(
                    new MariaDBColumnName(new MariaDBColumn("*", MariaDBDataType.INT, false, 0)),
                    MariaDBAggregateFunction.COUNT);
            select.setFetchColumns(Arrays.asList(aggr));
        } else {
            MariaDBColumnName aggr = new MariaDBColumnName(MariaDBColumn.createDummy("*"));
            select.setFetchColumns(Arrays.asList(aggr));
        }

        select.setWhereClause(whereCondition);
        select.setSelectType(MariaDBSelectType.ALL);
        return select.asString();
    }

    @Override
    public String generateUnoptimizedQueryString(MariaDBSelectStatement select, MariaDBExpression whereCondition) {
        MariaDBPostfixUnaryOperation isTrue = new MariaDBPostfixUnaryOperation(MariaDBPostfixUnaryOperator.IS_TRUE,
                whereCondition);
        MariaDBText asText = new MariaDBText(isTrue, " as count", false);
        select.setFetchColumns(Arrays.asList(asText));
        select.setSelectType(MariaDBSelectType.ALL);

        return "SELECT SUM(count) FROM (" + select.asString() + ") as asdf";
    }
}