package idxdiff.common.gen;

import java.util.List;

import idxdiff.common.ast.newast.Expression;
import idxdiff.common.ast.newast.Join;
import idxdiff.common.ast.newast.Select;
import idxdiff.common.schema.AbstractTable;
import idxdiff.common.schema.AbstractTableColumn;
import idxdiff.common.schema.AbstractTables;

public interface NoRECGenerator<S extends Select<J, E, T, C>, J extends Join<E, T, C>, E extends Expression<C>, T extends AbstractTable<C, ?, ?>, C extends AbstractTableColumn<?, ?>> {

    NoRECGenerator<S, J, E, T, C> setTablesAndColumns(AbstractTables<T, C> tables);

    E generateBooleanExpression();

    S generateSelect();

    List<J> getRandomJoinClauses();

    List<E> getTableRefs();

    /**
     * Generates a query string that is likely to be optimized by the DBMS.
     *
     * @param select
     *            the base select expression used to generate the query
     * @param whereCondition
     *            a condition where records will be checked with
     * @param shouldUseAggregate
     *            whether to aggregate the record counts (`true`) or display records as is (`false`)
     *
     * @return a query string to be executed
     */
    String generateOptimizedQueryString(S select, E whereCondition, boolean shouldUseAggregate);

    /**
     * Generates a query string that is unlikely to be optimized by the DBMS.
     *
     * @param select
     *            the base select expression used to generate the query
     * @param whereCondition
     *            the condition each record will be checked with
     *
     * @return a query string to be executed
     */
    String generateUnoptimizedQueryString(S select, E whereCondition);
}
