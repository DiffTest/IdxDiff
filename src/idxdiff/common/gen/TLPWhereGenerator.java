package idxdiff.common.gen;

import java.util.List;

import idxdiff.common.ast.newast.Expression;
import idxdiff.common.ast.newast.Join;
import idxdiff.common.ast.newast.Select;
import idxdiff.common.schema.AbstractTable;
import idxdiff.common.schema.AbstractTableColumn;
import idxdiff.common.schema.AbstractTables;

public interface TLPWhereGenerator<S extends Select<J, E, T, C>, J extends Join<E, T, C>, E extends Expression<C>, T extends AbstractTable<C, ?, ?>, C extends AbstractTableColumn<?, ?>>
        extends PartitionGenerator<E, C> {

    TLPWhereGenerator<S, J, E, T, C> setTablesAndColumns(AbstractTables<T, C> tables);

    E generateBooleanExpression();

    S generateSelect();

    List<J> getRandomJoinClauses();

    List<E> getTableRefs();

    List<E> generateFetchColumns(boolean shouldCreateDummy);

    List<E> generateOrderBys();
}
