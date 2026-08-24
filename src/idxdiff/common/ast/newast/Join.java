package idxdiff.common.ast.newast;

import idxdiff.common.schema.AbstractTable;
import idxdiff.common.schema.AbstractTableColumn;

public interface Join<E extends Expression<C>, T extends AbstractTable<C, ?, ?>, C extends AbstractTableColumn<?, ?>>
        extends Expression<C> {

    void setOnClause(E onClause);
}
