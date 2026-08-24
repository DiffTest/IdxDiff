package idxdiff.common.ast.newast;

import idxdiff.common.schema.AbstractTableColumn;

public class ColumnReferenceNode<E, C extends AbstractTableColumn<?, ?>> {

    private final C c;

    public ColumnReferenceNode(C c) {
        this.c = c;
    }

    public C getColumn() {
        return c;
    }

}
