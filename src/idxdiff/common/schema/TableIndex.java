package idxdiff.common.schema;

public class TableIndex {

    private final String indexName;
    private final boolean isPartial;

    protected TableIndex(String indexName) {
        this(indexName, false);
    }

    protected TableIndex(String indexName, boolean isPartial) {
        this.indexName = indexName;
        this.isPartial = isPartial;
    }

    public static TableIndex create(String indexName) {
        return new TableIndex(indexName);
    }

    public static TableIndex create(String indexName, boolean isPartial) {
        return new TableIndex(indexName, isPartial);
    }

    public String getIndexName() {
        return indexName;
    }

    public boolean isPartial() {
        return isPartial;
    }

    @Override
    public String toString() {
        return indexName;
    }

}
