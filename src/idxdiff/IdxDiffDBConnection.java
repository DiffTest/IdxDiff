package idxdiff;

public interface IdxDiffDBConnection extends AutoCloseable {

    String getDatabaseVersion() throws Exception;
}
