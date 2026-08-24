package idxdiff.tidb;

// do not make the fields final to avoid warnings
public final class TiDBBugs {
    // https://github.com/pingcap/tidb/issues/35677
    public static boolean bug35677 = true;

    // https://github.com/pingcap/tidb/issues/35522
    // [FIX] Bug has been fixed — set to false so new "Unknown column" errors are caught
    public static boolean bug35522 = false;

    // https://github.com/pingcap/tidb/issues/35652
    // [FIX] Bug has been fixed — set to false so new "Cannot convert" errors are caught
    public static boolean bug35652 = false;

    // https://github.com/pingcap/tidb/issues/38295
    public static boolean bug38295 = true;

    // https://github.com/pingcap/tidb/issues/38319
    public static boolean bug38319 = true;

    // https://github.com/pingcap/tidb/issues/44747
    public static boolean bug44747 = true;

    // https://github.com/pingcap/tidb/issues/46556
    public static boolean bug46556 = true;

    // https://github.com/pingcap/tidb/issues/46591
    public static boolean bug46591 = true;

    // https://github.com/pingcap/tidb/issues/46598
    public static boolean bug46598 = true;

    // https://github.com/pingcap/tidb/issues/47346
    public static boolean bug47346 = true;

    // https://github.com/pingcap/tidb/issues/47348
    public static boolean bug47348 = true;

    // https://github.com/pingcap/tidb/issues/51525
    public static boolean bug51525 = true;

    private TiDBBugs() {
    }

}
