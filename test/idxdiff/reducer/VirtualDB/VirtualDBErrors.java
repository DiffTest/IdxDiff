package idxdiff.reducer.VirtualDB;

import idxdiff.common.query.ExpectedErrors;

public final class VirtualDBErrors {
    public VirtualDBErrors() {
    }

    public static void addErrors(ExpectedErrors errors) {
        errors.add("Default error");
    }
}
