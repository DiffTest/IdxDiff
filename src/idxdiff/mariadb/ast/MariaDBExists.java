package idxdiff.mariadb.ast;

public class MariaDBExists implements MariaDBExpression {

    private final MariaDBSelectStatement subquery;

    public MariaDBExists(MariaDBSelectStatement subquery) {
        this.subquery = subquery;
    }

    public MariaDBSelectStatement getSubquery() {
        return subquery;
    }

}