package idxdiff.mysql.ast;

import idxdiff.mysql.MySQLSchema.MySQLTable;

public class MySQLTableReference implements MySQLExpression {

    private final MySQLTable table;
    private String alias;

    public MySQLTableReference(MySQLTable table) {
        this.table = table;
    }

    public MySQLTableReference(MySQLTable table, String alias) {
        this.table = table;
        this.alias = alias;
    }

    public MySQLTable getTable() {
        return table;
    }

    public String getAlias() {
        return alias;
    }

    public void setAlias(String alias) {
        this.alias = alias;
    }

    public boolean hasAlias() {
        return alias != null && !alias.isEmpty();
    }

}