
package idxdiff.mysql;

import java.sql.SQLException;

import idxdiff.SQLGlobalState;

public class MySQLGlobalState extends SQLGlobalState<MySQLOptions, MySQLSchema> {

    @Override
    protected MySQLSchema readSchema() throws SQLException {
        return MySQLSchema.fromConnection(getConnection(), getDatabaseName());
    }

}
