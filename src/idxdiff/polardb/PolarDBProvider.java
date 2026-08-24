package idxdiff.polardb;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.sql.Statement;

import com.google.auto.service.AutoService;

import idxdiff.*;
import idxdiff.common.DBMSCommon;
import idxdiff.common.oracle.TestOracle;
import idxdiff.common.query.*;
import idxdiff.mysql.*;
import idxdiff.mysql.gen.MySQLDeleteGenerator;
import idxdiff.mysql.gen.MySQLInsertGenerator;
import idxdiff.mysql.gen.MySQLUpdateGenerator;
import idxdiff.mysql.gen.datadef.MySQLIndexGenerator;

@AutoService(DatabaseProvider.class)
public class PolarDBProvider extends SQLProviderAdapter<MySQLGlobalState, MySQLOptions> {

    private static final int PORT = 8527;

    public PolarDBProvider() { super(MySQLGlobalState.class, MySQLOptions.class); }

    enum Action implements AbstractAction<MySQLGlobalState> {
        SHOW_TABLES, INSERT, CREATE_INDEX, CREATE_TABLE, SELECT_INFO, ANALYZE_TABLE, UPDATE, DELETE;

        @Override
        public SQLQueryAdapter getQuery(MySQLGlobalState g) throws Exception {
            switch (this) {
            case SHOW_TABLES: return new SQLQueryAdapter("SHOW TABLES");
            case INSERT: return MySQLInsertGenerator.insertRow(g);
            case CREATE_INDEX: return MySQLIndexGenerator.create(g);
            case CREATE_TABLE:
                return PolarDBTableGenerator.generate(g,
                        DBMSCommon.createTableName(g.getSchema().getDatabaseTables().size()));
            case SELECT_INFO:
                return new SQLQueryAdapter(
                        "SELECT TABLE_NAME, ENGINE FROM information_schema.TABLES WHERE table_schema='"
                                + g.getDatabaseName() + "'");
            case ANALYZE_TABLE: {
                var ts = g.getSchema().getDatabaseTables();
                if (ts.isEmpty()) throw new IgnoreMeException();
                return new SQLQueryAdapter("ANALYZE TABLE " + Randomly.fromList(ts).getName() + ";",
                        ExpectedErrors.newErrors().build(), true);
            }
            case UPDATE: return MySQLUpdateGenerator.create(g);
            case DELETE: return MySQLDeleteGenerator.delete(g);
            default: throw new AssertionError(this);
            }
        }
    }

    private static int mapActions(MySQLGlobalState g, Action a) {
        Randomly r = g.getRandomly();
        switch (a) {
        case SHOW_TABLES: return r.getInteger(0, 1);
        case CREATE_TABLE: return r.getInteger(0, 1);
        case INSERT: return r.getInteger(0, g.getOptions().getMaxNumberInserts());
        case CREATE_INDEX: return r.getInteger(0, 5);
        case SELECT_INFO: return r.getInteger(0, 5);
        case ANALYZE_TABLE: return r.getInteger(0, 3);
        case UPDATE: return r.getInteger(0, 5);
        case DELETE: return r.getInteger(0, 3);
        default: throw new AssertionError(a);
        }
    }

    @Override
    public void generateDatabase(MySQLGlobalState g) throws Exception {
        while (g.getSchema().getDatabaseTables().size() < Randomly.smallNumber() + 1)
            g.executeStatement(PolarDBTableGenerator.generate(g,
                    DBMSCommon.createTableName(g.getSchema().getDatabaseTables().size())));
        new StatementExecutor<>(g, Action.values(), PolarDBProvider::mapActions, q -> {
            if (g.getSchema().getDatabaseTables().isEmpty()) throw new IgnoreMeException();
        }).executeStatements();
    }

    @Override
    public SQLConnection createDatabase(MySQLGlobalState g) throws SQLException {
        String host = g.getOptions().getHost() != null ? g.getOptions().getHost() : "localhost";
        int port = g.getOptions().getPort() != MainOptions.NO_SET_PORT ? g.getOptions().getPort() : PORT;
        String db = g.getDatabaseName();
        Connection con = DriverManager.getConnection(
                String.format("jdbc:mysql://%s:%d?serverTimezone=UTC&useSSL=false&allowPublicKeyRetrieval=true",
                        host, port),
                g.getOptions().getUserName(), g.getOptions().getPassword());
        try (Statement s = con.createStatement()) { s.execute("DROP DATABASE IF EXISTS " + db); }
        catch (SQLException e) {}
        try (Statement s = con.createStatement()) { s.execute("CREATE DATABASE " + db); }
        try (Statement s = con.createStatement()) { s.execute("USE " + db); }
        return new SQLConnection(con);
    }

    @Override protected void checkViewsAreValid(MySQLGlobalState g) {}
    @Override public String getDBMSName() { return "polardb"; }

    @Override
    protected TestOracle<MySQLGlobalState> getTestOracle(MySQLGlobalState g) throws Exception {
        return new PolarDBIndexOracle(g);
    }
}
