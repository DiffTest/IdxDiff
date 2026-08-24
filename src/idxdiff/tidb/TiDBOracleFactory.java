package idxdiff.tidb;

import java.sql.SQLException;

import idxdiff.OracleFactory;
import idxdiff.common.oracle.TestOracle;
import idxdiff.tidb.oracle.TiDBIndexOracle;

public enum TiDBOracleFactory implements OracleFactory<TiDBProvider.TiDBGlobalState> {

    INDEX {
        @Override
        public TestOracle<TiDBProvider.TiDBGlobalState> create(TiDBProvider.TiDBGlobalState globalState)
                throws SQLException {
            return new TiDBIndexOracle(globalState);
        }
    };

}
