package idxdiff.mariadb;

import java.sql.SQLException;

import idxdiff.OracleFactory;
import idxdiff.common.oracle.TestOracle;
import idxdiff.mariadb.oracle.MariaDBIndexOracle;

public enum MariaDBOracleFactory implements OracleFactory<MariaDBProvider.MariaDBGlobalState> {

    INDEX {
        @Override
        public TestOracle<MariaDBProvider.MariaDBGlobalState> create(MariaDBProvider.MariaDBGlobalState globalState)
                throws SQLException {
            return new MariaDBIndexOracle(globalState);
        }
    };
}
