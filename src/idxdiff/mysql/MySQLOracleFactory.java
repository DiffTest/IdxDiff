package idxdiff.mysql;

import idxdiff.OracleFactory;
import idxdiff.common.oracle.TestOracle;
import idxdiff.mysql.oracle.MySQLIndexOracle;

public enum MySQLOracleFactory implements OracleFactory<MySQLGlobalState> {

    INDEX {
        @Override
        public TestOracle<MySQLGlobalState> create(MySQLGlobalState globalState) throws Exception {
            return new MySQLIndexOracle(globalState);
        }
    };
}
