package idxdiff.polardb;

import idxdiff.OracleFactory;
import idxdiff.common.oracle.TestOracle;
import idxdiff.mysql.MySQLGlobalState;

public enum PolarDBOracleFactory implements OracleFactory<MySQLGlobalState> {

    INDEX {
        @Override
        public TestOracle<MySQLGlobalState> create(MySQLGlobalState globalState) {
            return new PolarDBIndexOracle(globalState);
        }
    };

}
