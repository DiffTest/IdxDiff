package idxdiff.postgres;

import idxdiff.OracleFactory;
import idxdiff.common.oracle.TestOracle;
import idxdiff.postgres.oracle.PostgresIndexOracle;

public enum PostgresOracleFactory implements OracleFactory<PostgresGlobalState> {

    INDEX {
        @Override
        public TestOracle<PostgresGlobalState> create(PostgresGlobalState globalState) throws Exception {
            return new PostgresIndexOracle(globalState);
        }

    };

}
