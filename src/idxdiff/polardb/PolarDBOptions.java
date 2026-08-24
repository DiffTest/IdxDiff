package idxdiff.polardb;

import java.util.Arrays;
import java.util.List;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;

import idxdiff.DBMSSpecificOptions;

@Parameters(separators = "=", commandDescription = "PolarDB-X (port 8527)")
public class PolarDBOptions implements DBMSSpecificOptions<PolarDBOracleFactory> {
    public static final String DEFAULT_HOST = "localhost";
    public static final int DEFAULT_PORT = 8527;

    @Parameter(names = "--oracle")
    public List<PolarDBOracleFactory> oracles = Arrays.asList(PolarDBOracleFactory.INDEX);

    @Override
    public List<PolarDBOracleFactory> getTestOracleFactory() { return oracles; }
}
