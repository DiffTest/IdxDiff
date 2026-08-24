package idxdiff.mariadb.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import idxdiff.Randomly;

public enum MariaDBFunctionName {

    // === Original functions ===
    BITCOUNT("BIT_COUNT", 1), LENGTH("LENGTH", 1), LENGTHB("LENGTHB", 1), LOCATE1("LOCATE", 2), LOCATE2("LOCATE", 3),
    ORD("ORD", 1), TRIM("TRIM", 1), UNCOMPRESSED_LENGTH("UNCOMPRESSED_LENGTH", 1),

    // === Math functions ===
    ABS("ABS", 1), CEIL("CEIL", 1), FLOOR("FLOOR", 1), ROUND1("ROUND", 1), ROUND2("ROUND", 2),
    TRUNCATE("TRUNCATE", 2), MOD("MOD", 2), POWER("POWER", 2), SQRT("SQRT", 1), SIGN("SIGN", 1),
    LOG("LOG", 1), LN("LN", 1), EXP("EXP", 1), CRC32("CRC32", 1),

    // === String functions ===
    CONCAT("CONCAT", 2, FunctionAttribute.VARIADIC), CONCAT_WS("CONCAT_WS", 3, FunctionAttribute.VARIADIC),
    SUBSTRING("SUBSTRING", 3), UPPER("UPPER", 1), LOWER("LOWER", 1), LTRIM("LTRIM", 1), RTRIM("RTRIM", 1),
    CHAR_LENGTH("CHAR_LENGTH", 1), REPLACE("REPLACE", 3), REVERSE("REVERSE", 1),
    LEFT("LEFT", 2), RIGHT("RIGHT", 2), LPAD("LPAD", 3), RPAD("RPAD", 3), REPEAT("REPEAT", 2),
    SPACE("SPACE", 1), STRCMP("STRCMP", 2), HEX("HEX", 1), UNHEX("UNHEX", 1),

    // === Date/Time functions ===
    YEAR("YEAR", 1), MONTH("MONTH", 1), DAY("DAY", 1), HOUR("HOUR", 1), MINUTE("MINUTE", 1), SECOND("SECOND", 1),
    DATE("DATE", 1), DAYOFMONTH("DAYOFMONTH", 1), DAYOFWEEK("DAYOFWEEK", 1), DAYOFYEAR("DAYOFYEAR", 1),
    MONTHNAME("MONTHNAME", 1), DAYNAME("DAYNAME", 1),

    // === Control flow functions ===
    IF("IF", 3), IFNULL("IFNULL", 2), NULLIF("NULLIF", 2),
    COALESCE("COALESCE", 2, FunctionAttribute.VARIADIC),

    // === Aggregate functions (for expression context) ===
    MIN("MIN", 1), MAX("MAX", 1), SUM("SUM", 1), AVG("AVG", 1),
    COUNT("COUNT", 1), GROUP_CONCAT("GROUP_CONCAT", 1),

    // === Informational functions ===
    VERSION("VERSION", 0), DATABASE("DATABASE", 0), USER("USER", 0),

    // === Encryption/Hash functions ===
    MD5("MD5", 1), SHA1("SHA1", 1), SHA2("SHA2", 2),

    // === Bit functions ===
    BIT_AND("BIT_AND", 1), BIT_OR("BIT_OR", 1), BIT_XOR("BIT_XOR", 1),

    // === Type conversion ===
    CAST_SIGNED("CAST_SIGNED", 1), CAST_UNSIGNED("CAST_UNSIGNED", 1),

    // === String/Comparison ===
    GREATEST("GREATEST", 2, FunctionAttribute.VARIADIC), LEAST("LEAST", 2, FunctionAttribute.VARIADIC),
    INET_NTOA("INET_NTOA", 1), INET_ATON("INET_ATON", 1),
    INET6_NTOA("INET6_NTOA", 1), INET6_ATON("INET6_ATON", 1);

    String functionName;
    private List<FunctionAttribute> functionAttributes;
    private int nrArgs;

    MariaDBFunctionName(String functionName, int nrArgs, FunctionAttribute... functionAttributes) {
        this.functionName = functionName;
        this.nrArgs = nrArgs;
        this.functionAttributes = new ArrayList<>(Arrays.asList(functionAttributes));
    }

    enum FunctionAttribute {
        VARIADIC
    };

    public String getFunctionName() {
        return functionName;
    }

    public int getNrArgs() {
        return nrArgs;
    }

    public List<FunctionAttribute> getFunctionAttributes() {
        return functionAttributes;
    }

    public boolean isVariadic() {
        return functionAttributes.stream().anyMatch(p -> p == FunctionAttribute.VARIADIC);
    }

    public static MariaDBFunctionName getRandom() {
        return Randomly.fromOptions(MariaDBFunctionName.values());
    }
}