package idxdiff.mariadb.ast;

import java.math.BigDecimal;

import idxdiff.Randomly;

public class MariaDBConstant implements MariaDBExpression {

    private MariaDBConstant() {
    }

    public static class MariaDBNullConstant extends MariaDBConstant {

        @Override
        public String toString() {
            return "NULL";
        }

    }

    public static class MariaDBIntConstant extends MariaDBConstant {

        private final long value;

        public MariaDBIntConstant(long value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }

        public long getValue() {
            return value;
        }

    }

    public static class MariaDBNegativeIntConstant extends MariaDBConstant {

        private final long value;

        public MariaDBNegativeIntConstant(long value) {
            this.value = value;
        }

        @Override
        public String toString() {
            return "-" + String.valueOf(value);
        }

        public long getValue() {
            return -value;
        }

    }

    public static class MariaDBDoubleConstant extends MariaDBConstant {

        private final double value;

        public MariaDBDoubleConstant(double value) {
            this.value = value;
        }

        public double getValue() {
            return value;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }

    }

    public static class MariaDBScientificConstant extends MariaDBConstant {

        private final double value;

        public MariaDBScientificConstant(double value) {
            this.value = value;
        }

        public double getValue() {
            return value;
        }

        @Override
        public String toString() {
            // Format in scientific notation
            return String.format("%.6e", value);
        }

    }

    public static class MariaDBDecimalConstant extends MariaDBConstant {

        private final BigDecimal value;

        public MariaDBDecimalConstant(BigDecimal value) {
            this.value = value;
        }

        public BigDecimal getValue() {
            return value;
        }

        @Override
        public String toString() {
            return value.toPlainString();
        }

    }

    public static class MariaDBTextConstant extends MariaDBConstant {

        private final String value;

        public MariaDBTextConstant(String value) {
            this.value = value;
        }

        public String getValue() {
            return value;
        }

        @Override
        public String toString() {
            return "'" + value.replace("'", "''").replace("\\", "\\\\") + "'";
        }

    }

    public static class MariaDBEmptyStringConstant extends MariaDBConstant {

        @Override
        public String toString() {
            return "''";
        }

    }

    public static class MariaDBBooleanConstant extends MariaDBConstant {

        private final boolean value;

        public MariaDBBooleanConstant(boolean value) {
            this.value = value;
        }

        public boolean getValue() {
            return value;
        }

        @Override
        public String toString() {
            return String.valueOf(value);
        }

    }

    public static class MariaDBHexConstant extends MariaDBConstant {

        private final String hexValue;

        public MariaDBHexConstant(String hexValue) {
            this.hexValue = hexValue;
        }

        @Override
        public String toString() {
            return "0x" + hexValue;
        }

        public String getHexValue() {
            return hexValue;
        }

    }

    public static class MariaDBBitConstant extends MariaDBConstant {

        private final String bitValue;

        public MariaDBBitConstant(String bitValue) {
            this.bitValue = bitValue;
        }

        @Override
        public String toString() {
            return "b'" + bitValue + "'";
        }

        public String getBitValue() {
            return bitValue;
        }

    }

    public static class MariaDBDateConstant extends MariaDBConstant {

        private final String dateValue;

        public MariaDBDateConstant(String dateValue) {
            this.dateValue = dateValue;
        }

        @Override
        public String toString() {
            return "'" + dateValue + "'";
        }

        public String getDateValue() {
            return dateValue;
        }

    }

    public static class MariaDBTimestampConstant extends MariaDBConstant {

        private final String timestampValue;

        public MariaDBTimestampConstant(String timestampValue) {
            this.timestampValue = timestampValue;
        }

        @Override
        public String toString() {
            return "'" + timestampValue + "'";
        }

        public String getTimestampValue() {
            return timestampValue;
        }

    }

    public static MariaDBTextConstant createTextConstant(String text) {
        return new MariaDBTextConstant(text);
    }

    public static MariaDBIntConstant createIntConstant(long val) {
        return new MariaDBIntConstant(val);
    }

    public static MariaDBNullConstant createNullConstant() {
        return new MariaDBNullConstant();
    }

    public static MariaDBConstant createBooleanConstant(boolean val) {
        return new MariaDBBooleanConstant(val);
    }

    public static MariaDBConstant createNegativeIntConstant(long val) {
        return new MariaDBNegativeIntConstant(val);
    }

    public static MariaDBConstant createScientificConstant(double val) {
        return new MariaDBScientificConstant(val);
    }

    public static MariaDBConstant createDecimalConstant(BigDecimal val) {
        return new MariaDBDecimalConstant(val);
    }

    public static MariaDBConstant createEmptyStringConstant() {
        return new MariaDBEmptyStringConstant();
    }

    public static MariaDBConstant createHexConstant(String hex) {
        return new MariaDBHexConstant(hex);
    }

    public static MariaDBConstant createBitConstant(String bits) {
        return new MariaDBBitConstant(bits);
    }

    public static MariaDBConstant createDateConstant(String date) {
        return new MariaDBDateConstant(date);
    }

    public static MariaDBConstant createTimestampConstant(String ts) {
        return new MariaDBTimestampConstant(ts);
    }

    /**
     * Generate a random constant with enhanced type coverage.
     */
    public static MariaDBConstant getRandomConstantValue(Randomly r) {
        if (Randomly.getBooleanWithSmallProbability()) {
            return createNullConstant();
        }
        int choice = r.getInteger(0, 14);
        switch (choice) {
        case 0:
        case 1:
        case 2:
            return createIntConstant(r.getInteger());
        case 3:
            return createNegativeIntConstant(Math.abs(r.getInteger()) + 1);
        case 4:
            double d;
            do {
                d = r.getDouble();
            } while (Double.isInfinite(d) || Double.isNaN(d));
            return new MariaDBDoubleConstant(d);
        case 5:
            return createTextConstant(r.getString());
        case 6:
            return createBooleanConstant(Randomly.getBoolean());
        case 7:
            return createEmptyStringConstant();
        case 8:
            // Hex constant
            return createHexConstant(randomHexString(r));
        case 9:
            // Bit constant
            return createBitConstant(randomBitString(r));
        case 10:
            // Scientific notation
            double sd;
            do {
                sd = r.getDouble();
            } while (Double.isInfinite(sd) || Double.isNaN(sd));
            return createScientificConstant(sd);
        case 11:
            // Decimal constant
            return createDecimalConstant(randomBigDecimal(r));
        case 12:
            // Date constant
            return createDateConstant(randomDate(r));
        case 13:
            // Timestamp constant
            return createTimestampConstant(randomTimestamp(r));
        default:
            return createIntConstant(r.getInteger());
        }
    }

    private static String randomHexString(Randomly r) {
        int len = r.getInteger(1, 9);
        StringBuilder sb = new StringBuilder();
        String hexChars = "0123456789ABCDEF";
        for (int i = 0; i < len; i++) {
            sb.append(hexChars.charAt(r.getInteger(0, hexChars.length())));
        }
        return sb.toString();
    }

    private static String randomBitString(Randomly r) {
        int len = r.getInteger(1, 9);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < len; i++) {
            sb.append(r.getInteger(0, 2));
        }
        return sb.toString();
    }

    private static BigDecimal randomBigDecimal(Randomly r) {
        return BigDecimal.valueOf(r.getDouble()).setScale(r.getInteger(0, 6), BigDecimal.ROUND_HALF_UP);
    }

    private static String randomDate(Randomly r) {
        int year = r.getInteger(1970, 2038);
        int month = r.getInteger(1, 13);
        int day = r.getInteger(1, 29);
        return String.format("%04d-%02d-%02d", year, month, day);
    }

    private static String randomTimestamp(Randomly r) {
        return randomDate(r) + String.format(" %02d:%02d:%02d", r.getInteger(0, 24), r.getInteger(0, 60),
                r.getInteger(0, 60));
    }

}