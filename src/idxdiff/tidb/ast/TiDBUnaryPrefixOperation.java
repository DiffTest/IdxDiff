package idxdiff.tidb.ast;

import idxdiff.Randomly;
import idxdiff.common.ast.BinaryOperatorNode.Operator;
import idxdiff.common.ast.UnaryOperatorNode;
import idxdiff.tidb.ast.TiDBUnaryPrefixOperation.TiDBUnaryPrefixOperator;

public class TiDBUnaryPrefixOperation extends UnaryOperatorNode<TiDBExpression, TiDBUnaryPrefixOperator>
        implements TiDBExpression {

    public enum TiDBUnaryPrefixOperator implements Operator {
        NOT("NOT"), //
        INVERSION("~"), //
        PLUS("+"), //
        MINUS("-"), //
        BINARY("BINARY"); //

        private String s;

        TiDBUnaryPrefixOperator(String s) {
            this.s = s;
        }

        public static TiDBUnaryPrefixOperator getRandom() {
            return Randomly.fromOptions(values());
        }

        @Override
        public String getTextRepresentation() {
            return s;
        }
    }

    public TiDBUnaryPrefixOperation(TiDBExpression expr, TiDBUnaryPrefixOperator op) {
        super(expr, op);
    }

    @Override
    public OperatorKind getOperatorKind() {
        return OperatorKind.PREFIX;
    }

}
