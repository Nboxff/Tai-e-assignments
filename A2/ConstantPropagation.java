/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import org.checkerframework.checker.units.qual.C;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact boundCPFact = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        for (Var param : params) {
            if (canHoldInt(param)) {
                boundCPFact.update(param, Value.getNAC());
            }
        }
        return boundCPFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> factVars = fact.keySet();
        for (Var factVar : factVars) {
            Value meetVal = meetValue(fact.get(factVar), target.get(factVar));
            target.update(factVar, meetVal);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {

        // Case1: NAC meet v
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        // Case2: UNDEF meet v
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }

        // Case3: c meet c, Case4: c1 meet c2
        assert v1.isConstant() && v2.isConstant();
        if (v1.getConstant() == v2.getConstant()) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact newOut = in.copy();
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            if (definitionStmt.getLValue() instanceof Var def) {
                Exp exp = definitionStmt.getRValue();
                if (canHoldInt(def)) {
                    newOut.update(def, evaluate(exp, in));
                }
            }

        }
        boolean haveChanges = !newOut.equals(out);
        out.clear();
        out.copyFrom(newOut);
        return haveChanges;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        Value genValue;
        if (exp == null) {
            return Value.getNAC();
        }
        if (exp instanceof IntLiteral intLiteral) {
            genValue = Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof Var varExp) {
            // Ignore varExp is not INT type
            if (!canHoldInt(varExp)) {
                return Value.getNAC();
            }
            genValue = in.get(varExp);
        } else if (exp instanceof BinaryExp binaryExp) {
            Var operand1 = binaryExp.getOperand1();
            Var operand2 = binaryExp.getOperand2();
            Value val1 = in.get(operand1);
            Value val2 = in.get(operand2);
            if (!canHoldInt(operand1) || !canHoldInt(operand2)) {
                genValue = Value.getNAC();
            } else if (val1.isConstant() && val2.isConstant()) {
                genValue = calculate(binaryExp, val1.getConstant(), val2.getConstant());
            } else if (val1.isNAC() || val2.isNAC()) {
                genValue = Value.getNAC();
                // NAC / 0 or NAC % 0
                if (val1.isNAC() && val2.isConstant() && binaryExp instanceof ArithmeticExp arithmeticExp) {
                    ArithmeticExp.Op op = arithmeticExp.getOperator();
                    if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM && val2.getConstant() == 0) {
                        genValue = Value.getUndef();
                    }
                }
            } else {
                genValue = Value.getUndef();
            }
        } else {
            // Other type like load
            genValue = Value.getNAC();
        }
        return genValue;
    }

    private static Value calculate(BinaryExp binaryExp, int value1, int value2) {
        if (binaryExp instanceof ArithmeticExp arithmeticExp) {
            ArithmeticExp.Op op = arithmeticExp.getOperator();
            switch (op) {
                case ADD:
                    return Value.makeConstant(value1 + value2);
                case SUB:
                    return Value.makeConstant(value1 - value2);
                case MUL:
                    return Value.makeConstant(value1 * value2);
                case DIV:
                    if (value2 == 0) {
                        return Value.getUndef();
                    }
                    return Value.makeConstant(value1 / value2);
                case REM:
                    if (value2 == 0) {
                        return Value.getUndef();
                    }
                    return Value.makeConstant(value1 % value2);
            }
        } else if (binaryExp instanceof ConditionExp conditionExp) {
            ConditionExp.Op op = conditionExp.getOperator();
            return switch (op) {
                case EQ -> Value.makeConstant(value1 == value2 ? 1 : 0);
                case GE -> Value.makeConstant(value1 >= value2 ? 1 : 0);
                case GT -> Value.makeConstant(value1 > value2 ? 1 : 0);
                case LE -> Value.makeConstant(value1 <= value2 ? 1 : 0);
                case LT -> Value.makeConstant(value1 < value2 ? 1 : 0);
                case NE -> Value.makeConstant(value1 != value2 ? 1 : 0);
            };
        } else if (binaryExp instanceof ShiftExp shiftExp) {
            ShiftExp.Op op = shiftExp.getOperator();
            return switch (op) {
                case SHL -> Value.makeConstant(value1 << value2);
                case SHR -> Value.makeConstant(value1 >> value2);
                case USHR -> Value.makeConstant(value1 >>> value2);
            };
        } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
            BitwiseExp.Op op = bitwiseExp.getOperator();
            return switch (op) {
                case OR -> Value.makeConstant(value1 | value2);
                case AND -> Value.makeConstant(value1 & value2);
                case XOR -> Value.makeConstant(value1 ^ value2);
            };
        } else {
            return Value.getNAC();
        }
        return null;
    }

}
