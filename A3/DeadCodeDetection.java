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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // Your task is to recognize dead code in ir and add it to deadCode

        // BFS to detect control-flow unreachable code
        Queue<Stmt> queue = new LinkedList<>();
        Map<Stmt, Boolean> visited = new HashMap<>();
        for (Stmt stmt : cfg) {
            visited.put(stmt, false);
        }

        queue.add(cfg.getEntry());
        visited.put(cfg.getEntry(), true);

        while (!queue.isEmpty()) {
            Stmt nowStmt = queue.poll();
            visited.put(nowStmt, true);

            if (nowStmt instanceof AssignStmt<?,?> assignStmt) {
                LValue lValue = assignStmt.getLValue();
                RValue rValue = assignStmt.getRValue();
                if (lValue instanceof Var lVar) {
                    if (hasNoSideEffect(rValue) && !liveVars.getOutFact(nowStmt).contains(lVar)) {
                        deadCode.add(nowStmt);
                    }
                }
            }

            for (Edge<Stmt> edge : cfg.getOutEdgesOf(nowStmt)) {
                Stmt nextStmt = edge.getTarget();
                if (visited.get(nextStmt)) continue;

                if (nowStmt instanceof If ifStmt) {
                    ConditionExp conditionExp = ifStmt.getCondition();
                    Value conditionVal = ConstantPropagation.evaluate(conditionExp, constants.getInFact(nowStmt));
                    if (conditionVal.isConstant()) {
                        int conditionInt = conditionVal.getConstant();
                        if (conditionInt == 1 && edge.getKind() == Edge.Kind.IF_FALSE)
                            continue;
                        if (conditionInt == 0 && edge.getKind() == Edge.Kind.IF_TRUE)
                            continue;
                    }
                }

                if (nowStmt instanceof SwitchStmt switchStmt) {
                    Var var = switchStmt.getVar();
                    Value holdValue = ConstantPropagation.evaluate(var, constants.getInFact(nowStmt));
                    if (holdValue.isConstant()) {
                        int holdInt = holdValue.getConstant();
                        if (edge.isSwitchCase()) {
                            int caseValue = edge.getCaseValue();
                            if (holdInt != caseValue) continue;
                        }
                        if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            if (switchStmt.getCaseValues().contains(holdInt)) continue;
                        }
                    }
                }
                queue.add(nextStmt);
            }
        }

        for (Stmt stmt : cfg) {
            if (!visited.get(stmt) && stmt != cfg.getEntry() && stmt != cfg.getExit()) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
