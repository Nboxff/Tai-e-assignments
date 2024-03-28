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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import javax.print.attribute.standard.PresentationDirection;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    /**
     * 判断两个变量是否是别名关系
     * 若 pts(x) ∩ pts(y) != empty, 则变量x, y为别名
     */
    private boolean isAliasVar(Var x, Var y) {
        Set<Obj> ptsX = pta.getPointsToSet(x);
        Set<Obj> ptsY = pta.getPointsToSet(y);
        for (Obj obj : ptsX) {
            if (ptsY.contains(obj)) {
                return true;
            }
        }
        return false;
    }

    /**
     * 变量x的别名，包含x
     */
    private List<Var> getAliasVars(Var x) {
        List<Var> aliasVars = new ArrayList<>();
        for (Var var : pta.getVars()) {
            if (isAliasVar(x, var)) {
                aliasVars.add(var);
            }
        }
        return aliasVars;
    }

    private boolean isArrayAccessAlias(Var index1, Var index2, CPFact fact1, CPFact fact2) {
        Value v1 = fact1.get(index1);
        Value v2 = fact2.get(index2);
        if (v1.isUndef() || v2.isUndef()) {
            return false;
        }

        if (v1.isNAC() || v2.isNAC()) {
            return true;
        }

        assert v1.isConstant() && v2.isConstant();
        return v1.getConstant() == v2.getConstant();
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        TransferStmtVisitor transferStmtVisitor = new TransferStmtVisitor(in, out);
        return stmt.accept(transferStmtVisitor);
    }

    private class TransferStmtVisitor implements StmtVisitor<Boolean> {
        private final CPFact in;

        private final CPFact out;

        private TransferStmtVisitor(CPFact in, CPFact out) {
            this.in = in;
            this.out = out;
        }

        /**
         * x = a.f
         */
        @Override
        public Boolean visit(LoadField stmt) {
            Var lValue = stmt.getLValue();
            Value res = Value.getUndef();
            if (!ConstantPropagation.canHoldInt(lValue)) {
                out.clear();
                out.copyFrom(in);
                return false;
            }

            // 分析实例字段
            if (!stmt.isStatic()) {
                Var base = null;
                FieldAccess fieldAccess = stmt.getFieldAccess();
                if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                    base = instanceFieldAccess.getBase();
                }
                JField field = stmt.getFieldRef().resolve();
                List<Var> aliasVars = getAliasVars(base);
                for (Var var : aliasVars) {
                    List<StoreField> storeFields = var.getStoreFields();
                    for (StoreField storeField : storeFields) {
                        if (storeField.getFieldRef().resolve().equals(field)) {
                            Var rValue = storeField.getRValue();
                            res = cp.meetValue(res, solver.getInFact(storeField).get(rValue));
                        }
                    }
                }
            }

            // 分析静态字段
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Type type = stmt.getFieldAccess().getType();
                for (Stmt node : icfg.getNodes()) {
                    if (node instanceof StoreField storeField
                            && storeField.isStatic()
                            && storeField.getFieldRef().resolve().equals(field)) {

                        Var rValue = storeField.getRValue();
                        res = cp.meetValue(res, solver.getInFact(storeField).get(rValue));
                    }
                }
            }

            CPFact newOut = in.copy();
            newOut.update(lValue, res);

            if (!newOut.equals(out)) {
                out.clear();
                out.copyFrom(newOut);
                return true;
            }
            return false;
        }

        @Override
        public Boolean visit(LoadArray stmt) {
            Var lValue = stmt.getLValue();
            Value res = Value.getUndef();
            if (!ConstantPropagation.canHoldInt(lValue)) {
                out.clear();
                out.copyFrom(in);
                return false;
            }
            Var base = stmt.getArrayAccess().getBase();
            Var index = stmt.getArrayAccess().getIndex();

            List<Var> aliasVars = getAliasVars(base);
            for (Var var : aliasVars) {
                List<StoreArray> storeArrays = var.getStoreArrays();
                for (StoreArray storeArray : storeArrays) {
                    Var storeIndex = storeArray.getArrayAccess().getIndex();
                    if (isArrayAccessAlias(index, storeIndex, in, solver.getInFact(storeArray))) {
                        Var rValue = storeArray.getRValue();
                        res = cp.meetValue(res, solver.getInFact(storeArray).get(rValue));
                    }
                }
            }

            CPFact newOut = in.copy();
            newOut.update(lValue, res);

            if (!newOut.equals(out)) {
                out.clear();
                out.copyFrom(newOut);
                return true;
            }
            return false;
        }

        /**
         * a.f = x
         */
        @Override
        public Boolean visit(StoreField stmt) {
            Var RValue = stmt.getRValue();
            if (!ConstantPropagation.canHoldInt(RValue)) {
                return StmtVisitor.super.visit(stmt);
            }

            // 分析实例字段
            if (!stmt.isStatic()) {
                Var base = null;
                FieldAccess fieldAccess = stmt.getFieldAccess();
                if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                    base = instanceFieldAccess.getBase();
                }
                JField field = stmt.getFieldRef().resolve();
                List<Var> aliasVars = getAliasVars(base);
                for (Var var : aliasVars) {
                    List<LoadField> loadFields = var.getLoadFields();
                    for (LoadField loadField : loadFields) {
                        if (loadField.getFieldRef().resolve().equals(field)) {
                            solver.addToWorkList(loadField);
                        }
                    }
                }
            }

            // 分析静态字段
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Type type = stmt.getFieldAccess().getType();
                for (Stmt node : icfg.getNodes()) {
                    if (node instanceof LoadField loadField
                            && loadField.isStatic()
                            && loadField.getFieldRef().resolve().equals(field)) {

                        solver.addToWorkList(loadField);
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Boolean visit(StoreArray stmt) {
            Var base = stmt.getArrayAccess().getBase();
            Var index = stmt.getArrayAccess().getIndex();

            List<Var> aliasVars = getAliasVars(base);
            for (Var var : aliasVars) {
                List<LoadArray> loadArrays = var.getLoadArrays();
                for (LoadArray loadArray : loadArrays) {
                    Var storeIndex = loadArray.getArrayAccess().getIndex();
                    if (isArrayAccessAlias(index, storeIndex, in, solver.getInFact(loadArray))) {
                        solver.addToWorkList(loadArray);
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Boolean visitDefault(Stmt stmt) {
            return cp.transferNode(stmt, in, out);
        }

    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact result = out.copy();
        Stmt sourceStmt = edge.getSource();
        if (sourceStmt.getDef().isEmpty()) {
            return result;
        }
        if (sourceStmt.getDef().get() instanceof Var def) {
            result.update(def, Value.getUndef());
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact result = new CPFact();
        JMethod jMethod = edge.getCallee();
        List<Var> params = jMethod.getIR().getParams();
        if (edge.getSource() instanceof Invoke invoke) {
            InvokeExp invokeExp = invoke.getInvokeExp();
            int i = 0;
            for (Var param : params) {
                result.update(param, callSiteOut.get(invokeExp.getArg(i)));
                i++;
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact result = new CPFact();
        Stmt callSite = edge.getCallSite();
        if (callSite.getDef().isEmpty()) {
            return result; // return an empty fact
        }

        if (callSite.getDef().get() instanceof Var def) {
            Collection<Var> returnVars = edge.getReturnVars();
            Value fact = Value.getUndef();
            for (Var var : returnVars) {
                fact = cp.meetValue(fact, returnOut.get(var));
            }
            result.update(def, fact);
        }
        return result;
    }
}
