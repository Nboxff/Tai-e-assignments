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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        @Override
        public Void visit(New stmt) {
            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(varPtr, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            VarPtr lValuePtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr rValuePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(rValuePtr, lValuePtr);
            return null;
        }

        /**
         * y = T.f, build PFG: y <- T.f
         */
        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                VarPtr lValuePtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField fieldPtr = pointerFlowGraph.getStaticField(field);
                addPFGEdge(fieldPtr, lValuePtr);
            }
            return null;
        }

        /**
         * T.f = y, build PFG: T.f <- y
         */
        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField fieldPtr = pointerFlowGraph.getStaticField(field);
                VarPtr rValuePtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(rValuePtr, fieldPtr);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod m = stmt.getMethodRef().resolve();
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, m))) {
                    addReachable(m);
                    List<Var> parameters = m.getIR().getParams();
                    int i = 0;
                    for (Var param : parameters) {
                        Var realParam = stmt.getInvokeExp().getArg(i);
                        VarPtr paramPtr = pointerFlowGraph.getVarPtr(param);
                        VarPtr realParamPtr = pointerFlowGraph.getVarPtr(realParam);
                        addPFGEdge(realParamPtr, paramPtr);
                        i++;
                    }
                    List<Var> retVars = m.getIR().getReturnVars();
                    Var r = stmt.getLValue();
                    if (null != r) {
                        VarPtr rPtr = pointerFlowGraph.getVarPtr(r);
                        for (Var ret : retVars) {
                            VarPtr retPtr = pointerFlowGraph.getVarPtr(ret);
                            addPFGEdge(retPtr, rPtr);
                        }
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                // Add <t, pt(s)> to WL
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet diffSet = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : diffSet.getObjects()) {
                    // x.f = y
                    for (StoreField storeField : var.getStoreFields()) {
                        VarPtr rValue = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        addPFGEdge(rValue, instanceField);
                    }
                    // y = x.f
                    for (LoadField loadField : var.getLoadFields()) {
                        VarPtr lValue = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(instanceField, lValue);
                    }
                    // x[*] = y
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        VarPtr rValue = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(rValue, arrayIndex);
                    }
                    // y = x[*]
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        VarPtr lValue = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, lValue);
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diffSet = new PointsToSet();
        PointsToSet pt = pointer.getPointsToSet();
        for (Obj obj : pointsToSet.getObjects()) {
            if (!pt.contains(obj)) {
                diffSet.addObject(obj);
                pt.addObject(obj);
            }
        }
        if (!diffSet.isEmpty()) {
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, diffSet);
            }
        }
        return diffSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        List<Invoke> invokes = var.getInvokes();
        for (Invoke invoke : invokes) {
            JMethod m = resolveCallee(recv, invoke);
            VarPtr mThis = pointerFlowGraph.getVarPtr(m.getIR().getThis());
            workList.addEntry(mThis, new PointsToSet(recv));

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m))) {
                addReachable(m);
                List<Var> parameters = m.getIR().getParams();
                int i = 0;
                for (Var param : parameters) {
                    Var realParam = invoke.getInvokeExp().getArg(i);
                    VarPtr paramPtr = pointerFlowGraph.getVarPtr(param);
                    VarPtr realParamPtr = pointerFlowGraph.getVarPtr(realParam);
                    addPFGEdge(realParamPtr, paramPtr);
                    i++;
                }
                List<Var> retVars = m.getIR().getReturnVars();
                Var r = invoke.getLValue();
                if (null != r) {
                    VarPtr rPtr = pointerFlowGraph.getVarPtr(r);
                    for (Var ret : retVars) {
                        VarPtr retPtr = pointerFlowGraph.getVarPtr(ret);
                        addPFGEdge(retPtr, rPtr);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
