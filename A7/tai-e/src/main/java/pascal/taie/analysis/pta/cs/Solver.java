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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt))
                    , heapModel.getObj(stmt));
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar csLVar = csManager.getCSVar(context, stmt.getLValue());
            CSVar csRVar = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(csRVar, csLVar);
            return null;
        }

        /**
         * y = T.f, build PFG: c:y <- T.f
         */
        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                CSVar csLVar = csManager.getCSVar(context, stmt.getLValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = csManager.getStaticField(field);
                addPFGEdge(staticField, csLVar);
            }
            return null;
        }

        /**
         * T.f = y, build PFG: T.f <- c:y
         */
        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                CSVar csRVar = csManager.getCSVar(context, stmt.getRValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = csManager.getStaticField(field);
                addPFGEdge(csRVar, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod m = stmt.getMethodRef().resolve();
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context targetContext = contextSelector.selectContext(csCallSite, m);
                CSMethod csTargetMethod = csManager.getCSMethod(targetContext, m);
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt)
                        , csCallSite
                        , csTargetMethod))) {
                    addReachable(csTargetMethod);

                    List<Var> parameters = m.getIR().getParams();
                    int i = 0;
                    for (Var param : parameters) {
                        Var realParam = stmt.getInvokeExp().getArg(i);
                        CSVar ca = csManager.getCSVar(context, realParam);
                        CSVar targetParam = csManager.getCSVar(targetContext, param);
                        addPFGEdge(ca, targetParam);
                        i++;
                    }
                    List<Var> retVars = m.getIR().getReturnVars();
                    Var r = stmt.getLValue();
                    if (null != r) {
                        CSVar rCSVar = csManager.getCSVar(context, r);
                        for (Var ret : retVars) {
                            CSVar retVar = csManager.getCSVar(targetContext, ret);
                            addPFGEdge(retVar, rCSVar);
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
            if (entry.pointer() instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                for (CSObj obj : diffSet.getObjects()) {
                    // x.f = y
                    for (StoreField storeField : var.getStoreFields()) {
                        CSVar rVal = csManager.getCSVar(context, storeField.getRValue());
                        InstanceField instanceField = csManager.getInstanceField(obj, storeField.getFieldRef().resolve());
                        addPFGEdge(rVal, instanceField);
                    }
                    // y = x.f
                    for (LoadField loadField : var.getLoadFields()) {
                        CSVar lVar = csManager.getCSVar(context, loadField.getLValue());
                        InstanceField instanceField = csManager.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(instanceField, lVar);
                    }
                    // x[*] = y
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        CSVar rVal = csManager.getCSVar(context, storeArray.getRValue());
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(rVal, arrayIndex);
                    }
                    // y = x[*]
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        CSVar lVar = csManager.getCSVar(context, loadArray.getLValue());
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, lVar);
                    }
                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diffSet = PointsToSetFactory.make();
        PointsToSet pt = pointer.getPointsToSet();
        for (CSObj obj : pointsToSet.getObjects()) {
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        Var var = recv.getVar();
        List<Invoke> invokes = var.getInvokes();
        for (Invoke invoke : invokes) {
            JMethod m = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context targetContext = contextSelector.selectContext(csCallSite, recvObj, m);
            CSVar csMThis = csManager.getCSVar(targetContext, m.getIR().getThis());
            workList.addEntry(csMThis, PointsToSetFactory.make(recvObj));

            CSMethod csTargetMethod = csManager.getCSMethod(targetContext, m);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke)
                    , csCallSite
                    , csTargetMethod))) {
                addReachable(csTargetMethod);
                List<Var> parameters = m.getIR().getParams();
                int i = 0;
                for (Var param : parameters) {
                    Var realParam = invoke.getInvokeExp().getArg(i);
                    CSVar ca = csManager.getCSVar(recv.getContext(), realParam);
                    CSVar targetParam = csManager.getCSVar(targetContext, param);
                    addPFGEdge(ca, targetParam);
                    i++;
                }
                List<Var> retVars = m.getIR().getReturnVars();
                Var r = invoke.getLValue();
                if (null != r) {
                    CSVar rCSVar = csManager.getCSVar(recv.getContext(), r);
                    for (Var ret : retVars) {
                        CSVar retVar = csManager.getCSVar(targetContext, ret);
                        addPFGEdge(retVar, rCSVar);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
