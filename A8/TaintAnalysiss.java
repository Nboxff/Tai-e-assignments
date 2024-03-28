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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private Map<JMethod, ArrayList<Integer>> sinkList;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        initSink();
    }

    public Set<Source> getSources() {
        return config.getSources();
    }

    public Set<Sink> getSinks() {
        return config.getSinks();
    }

    public Obj makeTaint(Invoke source, Type type) {
        return manager.makeTaint(source, type);
    }

    public boolean isSource(JMethod method) {
        for (Source source : config.getSources()) {
            if (source.method().equals(method)) {
                return true;
            }
        }
        return false;
    }

    public Type getSourceType(JMethod method) {
        for (Source source : config.getSources()) {
            if (source.method().equals(method)) {
                return source.type();
            }
        }
        return null;
    }

    private void initSink() {
        sinkList = new HashMap<>();
        for (Sink sink : config.getSinks()) {
            JMethod m = sink.method();
            int index = sink.index();
            if (!sinkList.containsKey(m)) {
                sinkList.put(m, new ArrayList<>());
            }
            sinkList.get(m).add(index);
        }
    }

    public boolean isSink(JMethod method, int i) {
        for (Sink sink : config.getSinks()) {
            if (sink.method().equals(method) && sink.index() == i) {
                return true;
            }
        }
        return false;
    }

    public void taintPropagate(Invoke invoke, JMethod m, CSVar recv) {
        for (TaintTransfer taintTransfer : config.getTransfers()) {
            if (m.equals(taintTransfer.method())) {
                PointsToSet taintPointsToSet = PointsToSetFactory.make();
                if (taintTransfer.from() == TaintTransfer.BASE && taintTransfer.to() == TaintTransfer.RESULT) {
                    for (CSObj csObj : recv.getPointsToSet().getObjects()) {
                        Obj obj = csObj.getObject();
                        if (manager.isTaint(obj)) {
                            Obj taint = manager.makeTaint(manager.getSourceCall(obj), taintTransfer.type());
                            CSObj csTaint = csManager.getCSObj(emptyContext, taint);
                            taintPointsToSet.addObject(csTaint);
                        }
                    }
                    Var r = invoke.getLValue();
                    if (r != null) {
                        CSVar rCSVar = csManager.getCSVar(recv.getContext(), r);
                        solver.addToWorkList(rCSVar, taintPointsToSet);
                    }
                } else {
                    int i = taintTransfer.from();
                    Var ai = invoke.getInvokeExp().getArg(i);
                    CSVar csAi = csManager.getCSVar(recv.getContext(), ai);
                    for (CSObj csObj : csAi.getPointsToSet().getObjects()) {
                        Obj obj = csObj.getObject();
                        if (manager.isTaint(obj)) {
                            System.out.println(obj);
                            Obj taint = manager.makeTaint(manager.getSourceCall(obj), taintTransfer.type());
                            CSObj csTaint = csManager.getCSObj(emptyContext, taint);
                            taintPointsToSet.addObject(csTaint);
                        }
                    }
                    if (taintTransfer.to() == TaintTransfer.BASE) {
                        solver.addToWorkList(recv, taintPointsToSet);
                    } else {
                        Var r = invoke.getLValue();
                        if (r != null) {
                            CSVar rCSVar = csManager.getCSVar(recv.getContext(), r);
                            solver.addToWorkList(rCSVar, taintPointsToSet);
                        }
                    }
                }

            }
        }
    }

    public void taintStaticPropagate(Invoke invoke, JMethod m, Context context) {
        for (TaintTransfer taintTransfer : config.getTransfers()) {
            if (m.equals(taintTransfer.method())) {
                PointsToSet taintPointsToSet = PointsToSetFactory.make();

                int i = taintTransfer.from();
                Var ai = invoke.getInvokeExp().getArg(i);
                CSVar csAi = csManager.getCSVar(context, ai);
                for (CSObj csObj : csAi.getPointsToSet().getObjects()) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        Obj taint = manager.makeTaint(manager.getSourceCall(obj), taintTransfer.type());
                        CSObj csTaint = csManager.getCSObj(emptyContext, taint);
                        taintPointsToSet.addObject(csTaint);
                    }
                }

                Var r = invoke.getLValue();
                if (r != null) {
                    CSVar rCSVar = csManager.getCSVar(context, r);
                    solver.addToWorkList(rCSVar, taintPointsToSet);
                }
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

        // You could query pointer analysis results you need via variable result.
        for (Edge<CSCallSite, CSMethod> edge : solver.getCallGraph().edges().toList()) {
            JMethod m = edge.getCallee().getMethod();
            Invoke l = edge.getCallSite().getCallSite();
            if (!sinkList.containsKey(m)) {
                continue;
            }
            for (Integer i : sinkList.get(m)) {
                Var ai = l.getInvokeExp().getArg(i);
                CSVar csAi = csManager.getCSVar(edge.getCallSite().getContext(), ai);
                for (CSObj csObj : result.getPointsToSet(csAi)) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        Invoke j = manager.getSourceCall(obj);
                        taintFlows.add(new TaintFlow(j, l, i));
                    }
                }
            }
        }
        System.err.println(taintFlows);
        return taintFlows;
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }
}
