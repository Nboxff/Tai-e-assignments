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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new LinkedList<>();
        Map<Node, Boolean> inWorkList = new HashMap<>();
        for (Node node : cfg) {
            if (node == cfg.getEntry()) continue;
            workList.add(node);
            inWorkList.put(node, true);
        }

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            inWorkList.put(node, false);
            result.setInFact(node, analysis.newInitialFact());
            for (Node pre : cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pre), result.getInFact(node));
            }

            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for (Node suc : cfg.getSuccsOf(node)) {
                    if (!inWorkList.get(suc)) {
                        workList.add(suc);
                        inWorkList.put(suc, true);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new LinkedList<>();
        Map<Node, Boolean> inWorkList = new HashMap<>();
        for (Node node : cfg) {
            if (node == cfg.getExit()) continue;
            workList.add(node);
            inWorkList.put(node, true);
        }

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            inWorkList.put(node, false);
            result.setOutFact(node, analysis.newInitialFact());
            for (Node suc : cfg.getSuccsOf(node)) {
                analysis.meetInto(result.getInFact(suc), result.getOutFact(node));
            }

            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for (Node pre : cfg.getPredsOf(node)) {
                    if (!inWorkList.get(pre)) {
                        workList.add(pre);
                        inWorkList.put(pre, true);
                    }
                }
            }
        }
    }
}
