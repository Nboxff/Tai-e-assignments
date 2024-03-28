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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);
                for (Invoke cs : callGraph.callSitesIn(m).toList()) {
                    Set<JMethod> T = resolve(cs);
                    for (JMethod targetMethod : T) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, targetMethod));
                        workList.add(targetMethod);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> targetMethods = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        CallKind callKind = CallGraphs.getCallKind(callSite);

        if (callKind == CallKind.STATIC || callKind == CallKind.SPECIAL) {
            targetMethods.add(dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature()));
        }

        if (callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            JClass c = methodRef.getDeclaringClass();
            Queue<JClass> queue = new LinkedList<>();
            Map<JClass, Boolean> visited = new HashMap<>();
            queue.add(c);
            visited.put(c, true);

            if (!c.isInterface()) {
                JMethod tm = dispatch(c, methodRef.getSubsignature());
                if (tm != null && !tm.isAbstract()) {
                    targetMethods.add(tm);
                }
            }

            while (!queue.isEmpty()) {
                JClass cur = queue.poll();

                if (cur.isInterface()) {
                    for (JClass subInterface : hierarchy.getDirectSubinterfacesOf(cur)) {
                        if (visited.getOrDefault(subInterface, false))
                            continue;
                        queue.add(subInterface);
                        visited.put(subInterface, true);
                    }
                    for (JClass impClass : hierarchy.getDirectImplementorsOf(cur)) {
                        if (visited.getOrDefault(impClass, false))
                            continue;
                        queue.add(impClass);
                        visited.put(impClass, true);

                        JMethod tm = dispatch(impClass, methodRef.getSubsignature());
                        if (tm != null && !tm.isAbstract()) {
                            targetMethods.add(tm);
                        }
                    }
                } else {
                    for (JClass subClass: hierarchy.getDirectSubclassesOf(cur)) {
                        if (visited.getOrDefault(subClass, false))
                            continue;
                        queue.add(subClass);
                        visited.put(subClass, true);

                        JMethod tm = dispatch(subClass, methodRef.getSubsignature());
                        if (tm != null && !tm.isAbstract()) {
                            targetMethods.add(tm);
                        }
                    }
                }
            }
        }
        return targetMethods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null) {
            return jMethod;
        }
        if (jclass.getSuperClass() != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
