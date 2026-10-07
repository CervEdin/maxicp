/*
 * MaxiCP is under MIT License
 * Copyright (c)  2024 UCLouvain
 *
 */

package org.maxicp.cp.engine.constraints.scheduling;

import org.maxicp.cp.engine.core.AbstractCPConstraint;
import org.maxicp.cp.engine.core.CPBoolVar;
import org.maxicp.cp.engine.core.CPIntervalVar;
import org.maxicp.state.datastructures.StateSparseSet;
import org.maxicp.util.exception.InconsistencyException;

import java.util.ArrayList;

/**
 * Bound Consistency filtering for the NoOverlap constraint
 *
 * @author Pierre Schaus
 */
public class NoOverlapBC extends AbstractCPConstraint {

    final CPIntervalVar[] vars;
    private CPBoolVar[] precedences;

    public NoOverlapBC(CPIntervalVar... vars) {
        super(vars[0].getSolver());
        this.vars = vars;
    }

    @Override
    public void post() {
        ArrayList<CPBoolVar> precedences = new ArrayList<>();

        for (int i = 0; i < vars.length; i++) {
            for (int j = i + 1; j < vars.length; j++) {
                NoOverlapBinary binary = new NoOverlapBinary(vars[i], vars[j]);
                getSolver().post(binary);
                precedences.add(binary.before);
            }
        }
        this.precedences = precedences.toArray(new CPBoolVar[0]);

        getSolver().post(new NoOverlapBCGlobal(vars));
    }

    /**
     * Return the precedence variables that are used to model the non-overlap constraint
     * They are n*(n-1)/2 variables where n is the number of interval variables.
     *
     * @return an array of boolean variables
     */
    public CPBoolVar[] precedenceVars() {
        return precedences;
    }
}


class NoOverlapBCGlobal extends AbstractCPConstraint {
    StateSparseSet activities;
    CPIntervalVar[] intervals;
    int[] iterator;

    int[] startMin;
    int[] endMax;
    int[] duration;
    boolean[] isOptional;

    int n;

    NoOverlapBCLeftToRight globalFilter;

    NoOverlapBCGlobal(CPIntervalVar... vars) {
        super(vars[0].getSolver());
        this.intervals = vars;
        activities = new StateSparseSet(getSolver().getStateManager(), vars.length, 0);
        iterator = new int[vars.length];
        startMin = new int[vars.length];
        endMax = new int[vars.length];
        duration = new int[vars.length];
        isOptional = new boolean[vars.length];
        globalFilter = new NoOverlapBCLeftToRight(vars.length);
    }

    private void update() {
        n = activities.fillArray(iterator);
        for (int iter = 0; iter < n; iter++) {
            CPIntervalVar act = intervals[iterator[iter]];
            if (act.isAbsent()) {
                activities.remove(iterator[iter]);
            }
        }
        filter();
        n = activities.fillArray(iterator);
        for (int iter = 0; iter < n; iter++) {
            int i = iterator[iter];
            CPIntervalVar act = intervals[i];
            startMin[iter] = act.startMin();
            endMax[iter] = act.endMax();
            duration[iter] = act.lengthMin();
            isOptional[iter] = !act.isPresent();
            assert (!act.isAbsent());
        }

    }

    private void filter() {
        // TODO
    }

    @Override
    public void post() {
        for (CPIntervalVar interval : intervals) {
            if (!interval.isAbsent()) {
                interval.propagateOnChange(this);
            }
        }
        propagate();
    }

    @Override
    public void propagate() {
        // left to right
        update();
        // set lct of optional to + infinity, so that they never restrict the other activities
        for (int i = 0; i < n; i++) {
            if (isOptional[i]) {
                endMax[i] = Integer.MAX_VALUE;
            }
        }
        NoOverlapBCLeftToRight.Outcome oc = globalFilter.filter(startMin, duration, endMax, n);
        if (oc == NoOverlapBCLeftToRight.Outcome.INCONSISTENCY) {
            throw InconsistencyException.INCONSISTENCY;
        } else if (oc == NoOverlapBCLeftToRight.Outcome.CHANGE) {
            // update startMin and endMax bounds
            // the bounds of an optional interval hold if it is present, it becomes absent if it no longer fits
            for (int i = 0; i < n; i++) {
                CPIntervalVar interval = intervals[iterator[i]];
                interval.setStartMin(globalFilter.startMin[i]);
                if (!isOptional[i]) {
                    interval.setEndMax(globalFilter.endMax[i]);
                }
            }
        }

        // right to left
        update();
        // mirror the activities
        for (int i = 0; i < n; i++) {
            int startMinOld = startMin[i];
            startMin[i] = -endMax[i];
            endMax[i] = isOptional[i] ? Integer.MAX_VALUE : -startMinOld;
        }
        oc = globalFilter.filter(startMin, duration, endMax, n);
        if (oc == NoOverlapBCLeftToRight.Outcome.INCONSISTENCY) {
            throw InconsistencyException.INCONSISTENCY;
        } else if (oc == NoOverlapBCLeftToRight.Outcome.CHANGE) {
            // update endMax variables
            for (int i = 0; i < n; i++) {
                CPIntervalVar interval = intervals[iterator[i]];
                interval.setEndMax(-globalFilter.startMin[i]);
                if (!isOptional[i]) {
                    interval.setStartMin(-globalFilter.endMax[i]);
                }
            }
        }
    }
}