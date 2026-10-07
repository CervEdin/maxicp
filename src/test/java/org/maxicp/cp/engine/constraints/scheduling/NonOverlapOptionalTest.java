/*
 * MaxiCP is under MIT License
 * Copyright (c)  2024 UCLouvain
 *
 */

package org.maxicp.cp.engine.constraints.scheduling;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.maxicp.cp.engine.core.CPConstraint;
import org.maxicp.cp.engine.core.CPIntervalVar;
import org.maxicp.cp.engine.core.CPSolver;
import org.maxicp.search.DFSearch;
import org.maxicp.util.exception.InconsistencyException;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;
import java.util.function.Function;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.*;
import static org.maxicp.cp.CPFactory.*;
import static org.maxicp.search.Searches.*;

/**
 * Differential tests of the no-overlap constraints with optional intervals:
 * the set of solutions must be the same as the one of the pairwise decomposition.
 */
class NonOverlapOptionalTest {

    private static final int PRESENT = 0, OPTIONAL = 1, ABSENT = 2;
    private static final int MAX_SOLUTIONS = 50000;

    enum Filter {
        NO_OVERLAP(NoOverlap::new),
        NO_OVERLAP_BC(NoOverlapBC::new),
        // the global filtering alone, without the binary constraints that could hide its mistakes
        NO_OVERLAP_GLOBAL(NoOverlapGlobal::new),
        NO_OVERLAP_BC_GLOBAL(NoOverlapBCGlobal::new);

        final Function<CPIntervalVar[], CPConstraint> make;

        Filter(Function<CPIntervalVar[], CPConstraint> make) {
            this.make = make;
        }
    }

    record Instance(int[] startMin, int[] startMax, int[] lengthMin, int[] lengthMax, int[] endMax, int[] status) {
        int n() {
            return startMin.length;
        }

        @Override
        public String toString() {
            StringJoiner joiner = new StringJoiner("\n");
            for (int i = 0; i < n(); i++) {
                joiner.add(String.format("a%d start=[%d,%d] length=[%d,%d] endMax=%d %s", i,
                        startMin[i], startMax[i], lengthMin[i], lengthMax[i], endMax[i],
                        new String[]{"present", "optional", "absent"}[status[i]]));
            }
            return joiner.toString();
        }
    }

    /**
     * Random small instance with a different, tight time window per interval.
     * About 40% of the intervals are present, 50% optional and 10% absent.
     */
    static Instance randomInstance(Random r, int maxN, int width, int spread, int offset) {
        int n = 2 + r.nextInt(maxN - 1);
        int[] startMin = new int[n], startMax = new int[n], lengthMin = new int[n], lengthMax = new int[n];
        int[] endMax = new int[n], status = new int[n];
        for (int i = 0; i < n; i++) {
            startMin[i] = offset + r.nextInt(spread);
            startMax[i] = startMin[i] + r.nextInt(width);
            lengthMin[i] = 1 + r.nextInt(6);
            lengthMax[i] = r.nextInt(3) == 0 ? lengthMin[i] + r.nextInt(3) : lengthMin[i];
            int slack = startMax[i] - startMin[i] + lengthMax[i] - lengthMin[i];
            endMax[i] = startMin[i] + lengthMin[i] + r.nextInt(slack + 1);
            int s = r.nextInt(10);
            status[i] = s < 4 ? PRESENT : s < 9 ? OPTIONAL : ABSENT;
        }
        return new Instance(startMin, startMax, lengthMin, lengthMax, endMax, status);
    }

    private static CPIntervalVar[] makeIntervals(CPSolver cp, Instance inst) {
        CPIntervalVar[] intervals = new CPIntervalVar[inst.n()];
        for (int i = 0; i < inst.n(); i++) {
            intervals[i] = makeIntervalVar(cp);
            intervals[i].setStartMin(inst.startMin[i]);
            intervals[i].setStartMax(inst.startMax[i]);
            intervals[i].setLengthMin(inst.lengthMin[i]);
            intervals[i].setLengthMax(inst.lengthMax[i]);
            intervals[i].setEndMax(inst.endMax[i]);
            if (inst.status[i] == PRESENT) intervals[i].setPresent();
            if (inst.status[i] == ABSENT) intervals[i].setAbsent();
        }
        return intervals;
    }

    /**
     * Branches on the status, then on the start, then on the length of the present intervals,
     * so that every leaf fixes all the intervals.
     */
    private static Supplier<Runnable[]> fixAll(CPSolver cp, CPIntervalVar[] intervals) {
        Supplier<Runnable[]> lengths = () -> {
            for (CPIntervalVar var : intervals) {
                if (var.isPresent() && var.lengthMin() != var.lengthMax()) {
                    int length = var.lengthMin();
                    return branch(() -> {
                        var.setLength(length);
                        cp.fixPoint();
                    }, () -> {
                        var.setLengthMin(length + 1);
                        cp.fixPoint();
                    });
                }
            }
            return EMPTY;
        };
        return and(branchOnStatus(intervals), branchOnPresentStarts(intervals), lengths);
    }

    private static boolean isValid(int[] start, int[] end, boolean[] present) {
        for (int i = 0; i < start.length; i++) {
            for (int j = i + 1; j < start.length; j++) {
                if (present[i] && present[j] && start[i] < end[j] && start[j] < end[i]) return false;
            }
        }
        return true;
    }

    /**
     * Enumerates the solutions of the instance, with the given filter or, if it is null, with the decomposition.
     *
     * @return the solutions, encoded as strings, or null if there are too many
     */
    static Set<String> solutions(Instance inst, Filter filter) {
        CPSolver cp = makeSolver();
        CPIntervalVar[] intervals = makeIntervals(cp, inst);
        Set<String> solutions = new HashSet<>();
        try {
            if (filter == null) {
                NonOverlapTest.postDecomposition(intervals);
            } else {
                cp.post(filter.make.apply(intervals));
            }
        } catch (InconsistencyException e) {
            return solutions;
        }
        DFSearch dfs = makeDfs(cp, fixAll(cp, intervals));
        dfs.onSolution(() -> {
            int n = intervals.length;
            int[] start = new int[n], end = new int[n];
            boolean[] present = new boolean[n];
            StringJoiner joiner = new StringJoiner(",");
            for (int i = 0; i < n; i++) {
                CPIntervalVar var = intervals[i];
                present[i] = var.isPresent();
                if (present[i]) {
                    assertTrue(var.startMin() == var.startMax() && var.lengthMin() == var.lengthMax());
                    start[i] = var.startMin();
                    end[i] = var.endMin();
                    joiner.add(start[i] + ":" + var.lengthMin());
                } else {
                    joiner.add("-");
                }
            }
            if (filter == null) {
                assertTrue(isValid(start, end, present), "the decomposition accepts an overlap: " + joiner);
            }
            solutions.add(joiner.toString());
        });
        if (dfs.solve(s -> s.numberOfSolutions() >= MAX_SOLUTIONS).numberOfSolutions() >= MAX_SOLUTIONS) {
            return null;
        }
        return solutions;
    }

    /**
     * Compares the solutions of the filter with the ones of the decomposition on random instances.
     */
    static void assertSameSolutions(Filter filter, long seed, int nInstances, int maxN, int width, int spread, int offset) {
        Random r = new Random(seed);
        for (int it = 0; it < nInstances; it++) {
            Instance inst = randomInstance(r, maxN, width, spread, offset);
            Set<String> expected = solutions(inst, null);
            if (expected == null) continue;
            Set<String> actual = solutions(inst, filter);
            if (!expected.equals(actual)) {
                Set<String> missing = new HashSet<>(expected);
                missing.removeAll(actual);
                Set<String> extra = new HashSet<>(actual);
                extra.removeAll(expected);
                fail(String.format("%s, seed %d, instance %d:%n%s%nmissing solutions: %s%nextra solutions: %s",
                        filter, seed, it, inst, missing, extra));
            }
        }
    }

    @ParameterizedTest
    @EnumSource(Filter.class)
    public void testSameSolutionsAsDecompositionRandom(Filter filter) {
        assertSameSolutions(filter, 42, 300, 5, 10, 12, 0);
    }

    @ParameterizedTest
    @EnumSource(Filter.class)
    public void testSameSolutionsAsDecompositionRandomLarge(Filter filter) {
        assertSameSolutions(filter, 43, 30, 8, 6, 25, 0);
    }
}
