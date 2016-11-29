package il.ac.bgu.cs.fvm.ex2;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static java.util.Arrays.asList;
import static junit.framework.TestCase.assertEquals;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.examples.ExampleCircuit;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

public class CircuitTest {

    FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

    @SuppressWarnings({ "rawtypes", "unchecked" })
	@Test
    public void test1() throws Exception {
        Circuit c = new ExampleCircuit();

        TransitionSystem ts = fvmFacadeImpl.transitionSystemFromCircuit(c);

        assertEquals(
                set(p(seq(true), seq(true)),
                    p(seq(false), seq(true)),
                    p(seq(true), seq(false)),
                    p(seq(false), seq(false))
                ), ts.getStates());

        assertEquals(
                set(p(seq(false), seq(true)),
                    p(seq(false), seq(false))
                ), ts.getInitialStates());

        assertEquals(set(
                seq(false),
                seq(true)
        ), ts.getActions());

        assertEquals(set("r", "x", "y"), ts.getAtomicPropositions());

        assertEquals(set(
                transition(p(seq(false), seq(true)), seq(true), p(seq(true), seq(true))),
                transition(p(seq(false), seq(false)), seq(true), p(seq(false), seq(true))),
                transition(p(seq(true), seq(false)), seq(true), p(seq(true), seq(true))),
                transition(p(seq(false), seq(true)), seq(false), p(seq(true), seq(false))),
                transition(p(seq(false), seq(false)), seq(false), p(seq(false), seq(false))),
                transition(p(seq(true), seq(false)), seq(false), p(seq(true), seq(false))),
                transition(p(seq(true), seq(true)), seq(true), p(seq(true), seq(true))),
                transition(p(seq(true), seq(true)), seq(false), p(seq(true), seq(false)))
        ), ts.getTransitions());

        assertEquals(
                set("r", "x", "y"),
                ts.getLabel(p(seq(true), seq(true))));

        assertEquals(
                set("x"),
                ts.getLabel(p(seq(false), seq(true))));

        assertEquals(
                set("r"),
                ts.getLabel(p(seq(true), seq(false))));

        assertEquals(
                set("y"),
                ts.getLabel(p(seq(false), seq(false))));
    }

    @SuppressWarnings("unchecked")
	@Test
    public void test2() throws Exception {
        Circuit c;
        c = new Circuit() {

            @Override
            public List<Boolean> updateRegisters(List<Boolean> registers,
                                                 List<Boolean> inputs) {
                return registers;
            }

            @Override
            public List<Boolean> computeOutputs(List<Boolean> registers,
                                                List<Boolean> inputs) {
                return inputs;
            }

            @Override
            public List<String> getInputPortNames() {
                return asList("x1", "x2");
            }

            @Override
            public List<String> getRegisterNames() {
                return asList("r1", "r2");
            }

            @Override
            public List<String> getOutputPortNames() {
                return asList("y1", "y2");
            }
        };

        TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts;
        ts = fvmFacadeImpl.transitionSystemFromCircuit(c);

        assertEquals(set(p(seq(false, false), seq(true, false)),
                         p(seq(false, false), seq(false, false)),
                         p(seq(false, false), seq(true, true)),
                         p(seq(false, false), seq(false, true))
        ), ts.getStates());

        assertEquals(set(p(seq(false, false), seq(true, false)),
                         p(seq(false, false), seq(false, false)),
                         p(seq(false, false), seq(true, true)),
                         p(seq(false, false), seq(false, true))
        ), ts.getInitialStates());

        assertEquals(set(seq(false, false),
                         seq(true, true),
                         seq(true, false),
                         seq(false, true)
        ), ts.getActions());

        assertEquals(
                set("r2", "y1", "x1", "y2", "x2", "r1"),
                ts.getAtomicPropositions());

        assertEquals(set(
                transition(
                        p(seq(false, false), seq(true, false)),
                        seq(true, true),
                        p(seq(false, false), seq(true, true))),
                transition(
                        p(seq(false, false), seq(true, false)),
                        seq(false, false),
                        p(seq(false, false), seq(false, false))),
                transition(
                        p(seq(false, false), seq(false, true)),
                        seq(false, true),
                        p(seq(false, false), seq(false, true))),
                transition(
                        p(seq(false, false), seq(true, true)),
                        seq(false, true),
                        p(seq(false, false), seq(false, true))),
                transition(
                        p(seq(false, false), seq(false, true)),
                        seq(true, false),
                        p(seq(false, false), seq(true, false))),
                transition(
                        p(seq(false, false), seq(false, false)),
                        seq(false, true),
                        p(seq(false, false), seq(false, true))),
                transition(
                        p(seq(false, false), seq(true, false)),
                        seq(false, true),
                        p(seq(false, false), seq(false, true))),
                transition(
                        p(seq(false, false), seq(false, false)),
                        seq(true, false),
                        p(seq(false, false), seq(true, false))),
                transition(
                        p(seq(false, false), seq(true, true)),
                        seq(true, false),
                        p(seq(false, false), seq(true, false))),
                transition(
                        p(seq(false, false), seq(false, true)),
                        seq(false, false),
                        p(seq(false, false), seq(false, false))),
                transition(
                        p(seq(false, false), seq(false, false)),
                        seq(true, true),
                        p(seq(false, false), seq(true, true))),
                transition(
                        p(seq(false, false), seq(true, true)),
                        seq(true, true),
                        p(seq(false, false), seq(true, true))),
                transition(
                        p(seq(false, false), seq(true, false)),
                        seq(true, false),
                        p(seq(false, false), seq(true, false))),
                transition(
                        p(seq(false, false), seq(false, true)),
                        seq(true, true),
                        p(seq(false, false), seq(true, true))),
                transition(
                        p(seq(false, false), seq(false, false)),
                        seq(false, false),
                        p(seq(false, false), seq(false, false))),
                transition(
                        p(seq(false, false), seq(true, true)),
                        seq(false, false),
                        p(seq(false, false), seq(false, false)))), ts.getTransitions());

        assertEquals(set("y1", "x1"),
                     ts.getLabel(p(seq(false, false), seq(true, false))));

        assertEquals(set(),
                     ts.getLabel(p(seq(false, false), seq(false, false))));

        assertEquals(set("y1", "x1", "y2", "x2"),
                     ts.getLabel(p(seq(false, false), seq(true, true))));

        assertEquals(set("y2", "x2"),
                     ts.getLabel(p(seq(false, false), seq(false, true))));
    }

    @SuppressWarnings("unchecked")
	@Test
    public void test3() throws Exception {
        Circuit cc;
        cc = new Circuit() {

            List<Boolean> intToBits(int b) {

                List<Boolean> flags = new LinkedList<>();
                for (int i = 0; i < 3; ++i) {
                    flags.add((b & (1 << i)) != 0);
                }
                assertEquals(flags.size(), 3);

                return flags;
            }

            int bitsToInt(List<Boolean> flags) {
                assertEquals(flags.size(), 3);
                byte b = 0;
                for (int i = 0; i < 3; ++i) {
                    if (flags.get(i)) {
                        b |= (1 << i);
                    }
                }
                return b;
            }

            @Override
            public List<Boolean> updateRegisters(List<Boolean> registers,
                                                 List<Boolean> inputs) {
                if (inputs.get(0)) {
                    int adv = bitsToInt(registers) + 1;
                    if (adv == 8) {
                        adv = 0;
                    }

                    return intToBits(adv);
                } else {
                    return registers;
                }
            }

            @Override
            public List<Boolean> computeOutputs(List<Boolean> registers,
                                                List<Boolean> inputs) {
                return registers.subList(3, 3);
            }

            @Override
            public List<String> getInputPortNames() {
                return asList("inc");
            }

            @Override
            public List<String> getRegisterNames() {
                return asList("r1", "r2", "r3");
            }

            @Override
            public List<String> getOutputPortNames() {
                return asList("odd");
            }
        };

        TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ts;
        ts = fvmFacadeImpl.transitionSystemFromCircuit(cc);

        assertEquals(set(p(seq(false, false, false), seq(true)),
                         p(seq(false, false, true), seq(false)),
                         p(seq(false, true, true), seq(true)),
                         p(seq(true, false, true), seq(true)),
                         p(seq(false, false, true), seq(true)),
                         p(seq(false, false, false), seq(false)),
                         p(seq(false, true, false), seq(true)),
                         p(seq(false, true, true), seq(false)),
                         p(seq(true, true, false), seq(false)),
                         p(seq(false, true, false), seq(false)),
                         p(seq(true, false, false), seq(false)),
                         p(seq(true, true, false), seq(true)),
                         p(seq(true, true, true), seq(false)),
                         p(seq(true, false, false), seq(true)),
                         p(seq(true, false, true), seq(false)),
                         p(seq(true, true, true), seq(true))), ts.getStates());

        assertEquals(set(p(seq(false, false, false), seq(true)),
                         p(seq(false, false, false), seq(false))), ts.getInitialStates());

        assertEquals(set(seq(false), seq(true)), ts.getActions());

        assertEquals(set("r2", "r3", "odd", "r1", "inc"), ts.getAtomicPropositions());

        assertEquals(set(
                transition(p(seq(false, false, false), seq(true)),
                           seq(true),
                           p(seq(true, false, false), seq(true))),
                transition(p(seq(false, true, false), seq(false)),
                           seq(true),
                           p(seq(false, true, false), seq(true))),
                transition(
                        p(seq(false, false, true), seq(true)),
                        seq(true),
                        p(seq(true, false, true), seq(true))),
                transition(
                        p(seq(false, true, true), seq(false)),
                        seq(true),
                        p(seq(false, true, true), seq(true))),
                transition(
                        p(seq(false, false, false), seq(false)),
                        seq(true),
                        p(seq(false, false, false), seq(true))),
                transition(
                        p(seq(false, false, true), seq(false)),
                        seq(true),
                        p(seq(false, false, true), seq(true))),
                transition(
                        p(seq(false, false, false), seq(true)),
                        seq(false),
                        p(seq(true, false, false), seq(false))),
                transition(
                        p(seq(false, true, false), seq(false)),
                        seq(false),
                        p(seq(false, true, false), seq(false))),
                transition(
                        p(seq(false, false, true), seq(true)),
                        seq(false),
                        p(seq(true, false, true), seq(false))),
                transition(
                        p(seq(false, true, true), seq(false)),
                        seq(false),
                        p(seq(false, true, true), seq(false))),
                transition(
                        p(seq(false, false, false), seq(false)),
                        seq(false),
                        p(seq(false, false, false), seq(false))),
                transition(
                        p(seq(false, false, true), seq(false)),
                        seq(false),
                        p(seq(false, false, true), seq(false))),
                transition(
                        p(seq(true, false, false), seq(true)),
                        seq(true),
                        p(seq(false, true, false), seq(true))),
                transition(
                        p(seq(true, false, true), seq(true)),
                        seq(true),
                        p(seq(false, true, true), seq(true))),
                transition(
                        p(seq(true, true, true), seq(true)),
                        seq(false),
                        p(seq(false, false, false), seq(false))),
                transition(
                        p(seq(true, false, false), seq(true)),
                        seq(false),
                        p(seq(false, true, false), seq(false))),
                transition(
                        p(seq(true, false, true), seq(true)),
                        seq(false),
                        p(seq(false, true, true), seq(false))),
                transition(
                        p(seq(true, true, false), seq(false)),
                        seq(false),
                        p(seq(true, true, false), seq(false))),
                transition(
                        p(seq(true, true, true), seq(false)),
                        seq(false),
                        p(seq(true, true, true), seq(false))),
                transition(
                        p(seq(true, false, false), seq(false)),
                        seq(false),
                        p(seq(true, false, false), seq(false))),
                transition(
                        p(seq(false, true, false), seq(true)),
                        seq(false),
                        p(seq(true, true, false), seq(false))),
                transition(
                        p(seq(true, true, false), seq(true)),
                        seq(false),
                        p(seq(false, false, true), seq(false))),
                transition(
                        p(seq(true, false, true), seq(false)),
                        seq(false),
                        p(seq(true, false, true), seq(false))),
                transition(
                        p(seq(false, true, true), seq(true)),
                        seq(false),
                        p(seq(true, true, true), seq(false))),
                transition(
                        p(seq(true, true, true), seq(true)),
                        seq(true),
                        p(seq(false, false, false), seq(true))),
                transition(
                        p(seq(true, true, false), seq(false)),
                        seq(true),
                        p(seq(true, true, false), seq(true))),
                transition(
                        p(seq(true, true, true), seq(false)),
                        seq(true),
                        p(seq(true, true, true), seq(true))),
                transition(
                        p(seq(true, false, false), seq(false)),
                        seq(true),
                        p(seq(true, false, false), seq(true))),
                transition(
                        p(seq(false, true, false), seq(true)),
                        seq(true),
                        p(seq(true, true, false), seq(true))),
                transition(
                        p(seq(true, true, false), seq(true)),
                        seq(true),
                        p(seq(false, false, true), seq(true))),
                transition(
                        p(seq(true, false, true), seq(false)),
                        seq(true),
                        p(seq(true, false, true), seq(true))),
                transition(
                        p(seq(false, true, true), seq(true)),
                        seq(true),
                        p(seq(true, true, true), seq(true)))), ts.getTransitions());

        assertEquals(set("inc"), ts.getLabel(p(seq(false, false, false), seq(true))));
        assertEquals(set("r3"), ts.getLabel(p(seq(false, false, true), seq(false))));
        assertEquals(set("r2", "r3", "inc"), ts.getLabel(p(seq(false, true, true), seq(true))));
        assertEquals(set("r3", "inc", "r1"), ts.getLabel(p(seq(true, false, true), seq(true))));
        assertEquals(set("r3", "inc"), ts.getLabel(p(seq(false, false, true), seq(true))));
        assertEquals(set(), ts.getLabel(p(seq(false, false, false), seq(false))));
        assertEquals(set("r2", "inc"), ts.getLabel(p(seq(false, true, false), seq(true))));
        assertEquals(set("r2", "r3"), ts.getLabel(p(seq(false, true, true), seq(false))));
        assertEquals(set("r2", "r1"), ts.getLabel(p(seq(true, true, false), seq(false))));
        assertEquals(set("r2"), ts.getLabel(p(seq(false, true, false), seq(false))));
        assertEquals(set("r1"), ts.getLabel(p(seq(true, false, false), seq(false))));
        assertEquals(set("r2", "inc", "r1"), ts.getLabel(p(seq(true, true, false), seq(true))));
        assertEquals(set("r2", "r3", "r1"), ts.getLabel(p(seq(true, true, true), seq(false))));
        assertEquals(set("inc", "r1"), ts.getLabel(p(seq(true, false, false), seq(true))));
        assertEquals(set("r3", "r1"), ts.getLabel(p(seq(true, false, true), seq(false))));
        assertEquals(set("r2", "r3", "inc", "r1"), ts.getLabel(p(seq(true, true, true), seq(true))));
    }
}
