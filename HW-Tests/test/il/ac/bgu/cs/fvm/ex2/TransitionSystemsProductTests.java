package il.ac.bgu.cs.fvm.ex2;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder.AP;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder.Action;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder.State;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import il.ac.bgu.cs.fvm.util.Pair;

public class TransitionSystemsProductTests {

    FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

    @SuppressWarnings("unchecked")
	@Test
    // See page 52, Example 2.9 in the book
    public void booking() {
        TransitionSystem<State, Action, AP> bcr = BookingSystemBuilder.buildBCR();
        TransitionSystem<State, Action, AP> bp = BookingSystemBuilder.buildBP();
        TransitionSystem<State, Action, AP> printer = BookingSystemBuilder.buildPrinter();

        Set<Action> hs1 = new HashSet<>();
        hs1.add(Action.store);
        TransitionSystem<Pair<State, State>, Action, AP> ts1 = fvmFacadeImpl.interleave(bcr, bp, hs1);

        Set<Action> hs2 = new HashSet<>();
        hs1.add(Action.prt_cmd);
        TransitionSystem<Pair<Pair<State, State>, State>, Action, AP> ts = fvmFacadeImpl.interleave(ts1, printer, hs2);

        /*
        final TsPrinter tsPrinter = new TsPrinter();

        tsPrinter.setClassPrinter(Action.class, (obj, tsp, out) -> {
                              out.print("Action." + obj.name());
                          });

        tsPrinter.setClassPrinter(State.class, (obj, tsp, out) -> {
                              out.print("State." + obj.name());
                          });

        tsPrinter.setClassPrinter(AP.class, (obj, tsp, out) -> {
                              out.print("AP." + obj.name());
                          });
         
        out.println(tsPrinter.getAssertions(ts));
         */
        assertEquals(set(
                p(p(State.S1, State.S0), State.S0),
                p(p(State.S0, State.S0), State.S1),
                p(p(State.S0, State.S1), State.S1),
                p(p(State.S1, State.S1), State.S1),
                p(p(State.S0, State.S1), State.S0),
                p(p(State.S0, State.S0), State.S0),
                p(p(State.S1, State.S0), State.S1),
                p(p(State.S1, State.S1), State.S0)), ts.getStates());

        assertEquals(set(p(p(State.S0, State.S0), State.S0)), ts.getInitialStates());

        assertEquals(set(Action.store, Action.scan, Action.print, Action.prt_cmd), ts.getActions());

        assertEquals(set(), ts.getAtomicPropositions());

        assertEquals(set(
                transition(p(p(State.S0, State.S1), State.S0), Action.prt_cmd, p(p(State.S0, State.S0), State.S0)),
                transition(p(p(State.S0, State.S1), State.S1), Action.print, p(p(State.S0, State.S1), State.S0)),
                transition(p(p(State.S0, State.S1), State.S0), Action.scan, p(p(State.S1, State.S1), State.S0)),
                transition(p(p(State.S1, State.S0), State.S0), Action.store, p(p(State.S0, State.S1), State.S0)),
                transition(p(p(State.S0, State.S0), State.S1), Action.scan, p(p(State.S1, State.S0), State.S1)),
                transition(p(p(State.S0, State.S1), State.S1), Action.prt_cmd, p(p(State.S0, State.S0), State.S1)),
                transition(p(p(State.S1, State.S1), State.S0), Action.prt_cmd, p(p(State.S1, State.S1), State.S1)),
                transition(p(p(State.S1, State.S0), State.S1), Action.store, p(p(State.S0, State.S1), State.S1)),
                transition(p(p(State.S1, State.S0), State.S1), Action.print, p(p(State.S1, State.S0), State.S0)),
                transition(p(p(State.S0, State.S1), State.S1), Action.scan, p(p(State.S1, State.S1), State.S1)),
                transition(p(p(State.S0, State.S0), State.S0), Action.prt_cmd, p(p(State.S0, State.S0), State.S1)),
                transition(p(p(State.S1, State.S1), State.S0), Action.prt_cmd, p(p(State.S1, State.S0), State.S0)),
                transition(p(p(State.S1, State.S1), State.S1), Action.print, p(p(State.S1, State.S1), State.S0)),
                transition(p(p(State.S1, State.S1), State.S1), Action.prt_cmd, p(p(State.S1, State.S0), State.S1)),
                transition(p(p(State.S0, State.S1), State.S0), Action.prt_cmd, p(p(State.S0, State.S1), State.S1)),
                transition(p(p(State.S0, State.S0), State.S1), Action.print, p(p(State.S0, State.S0), State.S0)),
                transition(p(p(State.S0, State.S0), State.S0), Action.scan, p(p(State.S1, State.S0), State.S0)),
                transition(p(p(State.S1, State.S0), State.S0), Action.prt_cmd, p(p(State.S1, State.S0), State.S1))), ts.getTransitions());

        assertEquals(set(), ts.getLabel(p(p(State.S1, State.S0), State.S0)));
        assertEquals(set(), ts.getLabel(p(p(State.S0, State.S0), State.S1)));
        assertEquals(set(), ts.getLabel(p(p(State.S0, State.S1), State.S1)));
        assertEquals(set(), ts.getLabel(p(p(State.S1, State.S1), State.S1)));
        assertEquals(set(), ts.getLabel(p(p(State.S0, State.S1), State.S0)));
        assertEquals(set(), ts.getLabel(p(p(State.S0, State.S0), State.S0)));
        assertEquals(set(), ts.getLabel(p(p(State.S1, State.S0), State.S1)));
        assertEquals(set(), ts.getLabel(p(p(State.S1, State.S1), State.S0)));

    }

    @SuppressWarnings("unchecked")
	@Test // See page 37, Figure 2.4 in the book 
    public void trafficLight() {
        TransitionSystem<String, String, String> ts1 = FvmFacade.createInstance().createTransitionSystem();

        ts1.addState("red");
        ts1.addState("green");

        ts1.addInitialState("red");

        ts1.addAction("go1");

        ts1.addAtomicProposition("tl1-is-red");
        ts1.addToLabel("red", "tl1-is-red");

        ts1.addTransition(new Transition<>("red", "go1", "green"));
        ts1.addTransition(new Transition<>("green", "go1", "red"));

        TransitionSystem<String, String, String> ts2 = FvmFacade.createInstance().createTransitionSystem();
        ts2.addState("red");
        ts2.addState("green");

        ts2.addInitialState("red");
        ts2.addAction("go2");

        ts2.addAtomicProposition("tl2-is-red");
        ts2.addToLabel("red", "tl2-is-red");

        ts2.addTransition(new Transition<>("red", "go2", "green"));
        ts2.addTransition(new Transition<>("green", "go2", "red"));

        TransitionSystem<Pair<String, String>, String, String> ts = fvmFacadeImpl.interleave(ts1, ts2);

        assertEquals(set(
                p("red", "green"),
                p("green", "green"),
                p("green", "red"),
                p("red", "red")), ts.getStates());

        assertEquals(set(p("red", "red")), ts.getInitialStates());

        assertEquals(set("go1", "go2"), ts.getActions());

        assertEquals(set("tl2-is-red", "tl1-is-red"), ts.getAtomicPropositions());

        assertEquals(set(transition(p("green", "green"), "go1", p("red", "green")),
                         transition(p("red", "red"), "go2", p("red", "green")),
                         transition(p("green", "red"), "go2", p("green", "green")),
                         transition(p("green", "red"), "go1", p("red", "red")),
                         transition(p("red", "red"), "go1", p("green", "red")),
                         transition(p("red", "green"), "go2", p("red", "red")),
                         transition(p("green", "green"), "go2", p("green", "red")),
                         transition(p("red", "green"), "go1", p("green", "green"))), ts.getTransitions());

        assertEquals(set("tl1-is-red"), ts.getLabel(p("red", "green")));
        assertEquals(set(), ts.getLabel(p("green", "green")));
        assertEquals(set("tl2-is-red"), ts.getLabel(p("green", "red")));
        assertEquals(set("tl2-is-red", "tl1-is-red"), ts.getLabel(p("red", "red")));
    }
}
