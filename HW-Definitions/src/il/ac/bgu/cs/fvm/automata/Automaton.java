package il.ac.bgu.cs.fvm.automata;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * An non-deterministic automaton, composed of states and transitions.
 * @param <STATE> Type of states.
 * @param <L> Type of transitions/alphabet the automaton understands.
 */
public class Automaton<STATE, L> {

	private final Map<STATE, Map<Set<L>, Set<STATE>>>	transitions;
	private final Set<STATE>                            initial;
	private final Set<STATE>                            accepting;

	public Automaton() {
		transitions = new HashMap<>();
		initial = new HashSet<>();
		accepting = new HashSet<>();
	}

	public void addTransition(STATE source, Set<L> symbol, STATE destination) {
		if (!transitions.containsKey(source))
			addState(source);

		if (!transitions.containsKey(destination))
			addState(destination);

		Set<STATE> set = transitions.get(source).get(symbol);
		if (set == null) {
			set = new HashSet<>();
			transitions.get(source).put(symbol, set);
		}
		set.add(destination);
	}

	public void addState(STATE s) {
		if (!transitions.containsKey(s))
			transitions.put(s, new HashMap<>());
	}

    /**
     * Returns the states connected to {@code source} with transitions labeled 
     * by {@code symbol}.
     * @param source
     * @param symbol
     * @return Iterable of the states immediately reachable from {@code source}, given {@code symbol}.
     */
	public Set<STATE> nextStates(STATE source, Set<L> symbol) {
		if (!transitions.containsKey(source)) {
			throw new IllegalArgumentException("State " + source +" not in automaton.");
        } else {
			return transitions.get(source).get(symbol);
        }
	}

	public void setInitial(STATE s) {
		addState(s);
		initial.add(s);
	}

	public Iterable<STATE> getInitialStates() {
		return initial;
	}

	public void setAccepting(STATE s) {
		addState(s);
		accepting.add(s);
	}

	public Set<STATE> getAcceptingStates() {
		return accepting;
	}

}
