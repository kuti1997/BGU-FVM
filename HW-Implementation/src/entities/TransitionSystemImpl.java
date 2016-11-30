package entities;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {

	private Set<STATE> _states;
	private Set<STATE> _initial_states;
	private Set<ACTION> _actions;
	private Set<Transition<STATE,ACTION>> _transitions;
	private Set<ATOMIC_PROPOSITION> _atomic_propositions;
	private Map<STATE,Set<ATOMIC_PROPOSITION>> _labels;
	private String _name;

	public TransitionSystemImpl(){
		_states = new HashSet<STATE>();
		_actions = new HashSet<ACTION>();
		_transitions = new HashSet<Transition<STATE, ACTION>>();
		_atomic_propositions = new HashSet<ATOMIC_PROPOSITION>();
		_initial_states = new HashSet<STATE>();
		_labels = new HashMap<STATE,Set<ATOMIC_PROPOSITION>>();
		_name = "__EMPTY__";
	}

	public TransitionSystemImpl ( String name){
		this();
		_name = name; // Do we need to get it in constructor?
	}


	public String getName() {
		return _name;
	}


	public void setName(String name) {
		_name = name;
	}


	public void addAction(ACTION action) {
		_actions.add(action);
	}


	public void addInitialState(STATE state) throws FVMException {
		_states.add(state);
		_initial_states.add(state);

	}

	public void addState(STATE state) {
		_states.add(state);

	}

	public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
		if(!action_exist(t.getAction()))
			throw new FVMException("transition system "+ _name +" does not have ACTION "+ t.getAction().toString());
		if(!state_exist(t.getFrom()))
			throw new FVMException("transition system "+ _name +" does not have From STATE "+ t.getFrom().toString());
		if(!state_exist(t.getTo()))
			throw new FVMException("transition system "+ _name +" does not have To STATE "+ t.getTo().toString());
		_transitions.add(t);
	}

	private boolean state_exist(STATE to_compare) {
		for (STATE state : _states)
			if(state.equals(to_compare))
				return true;
		return false;
	}

	private boolean action_exist(ACTION to_compare) {
		for (ACTION action : _actions)
			if(action.equals(to_compare))
				return true;
		return false;
	}


	public Set<ACTION> getActions() {
		return new HashSet<ACTION>(_actions);
	}

	public void addAtomicProposition(ATOMIC_PROPOSITION p) {
		_atomic_propositions.add(p);
	}

	public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
		return new HashSet<ATOMIC_PROPOSITION>(_atomic_propositions);
	}

	public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
		if(!state_exist(s))
			throw new FVMException("transition system "+ _name +" does not have STATE "+ s.toString());
		if(!atomic_prop_exist(l))
			throw new FVMException("transition system "+ _name +" does not have ATOMIC_PROPOSITION "+ l.toString());
		Set<ATOMIC_PROPOSITION> state_atomic_propositions = getLabel(s);
		state_atomic_propositions.add(l);	
	}

	private boolean atomic_prop_exist(ATOMIC_PROPOSITION to_compare) {
		for (ATOMIC_PROPOSITION atomic_proposition : _atomic_propositions)
			if(atomic_proposition.equals(to_compare))
				return true;
		return false;
	}


	public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
		// check if there is an atomic proposition set.	
		Set<ATOMIC_PROPOSITION> state_atomic_propositions = _labels.get(s);
		if(state_atomic_propositions != null)
			return state_atomic_propositions;
		else
		{
			// if there are not any atomic propositions, then create new empty set.
			state_atomic_propositions = new HashSet<ATOMIC_PROPOSITION>();
			_labels.put(s,state_atomic_propositions);
			return state_atomic_propositions;
		}
	}


	public Set<STATE> getInitialStates() {
		return new HashSet<STATE>(_initial_states);
	}


	public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
		return new HashMap<STATE,Set<ATOMIC_PROPOSITION>>(_labels);
	}


	public Set<STATE> getStates() {
		return new HashSet<STATE>(_states);
	}


	public Set<Transition<STATE, ACTION>> getTransitions() {
		return new HashSet<Transition<STATE, ACTION>>(_transitions);
	}


	public void removeAction(ACTION action) throws FVMException {
		if(!_actions.remove(action))
			throw new FVMException("transition system "+ _name +" does not have ACTION "+ action.toString());
	}


	public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
		if(!_actions.remove(p))
			throw new FVMException("transition system "+ _name +" does not have ATOMIC_PROPOSITION "+ p.toString());
	}


	public void removeInitialState(STATE state) {
		_initial_states.remove(state);
	}


	public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
		Set<ATOMIC_PROPOSITION> state_atomic_propositions = _labels.get(s);
		if(state_atomic_propositions != null){
			state_atomic_propositions.remove(l);
		}
	}


	public void removeState(STATE state) throws FVMException {
		removeInitialState(state);
		if(!_actions.remove(state))
			throw new FVMException("transition system "+ _name +" does not have STATE "+ state.toString());

	}


	public void removeTransition(Transition<STATE, ACTION> t) {
		_transitions.remove(t);
	}

}
