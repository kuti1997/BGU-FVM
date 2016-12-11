package entities;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.DeletionOfAttachedActionException;
import il.ac.bgu.cs.fvm.exceptions.DeletionOfAttachedAtomicPropositionException;
import il.ac.bgu.cs.fvm.exceptions.DeletionOfAttachedStateException;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.InvalidInitialStateException;
import il.ac.bgu.cs.fvm.exceptions.InvalidLablingPairException;
import il.ac.bgu.cs.fvm.exceptions.InvalidTransitionException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart;
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
		if(!state_exist(state))
			throw new InvalidInitialStateException(state);
		_initial_states.add(state);

	}

	public void addState(STATE state) {
		_states.add(state);

	}

	public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
		if(!action_exist(t.getAction()))
			throw new InvalidTransitionException(t);
		if(!state_exist(t.getFrom()))
			throw new InvalidTransitionException(t);
		if(!state_exist(t.getTo()))
			throw new InvalidTransitionException(t);
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
			throw new StateNotFoundException(s);
		if(!atomic_prop_exist(l))
			throw new InvalidLablingPairException(s,l);
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
		if(! state_exist(s))
			throw new StateNotFoundException(s);
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
		for(Transition<STATE, ACTION> trans : _transitions){
			if(trans.getAction().equals(action))
				throw new DeletionOfAttachedActionException(action , TransitionSystemPart.TRANSITIONS);
		}
		
		if(!_actions.remove(action))
			throw new ActionNotFoundException(action);
	}


	public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
		
		Set<ATOMIC_PROPOSITION> ap_of_state = new HashSet<ATOMIC_PROPOSITION> ();
		for(STATE s : _states){
			ap_of_state = getLabel(s);
			if(ap_of_state.contains(p))
				throw new DeletionOfAttachedAtomicPropositionException(p , TransitionSystemPart.LABELING_FUNCTION);
		}
		
		if(!_atomic_propositions.remove(p))
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
		if(_initial_states.contains(state))
			throw new DeletionOfAttachedStateException(state , TransitionSystemPart.INITIAL_STATES);
		
		for(Transition<STATE, ACTION> trans : _transitions){
			if(trans.getFrom().equals(state) || trans.getTo().equals(state))
				throw new DeletionOfAttachedStateException(state , TransitionSystemPart.TRANSITIONS);
		}
		
		Set<ATOMIC_PROPOSITION> state_ap = getLabel(state);
		if(state_ap.size() > 0){
			throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);
		}
		
		boolean removed = _states.remove(state);
		if(!removed)
			throw new FVMException("transition system "+ _name +" does not have STATE "+ state.toString());

	}


	public void removeTransition(Transition<STATE, ACTION> t) {
		_transitions.remove(t);
	}

	
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((_actions == null) ? 0 : _actions.hashCode());
		result = prime * result + ((_atomic_propositions == null) ? 0 : _atomic_propositions.hashCode());
		result = prime * result + ((_initial_states == null) ? 0 : _initial_states.hashCode());
		result = prime * result + ((_labels == null) ? 0 : _labels.hashCode());
		result = prime * result + ((_name == null) ? 0 : _name.hashCode());
		result = prime * result + ((_states == null) ? 0 : _states.hashCode());
		result = prime * result + ((_transitions == null) ? 0 : _transitions.hashCode());
		return result;
	}

	
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		TransitionSystemImpl other = (TransitionSystemImpl) obj;
		if (_actions == null) {
			if (other._actions != null)
				return false;
		} else if (!_actions.equals(other._actions))
			return false;
		if (_atomic_propositions == null) {
			if (other._atomic_propositions != null)
				return false;
		} else if (!_atomic_propositions.equals(other._atomic_propositions))
			return false;
		if (_initial_states == null) {
			if (other._initial_states != null)
				return false;
		} else if (!_initial_states.equals(other._initial_states))
			return false;
		if (_labels == null) {
			if (other._labels != null)
				return false;
		} else if (!_labels.equals(other._labels))
			return false;
		if (_name == null) {
			if (other._name != null)
				return false;
		} else if (!_name.equals(other._name))
			return false;
		if (_states == null) {
			if (other._states != null)
				return false;
		} else if (!_states.equals(other._states))
			return false;
		if (_transitions == null) {
			if (other._transitions != null)
				return false;
		} else if (!_transitions.equals(other._transitions))
			return false;
		return true;
	}

}
