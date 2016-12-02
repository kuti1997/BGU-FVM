package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import java.io.InputStream;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import entities.*;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

	@Override
	public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {

		return new TransitionSystemImpl<S, A, P>();
	}

	@Override
	public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
		Set <S> ts_states = ts.getStates();
		Set <A> ts_action = ts.getActions();
		
		Set<S> states_to_check = new HashSet<S>();
		for(S state : ts_states){
			for(A action : ts_action){
				states_to_check = post(ts, state, action);
				if(states_to_check.size() > 1)
					return false;
			}
		}
		
		Set <S> ts_initial_states = ts.getInitialStates();
		if(ts_initial_states.size() > 1)
			return false;
		
		return true;
	}

	@Override
	public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
		Set <S> ts_initial_states = ts.getInitialStates();
		if(ts_initial_states.size() > 1)
			return false;
		
		Set <S> ts_states = ts.getStates();
		Set <P> ts_atomic_propositions = ts.getAtomicPropositions();
		
		Set <S> single_state_posts = new HashSet<S>();
		for(S state : ts_states){
			single_state_posts = post(ts , state);
			for(P ap : ts_atomic_propositions){
				
			}
		}
		
		
		return true;
	}

	@Override
	public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isExecution
	}

	@Override
	public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isExecutionFragment
	}

	@Override
	public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isInitialExecutionFragment
	}

	@Override
	public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isMaximalExecutionFragment
	}

	@Override
	public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isStateTerminal
	}

	@Override
	public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
		Set<S> states_to_return = new HashSet<S>();
		states_to_return = postHelper(ts, s);
		return states_to_return;
	}

	private <S , A> Set<S> postHelper(TransitionSystem<S, A, ?> ts, S s) {
		Set<S> states_to_return = new HashSet<S>();

		Set<A> ts_actions = (Set<A>) ts.getActions();

		Set<S> acc = new HashSet<S>();
		for(A action : ts_actions){
			acc = post(ts, s, action);
			states_to_return.addAll(acc);
		}

		return states_to_return;
	}

	@Override
	public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
		Set<S> states_to_return = new HashSet<S>();

		Set<S> acc = new HashSet<S>();
		for(S state : c){
			acc = post(ts, state);
			states_to_return.addAll(acc);
		}

		return states_to_return;
	}

	@Override
	public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
		Set<S> states_to_return = new HashSet<S>();
		HashSet<Transition<S, A>> tsTransitions = (HashSet<Transition<S, A>>) ts.getTransitions(); 

		for(Transition<S, A> trans: tsTransitions ){
			S from_state = trans.getFrom();
			A action_of_transition = trans.getAction();

			if(from_state.equals(s) && action_of_transition.equals(a)){
				S to_state = trans.getTo();
				states_to_return.add(to_state);
			}
		}

		return states_to_return;
	}

	@Override
	public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
		Set<S> states_to_return = new HashSet<S>();

		Set<S> acc = new HashSet<S>();
		for(S state : c){
			acc = post(ts, state, a);
			states_to_return.addAll(acc);
		}

		return states_to_return;
	}

	@Override
	public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
		Set<S> states_to_return = new HashSet<S>();
		states_to_return = preHelper(ts, s);
		return states_to_return;
	}

	private <S , A> Set<S> preHelper(TransitionSystem<S, A, ?> ts, S s) {
		Set<S> states_to_return = new HashSet<S>();

		Set<A> ts_actions = (Set<A>) ts.getActions();

		Set<S> acc = new HashSet<S>();
		for(A action : ts_actions){
			acc = pre(ts, s, action);
			states_to_return.addAll(acc);
		}

		return states_to_return;
	}

	@Override
	public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
		Set<S> states_to_return = new HashSet<S>();

		Set<S> acc = new HashSet<S>();
		for(S state : c){
			acc = pre(ts, state);
			states_to_return.addAll(acc);
		}

		return states_to_return;
	}

	@Override
	public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
		Set<S> states_to_return = new HashSet<S>();

		Set<S> acc = new HashSet<S>();
		for(S state : c){
			acc = pre(ts, state, a);
			states_to_return.addAll(acc);
		}

		return states_to_return;
	}

	@Override
	public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
		Set<S> states_to_return = new HashSet<S>();
		HashSet<Transition<S, A>> tsTransitions = (HashSet<Transition<S, A>>) ts.getTransitions(); 

		for(Transition<S, A> trans: tsTransitions ){
			A action_of_transition = trans.getAction();
			S to_state = trans.getTo();

			if( action_of_transition.equals(a) && to_state.equals(s)){
				S from_state = trans.getFrom();
				states_to_return.add(from_state);
			}
		}

		return states_to_return;
	}

	@Override
	public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement reach
	}

	@Override
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
	}

	@Override
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
	}

	@Override
	public <L, A> ProgramGraph<L, A> createProgramGraph() {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
	}

	@Override
	public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
	}

	@Override
	public TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
	}

	@Override
	public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
	}

	@Override
	public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, P> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
	}

	@Override
	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
	}

	@Override
	public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
	}

	@Override
	public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
	}

	@Override
	public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
		throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
	}



}
