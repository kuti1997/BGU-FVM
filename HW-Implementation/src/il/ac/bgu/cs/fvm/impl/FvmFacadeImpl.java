package il.ac.bgu.cs.fvm.impl;

import entities.TransitionSystemImpl;
import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
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
        Set<S> ts_states = ts.getStates();
        Set<A> ts_action = ts.getActions();

        Set<S> ts_initial_states = ts.getInitialStates();
        if (ts_initial_states.size() > 1)
            return false;

        Set<S> states_to_check;
        for (S state : ts_states) {
            for (A action : ts_action) {
                states_to_check = post(ts, state, action);
                if (states_to_check.size() > 1)
                    return false;
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        Set<S> ts_initial_states = ts.getInitialStates();
        if (ts_initial_states.size() > 1)
            return false;

        Set<S> ts_states = ts.getStates();


        Set<S> single_state_posts;
        for (S state : ts_states) {
            single_state_posts = post(ts, state);
            @SuppressWarnings("unchecked")
            S[] posts_in_array = (S[]) single_state_posts.toArray();
            for (int i = 0; i < posts_in_array.length - 1; i++) {
                for (int j = i + 1; j < posts_in_array.length; j++) {
                    if (ts.getLabel(posts_in_array[i]).containsAll(ts.getLabel(posts_in_array[j]))) {
                        if (ts.getLabel(posts_in_array[j]).containsAll(ts.getLabel(posts_in_array[i]))) {
                            return false;
                        }
                    }
                }
            }

        }


        return true;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e))
            return true;
        return false;
    }

    //	@SuppressWarnings("unchecked")
//	@Override
//	public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
//		S from = e.head();
//		if(!state_exist(ts, from))
//			throw new StateNotFoundException(from);
//		if(e.tail().size() == 0){
//			return true;
//		}
//
//
//		AlternatingSequence<S, A> initial_tail = (AlternatingSequence<S, A>) e.tail();
//
//		A action = (A) initial_tail.head();
//		if(!action_exist(ts, action))
//			throw new ActionNotFoundException(action);
//
//		AlternatingSequence<S, A> tail = (AlternatingSequence<S, A>) initial_tail.tail();
//		while(tail.size() != 0){
//			S target_state_to_check = tail.head();
//
//			if(!state_exist(ts, target_state_to_check))
//				throw new StateNotFoundException(target_state_to_check);
//
//			Set <S> post_of_from = post(ts , from, action);
//			if(!post_of_from.contains(target_state_to_check))
//				return false;
//
//			from = target_state_to_check;
//			initial_tail = (AlternatingSequence<S, A>) tail.tail();
//			if(initial_tail.size() == 0){
//				return true;
//			}
//			action = (A) initial_tail.head();
//			if(!action_exist(ts, action))
//				throw new ActionNotFoundException(action);
//			tail = (AlternatingSequence<S, A>) initial_tail.tail();
//
//		}
//
//		return true;
//
//	}
    @SuppressWarnings("unchecked")
    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        //TODO:: what happen if there is a actions without state? like s1 a1 s2 a2
        S from = e.head();
        if (!state_exist(ts, from))
            throw new StateNotFoundException(from);
        if (e.tail().size() == 0) {
            return true;
        }

        AlternatingSequence<A, S> actions = e.tail();
        A action = actions.head();

        if (!action_exist(ts, action))
            throw new ActionNotFoundException(action);

        AlternatingSequence<S, A> states = actions.tail();
        while (states.size() != 0) {
            S target_state_to_check = states.head();

            if (!state_exist(ts, target_state_to_check))
                throw new StateNotFoundException(target_state_to_check);

            Set<S> post_of_from = post(ts, from, action);
            if (!post_of_from.contains(target_state_to_check))
                return false;

            from = target_state_to_check;
            actions = states.tail();
            if (actions.size() == 0) {
                return true;
            }
            action = (A) actions.head();
            if (!action_exist(ts, action))
                throw new ActionNotFoundException(action);
            states = actions.tail();

        }

        return true;

    }


    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!ts.getInitialStates().contains(e.head()))
            return false;
        if (!isExecutionFragment(ts, e))
            return false;
        return true;
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!isStateTerminal(ts, e.last()))
            return false;
        if (!isExecutionFragment(ts, e))
            return false;
        return true;
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        if (!state_exist(ts, s))
            throw new StateNotFoundException(s);
        Set<S> s_posts = post(ts, s);
        if (s_posts.size() == 0)
            return true;
        return false;
    }

    private <S, A> boolean state_exist(TransitionSystem<S, A, ?> ts, S to_compare) {
        for (S state : ts.getStates())
            if (state.equals(to_compare))
                return true;
        return false;
    }

    private <S, A> boolean action_exist(TransitionSystem<S, A, ?> ts, A to_compare) {
        for (A action : ts.getActions())
            if (action.equals(to_compare))
                return true;
        return false;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> states_to_return = postHelper(ts, s);
        return states_to_return;
    }

    private <S, A> Set<S> postHelper(TransitionSystem<S, A, ?> ts, S s) {
        Set<S> states_to_return = new HashSet<S>();

        Set<A> ts_actions = ts.getActions();

        Set<S> acc;
        for (A action : ts_actions) {
            acc = post(ts, s, action);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c) {
            acc = post(ts, state);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> states_to_return = new HashSet<S>();
        Set<Transition<S, A>> tsTransitions = ts.getTransitions();

        for (Transition<S, A> trans : tsTransitions) {
            S from_state = trans.getFrom();
            A action_of_transition = trans.getAction();

            if (from_state.equals(s) && action_of_transition.equals(a)) {
                S to_state = trans.getTo();
                states_to_return.add(to_state);
            }
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c) {
            acc = post(ts, state, a);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> states_to_return;
        states_to_return = preHelper(ts, s);
        return states_to_return;
    }

    private <S, A> Set<S> preHelper(TransitionSystem<S, A, ?> ts, S s) {
        Set<S> states_to_return = new HashSet<S>();

        Set<A> ts_actions = ts.getActions();

        Set<S> acc;
        for (A action : ts_actions) {
            acc = pre(ts, s, action);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c) {
            acc = pre(ts, state);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c) {
            acc = pre(ts, state, a);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> states_to_return = new HashSet<S>();
        HashSet<Transition<S, A>> tsTransitions = (HashSet<Transition<S, A>>) ts.getTransitions();

        for (Transition<S, A> trans : tsTransitions) {
            A action_of_transition = trans.getAction();
            S to_state = trans.getTo();

            if (action_of_transition.equals(a) && to_state.equals(s)) {
                S from_state = trans.getFrom();
                states_to_return.add(from_state);
            }
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> to_return = new HashSet<S>();

        for (S init : ts.getInitialStates()) {
            to_return.add(init);
            to_return.addAll(reach(ts, init, to_return));
        }


        return to_return;
    }

    private <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts, S state, Set<S> to_return) {
        if (post(ts, state).size() == 0) {
            return to_return;
        } else {
            for (Transition<S, A> trans : ts.getTransitions()) {
                if (trans.getFrom().equals(state)) {
                    if (!to_return.contains(trans.getTo())) {
                        to_return.add(trans.getTo());
                        reach(ts, trans.getTo(), to_return);
                    }
                }
            }
        }

        return to_return;
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
