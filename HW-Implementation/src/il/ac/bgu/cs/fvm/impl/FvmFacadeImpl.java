package il.ac.bgu.cs.fvm.impl;

import entities.ProgramGraphImpl;
import entities.TransitionSystemImpl;
import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VeficationSucceeded;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.io.InputStream;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static java.util.stream.Collectors.toList;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade
{

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem()
    {

        return new TransitionSystemImpl<S, A, P>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts)
    {
        Set<S> ts_states = ts.getStates();
        Set<A> ts_action = ts.getActions();

        Set<S> ts_initial_states = ts.getInitialStates();
        if (ts_initial_states.size() > 1) return false;

        Set<S> states_to_check;
        for (S state : ts_states)
        {
            for (A action : ts_action)
            {
                states_to_check = post(ts, state, action);
                if (states_to_check.size() > 1) return false;
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts)
    {
        Set<S> ts_initial_states = ts.getInitialStates();
        if (ts_initial_states.size() > 1) return false;

        Set<S> ts_states = ts.getStates();


        Set<S> single_state_posts;
        for (S state : ts_states)
        {
            single_state_posts = post(ts, state);
            @SuppressWarnings("unchecked") S[] posts_in_array = (S[]) single_state_posts.toArray();
            for (int i = 0; i < posts_in_array.length - 1; i++)
            {
                for (int j = i + 1; j < posts_in_array.length; j++)
                {
                    if (ts.getLabel(posts_in_array[i]).containsAll(ts.getLabel(posts_in_array[j])))
                    {
                        if (ts.getLabel(posts_in_array[j]).containsAll(ts.getLabel(posts_in_array[i])))
                        {
                            return false;
                        }
                    }
                }
            }

        }


        return true;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
    {
        if (isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e)) return true;
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
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
    {
        S from = e.head();
        if (!state_exist(ts, from)) throw new StateNotFoundException(from);
        if (e.tail().size() == 0)
        {
            return true;
        }

        AlternatingSequence<A, S> actions = e.tail();
        A action = actions.head();

        if (!action_exist(ts, action)) throw new ActionNotFoundException(action);

        AlternatingSequence<S, A> states = actions.tail();
        while (states.size() != 0)
        {
            S target_state_to_check = states.head();

            if (!state_exist(ts, target_state_to_check)) throw new StateNotFoundException(target_state_to_check);

            Set<S> post_of_from = post(ts, from, action);
            if (!post_of_from.contains(target_state_to_check)) return false;

            from = target_state_to_check;
            actions = states.tail();
            if (actions.size() == 0)
            {
                return true;
            }
            action = (A) actions.head();
            if (!action_exist(ts, action)) throw new ActionNotFoundException(action);
            states = actions.tail();

        }

        return true;

    }


    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
    {
        if (!ts.getInitialStates().contains(e.head())) return false;
        if (!isExecutionFragment(ts, e)) return false;
        return true;
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
    {
        if (!isStateTerminal(ts, e.last())) return false;
        if (!isExecutionFragment(ts, e)) return false;
        return true;
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s)
    {
        if (!state_exist(ts, s)) throw new StateNotFoundException(s);
        Set<S> s_posts = post(ts, s);
        if (s_posts.size() == 0) return true;
        return false;
    }

    private <S, A> boolean state_exist(TransitionSystem<S, A, ?> ts, S to_compare)
    {
        for (S state : ts.getStates())
            if (state.equals(to_compare)) return true;
        return false;
    }

    private <S, A> boolean action_exist(TransitionSystem<S, A, ?> ts, A to_compare)
    {
        for (A action : ts.getActions())
            if (action.equals(to_compare)) return true;
        return false;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s)
    {
        Set<S> states_to_return = postHelper(ts, s);
        return states_to_return;
    }

    private <S, A> Set<S> postHelper(TransitionSystem<S, A, ?> ts, S s)
    {
        Set<S> states_to_return = new HashSet<S>();

        Set<A> ts_actions = ts.getActions();

        Set<S> acc;
        for (A action : ts_actions)
        {
            acc = post(ts, s, action);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c)
    {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c)
        {
            acc = post(ts, state);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a)
    {
        Set<S> states_to_return = new HashSet<S>();
        Set<Transition<S, A>> tsTransitions = ts.getTransitions();

        for (Transition<S, A> trans : tsTransitions)
        {
            S from_state = trans.getFrom();
            A action_of_transition = trans.getAction();

            if (from_state.equals(s) && action_of_transition.equals(a))
            {
                S to_state = trans.getTo();
                states_to_return.add(to_state);
            }
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a)
    {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c)
        {
            acc = post(ts, state, a);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s)
    {
        Set<S> states_to_return;
        states_to_return = preHelper(ts, s);
        return states_to_return;
    }

    private <S, A> Set<S> preHelper(TransitionSystem<S, A, ?> ts, S s)
    {
        Set<S> states_to_return = new HashSet<S>();

        Set<A> ts_actions = ts.getActions();

        Set<S> acc;
        for (A action : ts_actions)
        {
            acc = pre(ts, s, action);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c)
    {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c)
        {
            acc = pre(ts, state);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a)
    {
        Set<S> states_to_return = new HashSet<S>();

        Set<S> acc;
        for (S state : c)
        {
            acc = pre(ts, state, a);
            states_to_return.addAll(acc);
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a)
    {
        Set<S> states_to_return = new HashSet<S>();
        HashSet<Transition<S, A>> tsTransitions = (HashSet<Transition<S, A>>) ts.getTransitions();

        for (Transition<S, A> trans : tsTransitions)
        {
            A action_of_transition = trans.getAction();
            S to_state = trans.getTo();

            if (action_of_transition.equals(a) && to_state.equals(s))
            {
                S from_state = trans.getFrom();
                states_to_return.add(from_state);
            }
        }

        return states_to_return;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts)
    {
        Set<S> to_return = new HashSet<S>();

        for (S init : ts.getInitialStates())
        {
            to_return.add(init);
            to_return.addAll(reach(ts, init, to_return));
        }


        return to_return;
    }

    private <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts, S state, Set<S> to_return)
    {
        if (post(ts, state).size() == 0)
        {
            return to_return;
        } else
        {
            for (Transition<S, A> trans : ts.getTransitions())
            {
                if (trans.getFrom().equals(state))
                {
                    if (!to_return.contains(trans.getTo()))
                    {
                        to_return.add(trans.getTo());
                        reach(ts, trans.getTo(), to_return);
                    }
                }
            }
        }

        return to_return;
    }


    private <S1, S2, A> Pair<S1, S2> getNextStateS1(Set<Pair<S1, S2>> states, Transition<S1, A> transition, Pair<S1, S2> start)
    {
        Pair<S1, S2> ret = null;
        for (Pair<S1, S2> state : states)
        {
            if (state.first.equals(transition.getTo()) && state.second.equals(start.second))
            {
                ret = state;
                break;
            }

        }

        return ret;
    }

    private <S1, S2, A> Pair<S1, S2> getNextStateS2(Set<Pair<S1, S2>> states, Transition<S2, A> transition, Pair<S1, S2> start)
    {
        Pair<S1, S2> ret = null;
        for (Pair<S1, S2> state : states)
        {
            if (state.second.equals(transition.getTo()) && state.first.equals(start.first))
            {
                ret = state;
                break;
            }

        }

        return ret;
    }

    private <S1, S2, A> Pair<S1, S2> findNextState(Set<Pair<S1, S2>> states, Transition<S1, A> trans1,
                                                   Transition<S2, A> trans2)
    {
        Pair<S1, S2> ret = null;
        for (Pair<S1, S2> state : states)
        {
            if (state.first.equals(trans1.getTo()) && state.second.equals(trans2.getTo()))
            {
                ret = state;
                break;
            }

        }

        return ret;
    }

    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2)
    {
        return interleave(ts1, ts2, new HashSet<A>());
    }

    private <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleaveWithoutTransitions(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2)
    {
        TransitionSystem<Pair<S1, S2>, A, P> ret = createTransitionSystem();
        Set<A> act1 = ts1.getActions();
        Set<S1> s1 = ts1.getStates();
        Set<S1> i1 = ts1.getInitialStates();
        Set<P> ap1 = ts1.getAtomicPropositions();
        Set<A> act2 = ts2.getActions();
        Set<S2> s2 = ts2.getStates();
        Set<S2> i2 = ts2.getInitialStates();
        Set<P> ap2 = ts2.getAtomicPropositions();

        //insert states
        for (S1 state1 : s1)
            for (S2 state2 : s2)
            {
                Pair<S1, S2> state = new Pair(state1, state2);
                ret.addState(state);
            }

        //insert actions
        for (A act : act1)
        {
            ret.addAction(act);
        }

        for (A act : act2)
        {
            ret.addAction(act);
        }

        //insert Aps
        for (P ap : ap1)
        {
            ret.addAtomicProposition(ap);
        }

        for (P ap : ap2)
        {
            ret.addAtomicProposition(ap);
        }


        //insert initial states
        for (S1 state1 : i1)
            for (S2 state2 : i2)
            {
                Pair<S1, S2> state = new Pair(state1, state2);
                ret.addState(state);
                ret.addInitialState(state);
            }

        //insert labels
        Set<Pair<S1, S2>> states = ret.getStates();
        for (Pair<S1, S2> state : states)
        {
            Set<P> s1_labels = ts1.getLabel(state.first);
            Set<P> s2_labels = ts2.getLabel(state.second);
            for (P label : s1_labels) ret.addToLabel(state, label);
            for (P label : s2_labels) ret.addToLabel(state, label);
        }
        return ret;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions)
    {
        //TransitionSystem<Pair<S1, S2>, A, P> ret = interleaveWithoutTransitions(ts1, ts2);
        TransitionSystem<Pair<S1, S2>, A, P> ret = createTransitionSystem();


        Set<S1> i1 = ts1.getInitialStates();
        Set<S2> i2 = ts2.getInitialStates();
        Queue<Pair<S1, S2>> reach = new LinkedList();
        //insert initial states

        for (S1 initial1 : i1)
        {
            for (S2 initial2 : i2)
            {
                Pair<S1, S2> initial_state = new Pair(initial1, initial2);
                ret.addState(initial_state);
                ret.addInitialState(initial_state);
                reach.add(initial_state);
            }
        }

        Set<Transition<S1, A>> t1 = ts1.getTransitions();
        Set<Transition<S2, A>> t2 = ts2.getTransitions();

        while (!reach.isEmpty())
        {
            Pair<S1, S2> from = reach.poll();
            for (Transition<S1, A> trans1 : t1)
            {
                if (trans1.getFrom().equals(from.getFirst()))
                {
                    Pair<S1, S2> to = null;
                    Transition<Pair<S1, S2>, A> transition = null;
                    A action = action = trans1.getAction();
                    ;
                    if (handShakingActions.contains(trans1.getAction()))
                    {
                        for (Transition<S2, A> trans2 : t2)
                        {
                            if (trans2.getAction().equals(trans1.getAction()) && trans2.getFrom().equals(from.getSecond()))
                            {
                                to = new Pair(trans1.getTo(), trans2.getTo());
                                transition = new Transition(from, trans2.getAction(), to);
                                if (!ret.getStates().contains(to))
                                {
                                    reach.add(to);
                                    ret.addState(to);
                                }
                                ret.addAction(action);
                                ret.addTransition(transition);
                            }
                        }
                    } else
                    {
                        to = new Pair(trans1.getTo(), from.second);
                        transition = new Transition<Pair<S1, S2>, A>(from, trans1.getAction(), to);
                        if (!ret.getStates().contains(to))
                        {
                            reach.add(to);
                            ret.addState(to);
                        }
                        ret.addAction(action);
                        ret.addTransition(transition);
                    }
                }
            }
            for (Transition<S2, A> trans2 : t2)
            {
                if (trans2.getFrom().equals(from.getSecond()))
                {
                    Pair<S1, S2> to = null;
                    Transition<Pair<S1, S2>, A> transition = null;
                    A action = trans2.getAction();
                    if (!handShakingActions.contains(trans2.getAction()))
                    {
                        to = new Pair(from.first, trans2.getTo());
                        transition = new Transition<Pair<S1, S2>, A>(from, trans2.getAction(), to);
                    }
                    if (to != null)
                    {
                        if (!ret.getStates().contains(to))
                        {
                            reach.add(to);
                            ret.addState(to);
                        }
                        ret.addAction(action);
                        ret.addTransition(transition);
                    }
                }
            }
        }

        //insert labels
        Set<Pair<S1, S2>> states = ret.getStates();
        for (Pair<S1, S2> state : states)
        {
            Set<P> s1_labels = ts1.getLabel(state.first);
            Set<P> s2_labels = ts2.getLabel(state.second);
            for (P label : s1_labels)
            {
                ret.addAtomicProposition(label);
                ret.addToLabel(state, label);
            }
            for (P label : s2_labels)
            {
                ret.addAtomicProposition(label);
                ret.addToLabel(state, label);
            }
        }


        return ret;
    }

    private <S1, S2, A> Pair<S1, S2> findStartState(Set<Pair<S1, S2>> states, Transition<S1, A> trans1, Transition<S2, A> trans2)
    {
        Pair<S1, S2> ret = null;
        for (Pair<S1, S2> state : states)
        {
            if (state.first.equals(trans1.getFrom()) && state.second.equals(trans2.getFrom()))
            {
                ret = state;
                break;
            }

        }

        return ret;
    }


    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph()
    {
        return new ProgramGraphImpl<L, A>();
    }


    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2)
    {
        ProgramGraph<Pair<L1, L2>, A> ret = createProgramGraph();
        Set<L1> loc1 = pg1.getLocations();
        Set<L1> initials1 = pg1.getInitialLocations();
        Set<PGTransition<L1, A>> trans1 = pg1.getTransitions();
        Set<List<String>> initalizations1 = pg1.getInitalizations();
        Set<L2> loc2 = pg2.getLocations();
        Set<L2> initials2 = pg2.getInitialLocations();
        Set<PGTransition<L2, A>> trans2 = pg2.getTransitions();
        Set<List<String>> initalizations2 = pg2.getInitalizations();

        //insert locations
        for (L1 state1 : loc1)
            for (L2 state2 : loc2)
            {
                Pair<L1, L2> location = new Pair(state1, state2);
                ret.addLocation(location);
            }

        //insert initials
        for (L1 init1 : initials1)
            for (L2 init2 : initials2)
            {
                Pair<L1, L2> location = new Pair(init1, init2);
                ret.addInitialLocation(location);
            }

        //init preconditions
        for (List<String> initalization1 : initalizations1)
            for (List<String> initalization2 : initalizations2)
            {
                List<String> initalization = new ArrayList<>();
                initalization.addAll(initalization1);
                initalization.addAll(initalization2);
                ret.addInitalization(initalization);
            }


        Set<Pair<L1, L2>> locations = ret.getLocations();

        //add transitions
        for (PGTransition<L1, A> t1 : trans1)
            for (Pair<L1, L2> from : locations)
                if (from.first.equals(t1.getFrom()))
                {
                    Pair<L1, L2> to = findNextLoc1(locations, t1, from);
                    PGTransition<Pair<L1, L2>, A> transition = new PGTransition<Pair<L1, L2>, A>(from, t1.getCondition(), t1.getAction(), to);
                    ret.addTransition(transition);
                }

        for (PGTransition<L2, A> t2 : trans2)
            for (Pair<L1, L2> from : locations)
                if (from.second.equals(t2.getFrom()))
                {
                    Pair<L1, L2> to = findNextLoc2(locations, t2, from);
                    PGTransition<Pair<L1, L2>, A> transition = new PGTransition<Pair<L1, L2>, A>(from, t2.getCondition(), t2.getAction(), to);
                    ret.addTransition(transition);
                }


        return ret;
    }

    private <L1, L2, A> Pair<L1, L2> findNextLoc1(Set<Pair<L1, L2>> locations, PGTransition<L1, A> t1, Pair<L1, L2> from)
    {
        for (Pair<L1, L2> location : locations)
            if (location.first.equals(t1.getTo()) && location.second.equals(from.second))
                return location;
        return null;
    }

    private <L1, L2, A> Pair<L1, L2> findNextLoc2(Set<Pair<L1, L2>> locations, PGTransition<L2, A> t2, Pair<L1, L2> from)
    {
        for (Pair<L1, L2> location : locations)
            if (location.second.equals(t2.getTo()) && location.first.equals(from.first))
                return location;
        return null;
    }

    Boolean[] bitSetToArray(BitSet bs, int width)
    {
        Boolean[] result = new Boolean[width]; // all false
        for (int i = 0; i < result.length; i++) result[i] = false;
        bs.stream().forEach(i -> result[i] = true);
        return result;
    }

    List<Boolean[]> getboolList(int n)
    {
        return IntStream.range(0, (int) Math.pow(2, n))
                .mapToObj(i -> bitSetToArray(BitSet.valueOf(new long[]{i}), n))
                .collect(toList());
    }

    @Override
    public TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> transitionSystemFromCircuit(Circuit c)
    {
        TransitionSystem<Pair<List<Boolean>, List<Boolean>>, List<Boolean>, Object> ret = createTransitionSystem();
        List<String> registers_names = c.getRegisterNames();
        List<String> inputs_names = c.getInputPortNames();
        List<String> outputs_names = c.getOutputPortNames();

        //create all registers and input possible values
        List<Boolean[]> registers_values = getboolList(registers_names.size());
        List<Boolean[]> input_values = getboolList(inputs_names.size());

        //add actions
        for (Boolean[] input_option : input_values)
        {
            List<Boolean> input_option_list = new ArrayList(Arrays.asList(input_option));
            ret.addAction(input_option_list);
        }

        //add ap
        for (String s : registers_names)
            ret.addAtomicProposition(s);
        for (String s : inputs_names)
            ret.addAtomicProposition(s);
        for (String s : outputs_names)
            ret.addAtomicProposition(s);



        /*for (Boolean[] registers_value : registers_values)
            for (Boolean[] input_value : input_values)
            {
                List<Boolean> reg_vals = new ArrayList(Arrays.asList(registers_value));
                List<Boolean> input_vals = new ArrayList(Arrays.asList(input_value));
                Pair<List<Boolean>, List<Boolean>> state = new Pair(reg_vals, input_vals);
                ret.addState(state);
            }
*/



        /*Set<Pair<List<Boolean>, List<Boolean>>> states = ret.getStates();*/

        Queue<Pair<List<Boolean>, List<Boolean>>> reach = new LinkedList();
        //add initial states
        for (List<Boolean> action : ret.getActions())
        {
            List<Boolean> false_list = new ArrayList<Boolean>(registers_names.size());
            for (int i = 0; i < registers_names.size(); i++) false_list.add(false);
            Pair<List<Boolean>, List<Boolean>> state = new Pair(false_list, action);
            ret.addState(state);
            ret.addInitialState(state);
            reach.add(state);
        }

        while (!reach.isEmpty())
        {
            Pair<List<Boolean>, List<Boolean>> from = reach.poll();
            for (List<Boolean> action : ret.getActions())
            {
                List<Boolean> updated_registers = c.updateRegisters(from.first, from.second);
                Pair<List<Boolean>, List<Boolean>> to = new Pair<>(updated_registers, action);
                if (!ret.getStates().contains(to))
                {
                    ret.addState(to);
                    reach.add(to);
                }
                ret.addTransition(new Transition<>(from, action, to));
            }
        }

        //add Labels
        for (Pair<List<Boolean>, List<Boolean>> state : ret.getStates())
        {
            //add registers labels
            for (int i = 0; i < state.first.size(); i++)
                if (state.first.get(i))
                    ret.addToLabel(state, registers_names.get(i));
            //add inputs labels
            for (int i = 0; i < state.second.size(); i++)
                if (state.second.get(i))
                    ret.addToLabel(state, inputs_names.get(i));
            //add output labels
            List<Boolean> outputs = c.computeOutputs(state.first, state.second);
            for (int i = 0; i < outputs.size(); i++)
                if (outputs.get(i))
                    ret.addToLabel(state, outputs_names.get(i));
        }



        /*//add transitions
        for (Pair<List<Boolean>, List<Boolean>> from : states)
        {
            for (List<Boolean> action : ret.getActions())
            {
                List<Boolean> updated_registers = c.updateRegisters(from.first, from.second);
                //find the state with the new inputs and registers
                for (Pair<List<Boolean>, List<Boolean>> next : states)
                {
                    if (isEqual(updated_registers, next.first) && isEqual(action, next.second))
                    {
                        Transition<Pair<List<Boolean>, List<Boolean>>, List<Boolean>> transition = new Transition(from, action, next);
                        ret.addTransition(transition);
                        break;
                    }

                }
            }
        }
*/

        return ret;

    }

    private boolean isEqual(List<Boolean> l1, List<Boolean> l2)
    {
        if (l1.size() != l2.size()) return false;
        for (int i = 0; i < l1.size(); i++)
            if (l1.get(i) != l2.get(i)) return false;
        return true;
    }

    private <L, A> void labelState(TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts, Pair<L, Map<String, Object>> state)
    {
        ts.addAtomicProposition(state.first.toString());
        ts.addToLabel(state, state.first.toString());
        for (Map.Entry<String, Object> entry : state.second.entrySet())
        {
            String ap = entry.getKey().toString() + " = " + entry.getValue().toString();
            ts.addAtomicProposition(ap);
            ts.addToLabel(state, ap);
        }
    }

    private <L, A> void labelComplexState(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, Pair<List<L>, Map<String, Object>> state)
    {
        for (L location : state.first)
        {
            ts.addAtomicProposition(location.toString());
            ts.addToLabel(state, location.toString());
        }
        for (Map.Entry<String, Object> entry : state.second.entrySet())
        {
            String ap = entry.getKey().toString() + " = " + entry.getValue().toString();
            ts.addAtomicProposition(ap);
            ts.addToLabel(state, ap);
        }
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs)
    {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ret = createTransitionSystem();
        Set<PGTransition<L, A>> transitions = pg.getTransitions();
        Set<List<String>> initializations = pg.getInitalizations();

        Set<L> initial_locations = pg.getInitialLocations();
        Queue<Pair<L, Map<String, Object>>> reach = new LinkedList();

        //add initial states
        for (L initial_location : initial_locations)
        {
            boolean flag = true;
            for (List<String> conditions : initializations)
            {
                flag = false;
                Map<String, Object> initial_eval = new HashMap<>();
                for (String cond : conditions)
                {
                    initial_eval = ActionDef.effect(actionDefs, initial_eval, cond);

                }
                Pair<L, Map<String, Object>> state = new Pair<L, Map<String, Object>>(initial_location, initial_eval);
                ret.addState(state);
                ret.addInitialState(state);
                reach.add(state);

                labelState(ret, state);
            }

            if (flag)
            {
                Map<String, Object> initial_eval = new HashMap<>();
                Pair<L, Map<String, Object>> state = new Pair<L, Map<String, Object>>(initial_location, initial_eval);
                ret.addState(state);
                ret.addInitialState(state);
                reach.add(state);
                labelState(ret, state);
            }

        }

        while (!reach.isEmpty())
        {
            Pair<L, Map<String, Object>> from = reach.poll();
            for (PGTransition<L, A> transition : transitions)
            {
                if (transition.getFrom().equals(from.first) && ConditionDef.evaluate(conditionDefs, from.second, transition.getCondition()))
                {
                    //  ret.addAtomicProposition(transition.getCondition());
                    ret.addAction(transition.getAction());
                    Pair<L, Map<String, Object>> to = new Pair<L, Map<String, Object>>(transition.getTo(), ActionDef.effect(actionDefs, from.second, transition.getAction()));
                    if (!ret.getStates().contains(to))
                    {
                        ret.addState(to);
                        reach.add(to);
                    }
                    ret.addTransition(new Transition<Pair<L, Map<String, Object>>, A>(from, transition.getAction(), to));

                    labelState(ret, to);
                }
            }
        }


        return ret;

    }

    public static <E> List<E> generateFlatPerm(List<Set<E>> original)
    {
        List<Set<E>> copy = new ArrayList<>(original);
        List<List<E>> copy_perm = generatePerm(copy);
        List<E> flat = flat_list(copy_perm);
        return flat;
    }

    public static <E> List<E> flat_list(List<List<E>> flat)
    {
        List<E> ret = new ArrayList<E>();
        for (List<E> list : flat)
            ret.addAll(list);
        return ret;
    }

    public static <E> List<List<E>> generatePerm(List<Set<E>> original)
    {
        if (original.size() == 0)
        {
            List<List<E>> result = new ArrayList<List<E>>();
            result.add(new ArrayList<E>());
            return result;
        }
        Set<E> firstElement = original.remove(0);
        List<List<E>> returnValue = new ArrayList<List<E>>();
        List<List<E>> permutations = generatePerm(original);
        for (List<E> smallerPermutated : permutations)
        {
            if (firstElement.size() == 0)
            {
                returnValue.add(smallerPermutated);
            } else
            {
                for (E element : firstElement)
                {
                    List<E> temp = new ArrayList<E>(smallerPermutated);
                    temp.add(0, element);
                    returnValue.add(temp);
                }
            }
        }
        return returnValue;
    }


    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut)
    {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> ret = createTransitionSystem();
        Set<Sts> ts_initial_states = ts.getInitialStates();
        Iterable<Saut> auto_inital_states = aut.getInitialStates();
        Queue<Pair<Sts, Saut>> reach = new LinkedList<>();

        //initialize initial states
        for (Sts ts_initial : ts_initial_states)
        {
            Set<P> state_atomic_prop = ts.getLabel(ts_initial);
            for (Saut auto_initial : auto_inital_states)
            {
                Set<Saut> next_aut_states = aut.nextStates(auto_initial, state_atomic_prop);
                ret.addAllAtomicPropositions(next_aut_states);
                for (Saut next_state : next_aut_states)
                {
                    Pair<Sts, Saut> initial_state = new Pair(ts_initial, next_state);
                    ret.addState(initial_state);
                    ret.addInitialState(initial_state);
                    reach.add(initial_state);
                    ret.addToLabel(initial_state, initial_state.second);
                }
            }
        }
        while (!reach.isEmpty())
        {
            Pair<Sts, Saut> head = reach.poll();
            Set<Transition<Sts, A>> transitions = getTransitions(head, ts);
            for (Transition<Sts, A> transition : transitions)
            {
                Set<P> state_atomic_prop = ts.getLabel(transition.getTo());
                Set<Saut> next_aut_states = aut.nextStates(head.getSecond(), state_atomic_prop);
                if(next_aut_states!=null)
                {
                    ret.addAllAtomicPropositions(next_aut_states); // add all atomic prop
                    for (Saut state : next_aut_states)
                    {
                        Pair<Sts, Saut> next_state = new Pair<Sts, Saut>(transition.getTo(), state);
                        if (!ret.getStates().contains(next_state))
                        {
                            ret.addState(next_state);
                            reach.add(next_state);
                        }
                        ret.addToLabel(next_state, next_state.second); // add labels to state
                        ret.addAction(transition.getAction());
                        ret.addTransition(new Transition<Pair<Sts, Saut>, A>(head, transition.getAction(), next_state));
                    }
                }
            }
        }
        return ret;
    }

    private <Sts, Saut, A, P> Set<Transition<Sts, A>> getTransitions(Pair<Sts, Saut> head, TransitionSystem<Sts, A, P> ts)
    {

        Set<Transition<Sts, A>> transitions = ts.getTransitions();
        Set<Transition<Sts, A>> ret = transitions.stream().
                filter(transition -> transition.getFrom().equals(head.first)).collect(Collectors.toSet());
        return ret;
    }


    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs)
    {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret = createTransitionSystem();
        List<ProgramGraph<L, A>> program_graphs = cs.getProgramGraphs();

        //combine all initializations
        List<Set<List<String>>> initializations = new ArrayList<>();
        for (ProgramGraph<L, A> pg : program_graphs)
        {
            initializations.add(pg.getInitalizations());

        }

        //combine all initial locations
        List<Set<L>> initial_locations = new ArrayList<>();
        for (ProgramGraph<L, A> pg : program_graphs)
        {
            initial_locations.add(pg.getInitialLocations());
        }

        List<List<String>> initializations_permutations = generateFlatPerm(initializations);

        // Normal parser for normal operation and unlimited channel.
        Set<ActionDef> actionDefs = new HashSet<>();
        InterleavingActDef actionDef = new ParserBasedInterleavingActDef();
        actionDefs.add(actionDef);
        actionDefs.add(new ParserBasedActDef());

        // for zero capacity channel.
        Set<ActionDef> complexActionDefSet = new HashSet<>();
        complexActionDefSet.add(new ParserBasedInterleavingActDef());

        // for conditions
        ConditionDef conditionDef = new ParserBasedCondDef();
        Set<ConditionDef> conditionDefs = new HashSet<>();
        conditionDefs.add(conditionDef);


        Set<Map<String, Object>> initials_actions = generate_initial_actions(initializations_permutations, actionDefs);

        List<List<L>> initial_locations_permutations = generatePerm(initial_locations);

        Set<Pair<List<L>, Map<String, Object>>> initials_states = generate_initial_states(initial_locations_permutations, initials_actions);
        Queue<Pair<List<L>, Map<String, Object>>> reach = new LinkedList();

        //add all states as initial states and add atomic propositions.
        for (Pair<List<L>, Map<String, Object>> state : initials_states)
        {
            ret.addState(state);
            ret.addInitialState(state);
            reach.add(state);

            labelComplexState(ret, state);

        }

        while (!reach.isEmpty())
        {
            Pair<List<L>, Map<String, Object>> from = reach.poll();
            Map<Integer, List<PGTransition<L, A>>> simultaneous_actions = new HashMap<>();
            for (int i = 0; i < program_graphs.size(); i++)
            {
                ProgramGraph<L, A> current_pg = program_graphs.get(i);
                L current_location = from.getFirst().get(i);
                //iterate over all transitions to find those who are from "from" location and all the conditions are passed.
                for (PGTransition<L, A> pgTransition : current_pg.getTransitions())
                {
                    if (pgTransition.getFrom().equals(current_location)
                            && ConditionDef.evaluate(conditionDefs, from.second, pgTransition.getCondition()))
                    {
                        //we need to check if the action is one-sided or not
                        A action = pgTransition.getAction();
                        if (!actionDef.isOneSidedAction(action.toString()))
                        {
                            // create new location when the i-location is changed.
                            List<L> new_location = new ArrayList<>(from.first);
                            new_location.set(i, pgTransition.getTo());
                            handleTransition(ret, actionDefs, reach, from, action, new_location);
                        } else
                        {
                            if (!simultaneous_actions.containsKey(i))
                            {
                                simultaneous_actions.put(i, new ArrayList<>());
                            }
                            simultaneous_actions.get(i).add(pgTransition);
                        }
                    }
                }
                if (simultaneous_actions.size() > 0)
                {
                    // build list of all possible operation in order to calc permutation.
                    List<Set<Pair<Integer, PGTransition<L, A>>>> allComplexTransitions = new ArrayList<>();
                    for (Integer key : simultaneous_actions.keySet())
                    {
                        List<PGTransition<L, A>> transitions = simultaneous_actions.get(key);
                        Set<Pair<Integer, PGTransition<L, A>>> set = new HashSet<>();
                        for (PGTransition<L, A> transition : transitions)
                        {
                            set.add(new Pair<>(key, transition));
                        }
                        allComplexTransitions.add(set);
                    }
                    // compute permutation.
                    List<List<Pair<Integer, PGTransition<L, A>>>> allComplexTransitionPermutations = generatePerm(allComplexTransitions);
                    // for each permutation, we will check all the possible executions.
                    for (List<Pair<Integer, PGTransition<L, A>>> complexTransition : allComplexTransitionPermutations)
                    {
                        // handle the complex operation by creating merging them:
                        StringBuilder action = new StringBuilder();
                        List<L> newLocation = new ArrayList<>(from.first);
                        List<A> actions = new ArrayList<>();
                        for (Pair<Integer, PGTransition<L, A>> pair : complexTransition)
                        {
                            if (action.length() != 0)
                            {
                                action.append("|");
                            }
                            action.append(pair.second.getAction());
                            actions.add(pair.second.getAction());
                            newLocation.set(pair.first, pair.second.getTo());
                        }
                        // we have the newLocation and a join action,
                        // we will handle the transition
                        if (!actionDef.isOneSidedAction(actions.toString()) && complexTransition.size() > 1)
                        {
                            handleTransition(ret, complexActionDefSet, reach, from, (A) action.toString(), newLocation);
                        }
                    }
                }
            }
        }


        //throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
        return ret;
    }

    private <L, A> void handleTransition(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret, Set<ActionDef> actionDefs, Queue<Pair<List<L>, Map<String, Object>>> reach, Pair<List<L>, Map<String, Object>> state, A action, List<L> new_location)
    {
        Map<String, Object> newEval = ActionDef.effect(actionDefs, state.second, action);
        if (newEval != null)
        {
            Pair<List<L>, Map<String, Object>> newState = new Pair<>(new_location, newEval);
            Transition<Pair<List<L>, Map<String, Object>>, A> transition = new Transition<>(state, action, newState);
            if (!ret.getStates().contains(newState))
            {
                reach.add(newState);
                ret.addState(newState);
            }
            ret.addAction(action);
            ret.addTransition(transition);
            labelComplexState(ret, newState);
        }
    }

    private <L, A> Pair<List<L>, Map<String, Object>> create_state(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret, Set<ActionDef> actionDefs, Pair<List<L>, Map<String, Object>> state, A action, List<L> new_location)
    {

        Map<String, Object> eval = ActionDef.effect(actionDefs, state.second, action);
        if (eval != null)
        {
            return new Pair<>(new_location, eval);
        }
        return null;
    }

    private <L> Set<Pair<List<L>, Map<String, Object>>> generate_initial_states(List<List<L>> initial_locations_permutations, Set<Map<String, Object>> initials_actions)
    {
        Set<Pair<List<L>, Map<String, Object>>> ret = new HashSet<>();
        for (List<L> location : initial_locations_permutations)
            for (Map<String, Object> initial_action : initials_actions)
                ret.add(new Pair(location, initial_action));
        return ret;
    }

    private static Set<Map<String, Object>> generate_initial_actions(List<List<String>> initializations, Set<ActionDef> actionDefs)
    {
        Set<Map<String, Object>> ret = new HashSet<>();
        for (List<String> initialization : initializations)
        {
            Map<String, Object> eval = new HashMap<>();
            for (String action : initialization)
            {
                eval = ActionDef.effect(actionDefs, eval, action);
            }
            ret.add(eval);
        }
        if (ret.size() == 0)
        {
            ret.add(new HashMap<>());
        }
        return ret;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception
    {

        StmtContext root = NanoPromelaFileReader.pareseNanoPromelaFile(filename);

        ProgramGraph<String, String> pg = pgFromRoot(root);

        return pg;

    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception
    {
        StmtContext root = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);

        ProgramGraph<String, String> pg = pgFromRoot(root);

        return pg;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception
    {
        StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        ProgramGraph<String, String> pg = pgFromRoot(root);

        return pg;
    }


    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut)
    {
        Queue<Pair<S, Saut>> to_iterate = new LinkedList();
        Set<Pair<S, Saut>> R = new HashSet();
        Stack<Pair<S,Saut>> U = new Stack<>();
        Stack<Pair<S,Saut>> V = new Stack();
        Set<Pair<S, Saut>> T = new HashSet();
        Boolean flag = new Boolean(false);


        TransitionSystem<Pair<S, Saut>, A, Saut> product = product(ts, aut);
        to_iterate.addAll(product.getInitialStates());

        while (to_iterate.size() > 0 && !flag)
        {
            Pair<S, Saut> state = to_iterate.poll();
            if (!R.contains(state))
                flag = reachable_cycle(state,R,U,V,T,product,aut);
        }

        if(flag)
        {
            VerificationFailed result = new VerificationFailed();
            List<Pair<S,Saut>> l = new ArrayList();
            l.addAll(U);
            l.addAll(V);

            Pair<S,Saut> dup = l.get(l.size()-1);
            int first_appear = l.indexOf(dup);
            List<Pair<S,Saut>> unclear_prefix = l.subList(0,first_appear);
            List<Pair<S,Saut>> unclear_circle = l.subList(first_appear,l.size()-1);
            List prefix = new ArrayList();
            List circle = new ArrayList();
            for(Pair<S,Saut> state : unclear_prefix)
            {
                prefix.add(state.first);
            }
            for(Pair<S,Saut> state : unclear_circle)
            {
                circle.add(state.first);
            }
            result.setCycle(circle);
            result.setPrefix(prefix);
            return result;
        }
        else
            return new VerificationSucceeded<S>();

    }

    private <S, Saut> boolean reachable_cycle(Pair<S, Saut> state, Set<Pair<S, Saut>> r, Stack<Pair<S, Saut>> u, Stack<Pair<S, Saut>> v, Set<Pair<S, Saut>> t, TransitionSystem<Pair<S, Saut>, ?, Saut> product, Automaton<Saut, ?> aut)
    {
        boolean flag = false;
        u.push(state);
        r.add(state);
        Set<Saut> accpent_aut_states= aut.getAcceptingStates();
        while(u.size() > 0 && !flag)
        {
            Pair<S, Saut> s_tag = u.peek();
            Set<Pair<S,Saut>> post_s_tag = post(product,s_tag);
            post_s_tag.removeAll(r);
            if(post_s_tag.size() > 0)
            {
                Pair<S, Saut> s_tag_tag = (Pair<S, Saut>) post_s_tag.toArray()[0];
                u.push(s_tag_tag);
                r.add(s_tag_tag);
            }
            else
            {
                u.pop();
                if(accpent_aut_states.contains(s_tag.second))
                {
                    flag = cycle_check(s_tag,product,v,t);
                }
            }
        }
        return flag;
    }


    private <S, Saut> boolean cycle_check(Pair<S, Saut> state, TransitionSystem<Pair<S, Saut>, ?, ?> ts, Stack<Pair<S,Saut>> V,Set<Pair<S,Saut>> T)
    {
        boolean cycle_found = false;
        T.add(state);
        V.add(state);
        while(V.size() > 0)
        {
            Pair<S,Saut> s_tag = V.peek();
            Set<Pair<S,Saut>> post_s_tag = post(ts,s_tag);
            if(post_s_tag.contains(state))
            {
                cycle_found = true;
                break;
            }
            else
            {
                post_s_tag.removeAll(T);
                if(!post_s_tag.isEmpty())
                {
                    Pair<S, Saut> s_tag_tag = (Pair<S, Saut>) post_s_tag.toArray()[0];
                    V.push(s_tag_tag);
                    T.add(s_tag_tag);
                }
                else
                {
                    V.pop();
                }
            }
        }
        return  cycle_found;
    }


    private <S, A, P, Saut> void visit(Pair<S, Saut> state, Set<Pair<S, Saut>> accept_states, Set<Pair<S, Saut>> reach, TransitionSystem<Pair<S, Saut>, A, Saut> ts,Automaton<Saut, P> aut)
    {
        Stack<Pair<S, Saut>> U = new Stack();
        Set<Saut> aut_accept_states= aut.getAcceptingStates();
        U.push(state);
        reach.add(state);
        while(U.size()>0)
        {
            Pair<S, Saut> s_tag = U.peek();
            Set<Pair<S, Saut>> post_s_tag = post(ts,s_tag);
            if(reach.containsAll(post_s_tag))
            {
                U.pop();
                if(aut_accept_states.contains(s_tag.second))
                    accept_states.add(s_tag);
            }
            else
            {
                post_s_tag.removeAll(reach);
                Pair<S, Saut> s_tag_tag = (Pair<S, Saut>) post_s_tag.toArray()[0];
                U.push(s_tag_tag);
                reach.add(s_tag_tag);
            }
        }
    }

    private ProgramGraph<String, String> pgFromRoot(StmtContext root)
    {

        ProgramGraph<String, String> pg = createProgramGraph();

        HashSet<String> loc = new HashSet<String>();
        loc = sub(root, loc, pg);

        for (String locToAdd : loc)
        {
            pg.addLocation(locToAdd);
        }

        pg.addInitialLocation(root.getText());
        HashSet<String> reachableLocs = reachableOnly(pg);

        for (String locToRemove : pg.getLocations())
        {
            pg.removeLocation(locToRemove);
        }

        for (String locToAdd : reachableLocs)
        {
            pg.addLocation(locToAdd);
        }
        pg.addInitialLocation(root.getText());

        removeWasteTrans(pg);

        return pg;

    }

    private void removeWasteTrans(ProgramGraph<String, String> pg)
    {
        Set<PGTransition<String, String>> transitions = pg.getTransitions();
        Set<String> locations = pg.getLocations();

        for (PGTransition<String, String> trans : transitions)
        {
            if (locations.contains(trans.getFrom()) && locations.contains(trans.getTo()))
            {

            } else
            {
                pg.removeTransition(trans);
            }
        }

    }

    private HashSet<String> reachableOnly(ProgramGraph<String, String> pg)
    {
        Set<String> initialLocs = pg.getInitialLocations();

        HashSet<String> toReturn = new HashSet<String>();

        for (String loc : initialLocs)
        {
            toReturn.add(loc);
            toReturn.addAll(reachableOnly(pg, toReturn, loc));
        }

        return toReturn;
    }

    private Set<String> reachableOnly(ProgramGraph<String, String> pg, Set<String> toReturn, String loc)
    {
        Set<PGTransition<String, String>> transitions = pg.getTransitions();

        boolean flag = false;

        for (PGTransition<String, String> trans : transitions)
        {
            if (trans.getFrom().equals(loc))
            {
                flag = true;
                if (!toReturn.contains(trans.getTo()))
                {
                    toReturn.add(trans.getTo());
                    reachableOnly(pg, toReturn, trans.getTo());
                }
            }
        }
        if (flag == false)
        {
            return toReturn;
        }
        return toReturn;
    }

    private HashSet<String> sub(StmtContext root, HashSet<String> loc, ProgramGraph<String, String> pg)
    {

        if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null ||
                root.atomicstmt() != null || root.skipstmt() != null)
        {
            loc.add("");
            loc.add(root.getText());

            if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null)
            {
                PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", root.getText(), "");
                pg.addTransition(t);
            } else if (root.atomicstmt() != null)
            {

                PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", root.getText(), "");
                pg.addTransition(t);
            } else if (root.skipstmt() != null)
            {
                PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", "skip", "");
                pg.addTransition(t);
            }
        } else if (root.ifstmt() != null)
        {
//			System.out.println(root.);
            loc.add(root.getText());

            List<OptionContext> options = root.ifstmt().option();

            for (OptionContext option : options)
            {
                HashSet<String> emptyLoc = new HashSet<String>();
                loc.addAll(sub(option.stmt(), emptyLoc, pg));
            }

            Set<PGTransition<String, String>> transitions = pg.getTransitions(); //trans so far

            for (OptionContext option : options)
            {
                String fromToCheck = option.stmt().getText();

                for (PGTransition<String, String> trans : transitions)
                {
                    if (trans.getFrom().equals(fromToCheck))
                    {
                        PGTransition<String, String> t;
                        if (!(trans.getCondition().equals("")))
                        {
                            t = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ") && (" + trans.getCondition() + ")", trans.getAction(), trans.getTo());
                        } else
                        {
                            t = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ")", trans.getAction(), trans.getTo());
                        }
                        pg.addTransition(t);
                    }
                }
            }

        } else if (root.dostmt() != null)
        {
            loc.add(root.getText());
            loc.add("");

            List<OptionContext> options = root.dostmt().option();
            for (OptionContext option : options)
            { //need to check if .stmt() is needed
                HashSet<String> emptyLoc = new HashSet<String>();
                HashSet<String> temp = sub(option.stmt(), emptyLoc, pg);
                temp.remove("");

                String loopStmtWithSpaces = addSpaces(root.getText());
                for (String str : temp)
                {
                    loc.add(str + ";" + root.getText());

                    String strWithSpaces = addSpaces(str);
                    String s = strWithSpaces + " ; " + loopStmtWithSpaces;
                    StmtContext secondRoot = NanoPromelaFileReader.pareseNanoPromelaString(s);

                    addAdditionalTransactions(secondRoot, pg);
                }
            }
            //first cond
            String allRules = "(";
            for (OptionContext option : options)
            {
                allRules = allRules + option.boolexpr().getText() + ")||(";
            }
            allRules = allRules.substring(0, allRules.length() - 3);
            PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "!(" + allRules + ")", "", "");
            pg.addTransition(t);

            //second cond
            Set<PGTransition<String, String>> transitions = pg.getTransitions();

            for (OptionContext option : options)
            {
                String fromToCheck = option.stmt().getText();

                for (PGTransition<String, String> trans : transitions)
                {
                    if (trans.getFrom().equals(fromToCheck) && trans.getTo().equals(""))
                    {
                        PGTransition<String, String> t2;
                        if (!(trans.getCondition().equals("")))
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ") && (" + trans.getCondition() + ")", trans.getAction(), root.getText());
                        } else
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ")", trans.getAction(), root.getText());
                        }
                        pg.addTransition(t2);
                    } else if (trans.getFrom().equals(fromToCheck) && !(trans.getTo().equals("")))
                    {
                        PGTransition<String, String> t2;
                        if (!(trans.getCondition().equals("")))
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ") && (" + trans.getCondition() + ")", trans.getAction(), trans.getTo() + ";" + root.getText());
                        } else
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ")", trans.getAction(), trans.getTo() + ";" + root.getText());
                        }
                        pg.addTransition(t2);
                    }
                }
            }

        } else
        { // ;
            HashSet<String> emptyLoc1 = new HashSet<String>();
            loc.addAll(sub(root.stmt(1), emptyLoc1, pg));

            HashSet<String> emptyLoc0 = new HashSet<String>();
            HashSet<String> temp = sub(root.stmt(0), emptyLoc0, pg);
            temp.remove("");
            String secondStmtWithSpaces = addSpaces(root.stmt(1).getText());

            for (String str : temp)
            {

                loc.add(str + ";" + root.stmt(1).getText());

                String strWithSpaces = addSpaces(str);
                String s = strWithSpaces + " ; " + secondStmtWithSpaces;
                StmtContext secondRoot = NanoPromelaFileReader.pareseNanoPromelaString(s);

                addAdditionalTransactions(secondRoot, pg);

            }

            Set<PGTransition<String, String>> transitions = pg.getTransitions();

            for (PGTransition<String, String> trans : transitions)
            {
                String toCheck = root.stmt(0).getText();
                if (trans.getFrom().equals(toCheck) && trans.getTo().equals(""))
                {
                    PGTransition<String, String> t =
                            new PGTransition<String, String>(root.getText(), trans.getCondition(), trans.getAction(), root.stmt(1).getText());
                    pg.addTransition(t);
                } else if (trans.getFrom().equals(toCheck) && !(trans.getTo().equals("")))
                {
                    PGTransition<String, String> t =
                            new PGTransition<String, String>(root.getText(), trans.getCondition(), trans.getAction(), trans.getTo() + ";" + root.stmt(1).getText());
                    pg.addTransition(t);
                }
            }
        }

        return loc;
    }


    private void addAdditionalTransactions(StmtContext secondRoot, ProgramGraph<String, String> pg)
    {
        Set<PGTransition<String, String>> transitions = pg.getTransitions();

        for (PGTransition<String, String> trans : transitions)
        {
            String toCheck = secondRoot.stmt(0).getText();
            if (trans.getFrom().equals(toCheck) && trans.getTo().equals(""))
            {
                PGTransition<String, String> t =
                        new PGTransition<String, String>(secondRoot.getText(), trans.getCondition(), trans.getAction(), secondRoot.stmt(1).getText());
                pg.addTransition(t);
            } else if (trans.getFrom().equals(toCheck) && !(trans.getTo().equals("")))
            {
                PGTransition<String, String> t =
                        new PGTransition<String, String>(secondRoot.getText(), trans.getCondition(), trans.getAction(), trans.getTo() + ";" + secondRoot.stmt(1).getText());
                pg.addTransition(t);
            }
        }

    }

    private String addSpaces(String str)
    {
        str = str.replace("nsoda", "sagivmapgavker");
        str = str.replace("fi", " fi");
        str = str.replace("if", "if ");
        str = str.replace("od", " od");
        str = str.replace("do", "do ");
        str = str.replace("::", ":: ");


        str = str.replace("->", " -> ");
        str = str.replace("skip", " skip");
        str = str.replace("atomic", "atomic ");
        str = str.replace("sagivmapgavker", "nsoda");
        return str;
    }


}
