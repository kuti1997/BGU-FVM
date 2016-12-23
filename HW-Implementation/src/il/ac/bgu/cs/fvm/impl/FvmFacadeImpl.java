package il.ac.bgu.cs.fvm.impl;

import entities.ProgramGraphImpl;
import entities.TransitionSystemImpl;
import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

import java.io.InputStream;
import java.util.*;
import java.util.function.Predicate;
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
        //TODO:: what happen if there is a actions without state? like s1 a1 s2 a2
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
        TransitionSystem<Pair<S1, S2>, A, P> ret = interleaveWithoutTransitions(ts1, ts2);
        Set<Transition<S1, A>> t1 = ts1.getTransitions();
        Set<Transition<S2, A>> t2 = ts2.getTransitions();
        Set<Pair<S1, S2>> states = ret.getStates();

        //insert transitions

        //insert hadshaking
        for (Transition<S1, A> trans1 : t1)
        {
            A action = trans1.getAction();
            if (handShakingActions.contains(action))
            {
                for (Transition<S2, A> trans2 : t2)
                {
                    if (trans2.getAction().equals(action))
                    {
                        Pair<S1, S2> from = findStartState(states, trans1, trans2);
                        Pair<S1, S2> to = findNextState(states, trans1, trans2);
                        Transition<Pair<S1, S2>, A> transition = new Transition(from, action, to);
                        ret.addTransition(transition);
                    }
                }
            }
        }

        //insert only ts1
        for (Transition<S1, A> trans1 : t1)
        {
            if (!handShakingActions.contains(trans1.getAction()))
            {
                for (Pair<S1, S2> state : states)
                {
                    if (trans1.getFrom().equals(state.first))
                    {
                        Pair<S1, S2> next = getNextStateS1(states, trans1, state);
                        if (next == null)
                            System.out.println("Should not happen. Error");
                        Transition transition = new Transition(state, trans1.getAction(), next);
                        ret.addTransition(transition);
                    }
                }
            }
        }

        //insert only ts2
        for (Transition<S2, A> trans2 : t2)
        {
            if (!handShakingActions.contains(trans2.getAction()))
            {
                for (Pair<S1, S2> state : states)
                {
                    if (trans2.getFrom().equals(state.second))
                    {
                        Pair<S1, S2> next = getNextStateS2(states, trans2, state);
                        if (next == null)
                            System.out.println("Should not happen. Error");
                        Transition transition = new Transition(state, trans2.getAction(), next);
                        ret.addTransition(transition);
                    }
                }
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

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs)
    {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, P> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut)
    {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs)
    {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception
    {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception
    {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception
    {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }


}
