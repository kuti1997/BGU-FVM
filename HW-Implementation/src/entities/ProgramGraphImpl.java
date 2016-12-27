package entities;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Created by tomarlin on 21/12/16.
 */
public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A>
{
    private Set<L> locations;
    private Set<L> initial_locations;
    private Set<PGTransition<L, A>> transitions;
    private String name;
    private Set<List<String>> initalization;

    public ProgramGraphImpl()
    {
        this.locations = new HashSet<L>();
        this.initial_locations = new HashSet<L>();
        this.transitions = new HashSet<PGTransition<L, A>>();
        this.initalization = new HashSet<List<String>>();
    }

    public ProgramGraphImpl(String name)
    {
        this();
        this.name = name;
    }


    public void addInitalization(List<String> init)
    {
        initalization.add(init);
    }

    public void addInitialLocation(L location)
    {
        this.locations.add(location); //maybe not need to insert.
        this.initial_locations.add(location);
    }

    public void addLocation(L l)
    {
        this.locations.add(l);
    }

    public void addTransition(PGTransition<L, A> t)
    {
        this.transitions.add(t);
    }

    public Set<List<String>> getInitalizations()
    {
        return new HashSet<List<String>>(this.initalization);
    }

    public Set<L> getInitialLocations()
    {
        return new HashSet<L>(this.initial_locations);
    }

    public Set<L> getLocations()
    {
        return new HashSet<L>(this.locations);
    }

    public String getName()
    {
        return this.name;
    }

    public Set<PGTransition<L, A>> getTransitions()
    {
        return new HashSet<PGTransition<L, A>>(this.transitions);
    }

    public void removeLocation(L l)
    {
        this.initial_locations.remove(l);
        this.locations.remove(l);
    }

    public void removeTransition(PGTransition<L, A> t)
    {
        this.transitions.remove(t);
    }

    public void setName(String name)
    {
        this.name = name;
    }
    
    public void addAllLocations(HashSet<L>  locs){
    	this.locations.addAll(locs);
    }
}
