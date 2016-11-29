package il.ac.bgu.cs.fvm.util;

import java.util.Objects;

/**
 * A 2-tuple.
 * 
 * @param <FIRST>
 * @param <SECOND>
 */
public class Pair<FIRST, SECOND> {
    
    public final FIRST first;
    public final SECOND second;
    
    public static <X,Y> Pair<X,Y> pair( X x, Y y) {
        return new Pair<>(x,y);
    }
    
    public Pair(FIRST anX, SECOND aY) {
        first = anX;
        second = aY;
    }

    public FIRST getFirst() {
        return first;
    }

    public SECOND getSecond() {
        return second;
    }
    
    @Override
    public String toString() {
        return String.format("<%s,%s>", first, second);
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 97 * hash + Objects.hashCode(this.first);
        hash = 97 * hash + Objects.hashCode(this.second);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (! (obj instanceof Pair)) {
            return false;
        }
        final Pair<?, ?> other = (Pair<?, ?>) obj;
        
        return Objects.equals(this.first, other.first)
                && Objects.equals(this.second, other.second);
    }
    
}
