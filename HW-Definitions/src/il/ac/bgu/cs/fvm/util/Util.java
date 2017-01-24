package il.ac.bgu.cs.fvm.util;

import java.util.LinkedList;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * Utility methods helping the course staff implementation.
 * <p>
 */
public class Util {

    public static <T1, T2> Set<Pair<T1, T2>> getPairs(Set<T1> s1, Set<T2> s2) {
        Stream<Pair<T1,T2>> str = s1.stream().flatMap(e1 -> s2.stream().map(e2 -> new Pair<>(e1, e2))); //
        return str.collect(Collectors.toSet());
    }
    
	public static <T> Set<Set<T>> powerSet(Set<T> aset) {
		LinkedList<T> set = new LinkedList<>(aset);
		IntStream range = IntStream.range(0, (int) Math.pow(2, set.size()));

		Stream<Set<T>> stream = range.parallel().mapToObj(e -> {
			IntStream range2 = IntStream.range(0, set.size());
			return range2.filter(i -> (e & (0b1 << i)) != 0).mapToObj(i -> set.get(i)).collect(Collectors.toSet());
		});

		return stream.map(Function.identity()).collect(Collectors.toSet());
	}

}
