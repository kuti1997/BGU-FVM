package il.ac.bgu.cs.fvm.examples;

import java.util.LinkedList;
import java.util.List;

import il.ac.bgu.cs.fvm.circuits.Circuit;
import static java.util.Arrays.asList;

/**
 * The circuit on page 27, Figure 2.2
 */
public class ExampleCircuit implements Circuit {

    /**
     * Implements the relation r = x \/ r
     *
     */
    @Override
    public List<Boolean> updateRegisters(List<Boolean> registers, List<Boolean> inputs) {
        List<Boolean> r = new LinkedList<>();
        r.add(registers.get(0) || inputs.get(0));
        return r;
    }

    /**
     * Implements the relation y = not(x XOR r)
     *
     */
    @Override
    public List<Boolean> computeOutputs(List<Boolean> registers, List<Boolean> inputs) {
        List<Boolean> y = new LinkedList<>();
        y.add(!(registers.get(0) ^ inputs.get(0)));
        return y;
    }

    @Override
    public List<String> getInputPortNames() {
        return asList("x");
    }

    @Override
    public List<String> getRegisterNames() {
        return asList("r");
    }

    @Override
    public List<String> getOutputPortNames() {
        return asList("y");
    }

}
