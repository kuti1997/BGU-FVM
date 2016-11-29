package il.ac.bgu.cs.fvm.circuits;

import java.util.List;

/**
 * An interface for an abstract representation of logic circuits.
 */
public interface Circuit {

    /**
     * A method that returns a list of names of the input ports.
     *
     * @return A list of objects representing the names of the input ports.
     */
    List<String> getInputPortNames();

    /**
     * A method that returns a list of names of the registers.
     *
     * @return A list of objects representing the names of the registers.
     */
    List<String> getRegisterNames();

    /**
     * A method that returns a list of names of the output ports
     *
     * @return A list of objects representing the names of the output ports.
     */
    List<String> getOutputPortNames();

    /**
     * A method that updates the values of the registers based on the values of
     * the inputs and the current values of the registers. The Lengths of the
     * Boolean lists are expected to be of the same length as the lengths of
     * the corresponding name lists.
     *
     * @param registers
     * @param inputs
     * @return New register values.
     */
    public List<Boolean> updateRegisters(List<Boolean> registers, List<Boolean> inputs);

    /**
     * A method that updates the values of the registers based on the values of
     * the inputs and the current values of the registers. The Lengths of the
     * Boolean lists are expected to be of the same length as the lengths of the
     * corresponding name lists.
     *
     * @param registers A list representing the truth value of each register.
     * @param inputs A list representing the truth value of each output.
     * @return Output values.
     */
    public List<Boolean> computeOutputs(List<Boolean> registers, List<Boolean> inputs);
}
