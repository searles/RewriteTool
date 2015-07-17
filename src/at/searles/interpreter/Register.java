package at.searles.interpreter;

/**
 * Created by searles on 05.05.15.
 */
public interface Register {
    void set(Register r); // throws an exception if r is not same class as this
}
