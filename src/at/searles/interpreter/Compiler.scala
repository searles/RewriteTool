package at.searles.interpreter

import at.searles.kart.terms.Term

class Compiler {
	//val cache = Map.empty[Int, Register]
	//val statements = List[Statement]

	// FIXME: Write interpreter in RenderScript

	// Every term corresponds to a value
	// This value can then be cached for further use
	// unless it is actually a mutable value like an
	// iterator. In the latter case, it should not be
	// cached.

	// In general, a register can be a
	// * variable holding a number
	// * iterator allowing iterating through other values
	//   - in this case, the iterator contains one counter-register
	//   - iterators are created by ranges
	// * loops can be modeled as functions:
	//   - (1 to 10).fold(init_value)((x,y) -> x*x+y*y)
	//   - while(init_value).((x) -> condition)
	// * non-recursive functions that can be executed on demand
	//   - in this case, the function contains registers representing the return value and the arguments
	//   - not really necessary because they can easily be handled by inlining
	// * recursive functions
	//   - in this case, the function contains registers representing the return value and the arguments
	//   - we must keep the registers locally.
	// advantage of having the interpreter in C/RenderScript: We can use the stack of the execution function and
	// do not need to provide extra mechanisms.

	/* Example of interpreter in C

	range is compiled into a pair of Range and a register containing the current value

function {
	list<stmts>
	list<regs>

	register returnValue

	bool eval() {
	    stmts match {
	    case (+, src0, src1, dst): dst = src0 + src1;
	    case (fold, range, initvalue, cont, dst): // initvalue is a function, cont is a function
			range.init()
			dst = initvalue
			while(range.next())
			    dst = cont.eval() // when compiling, cont uses register set of initvalue.
	    }
	    case (or, alt0, alt1, dst): // alt0 and alt1 are functions with dst as returnValue
	  		alt0.eval() || alt1.eval();
	}
}

// two functions:
// okay, first step create code such that terms are flat.
// this can be done by conditional term rewriting.

// flat(s + t) -> flat(s) ++ flat(t) ++ s + t; then I go through list and set up registers

// flat(s or t) ->
// flat_assign(s or t, dst) ->

// Three functions I need for a proof of concept: plus, or and fold [fold can be part of a later step]
//


compiling(term t, stmts: list[stmt], regs: map[term, register], compile_stack) returns register
	list[stmt] program
	map[t, register] regs

	t match {
	    case(+, arg0, arg1): // [I could use overloading here?]
	        compiling(arg0, stmts, regs, arg1 :: stack)
	}

and compiling_predefined(term t, list[stmt], map[term, register], register): Unit = {
}
	 */


	/*def compile(t: Term): Register = {

	}*/
}
