# coq-lang-playarea
STLC in Coq extended with a sound big-step semantics and functions as closures.

This project starts with Software Foundation's ("SF's") STLC (simply typed lambda calculus) 
as defined in Coq and extends it in various ways:

- Added: a big-step semantics in the form of an `evalF` function that uses a
	runtime context, function closures and a
	return type that has normal return, "no gas" and "stuck" alternatives.
	See [LEval.v](LEval.v)

- Soundness proved: `evalF` on a well-typed term does not get stuck.
	See [LEProps.v](LEProps.v).


To use this software:

- Obtain the Coq interactive theorem prover [here](https://coq.inria.fr/download).

- Obtain the "Software Foundations" library (by Pierce et. al.)
	[sf.tar.qz](http://www.seas.upenn.edu/~bcpierce/sf/current/sf.tar.gz),
	unpack it someplace and change the `LoadPath` line of `Init.v` and the `PSF`
	variable in `Makefile` to its location.

The main files are:

- [LEval.v](LEval.v): Contains the definitions of the `eval` relation and `evalF` function;
	the latter is the key one. It also defines `alists` (association lists), 
	an `evalue` type (of values produced by `evalF`), 
	and runtime contexts (alists of `evalues`).

- [LEProps.v](LEProps.v): The main content is a proof that `evalF`, 
	when applied a well-typed term, either yields a value of that type 
	or "runs out of gas"; it does not get stuck.  
	Soundness, as defined above, follows directly.
	This file also defines:
	- a `value_has_type` relation (`v ::: T`) that relates `(v : evalue)` instances 
		and STLC types (`T : ty`);
	- an `evaluates_to_a` relation (`t / g =>: T`) that says `evalF` on term `t` 
		with runtime-context `g` will either run out of gas or yield a value of type `T`;
	- other relations;
	- lemmas for "inverting" the `value_has_type` function;
	- lemmas for reasoning about contexts and lookup;
	- lemmas that simplify later proofs.
	
	The relations are defined as fixpoints to get around the problem with LEProps3.
	However, there is some Coq-imposed ugliness that would be nice to clean up.

- [LEProps3.v](LEProps3.v): This is an earlier attempt at soundness using an inductive 
	relation for `value_has_type`. However, it ran into a problem with Coq's 
	"Non strictly positive occurrence" error.  Using admitted (faked) lemmas to get around this
	problem, the soundness theorem goes through.  

Additional files are:

- [LDef.v](LDef.v): Pierce's Stlc.v with non-essential material removed and module renamed to LDEF.
- [LProps.v](LProps.v): Pierce's StlcProp.v.
- [Tests.v](Tests.v): The examples factored out of Pierce's Stlc.v.
- [Tests2.v](Tests2.v): Tests of the big-step evaluation relations of [LEval.v](LEval.v).

There is also a file [Utils.v](Utils.v) that has some useful tactics (and related lemmas):

- Two tactics that deal with hypotheses of the form `H:P->Q` or `H:forall x, P->Q` 
	(where `Q` does not match the goal) by generating `P` as a subgoal, with `x` as an
	"existential" variable in the second case.
- A tactic for simplifying terms contained in a hypothesis.
