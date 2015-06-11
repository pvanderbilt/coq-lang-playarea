# coq-lang-playarea
STLC in Coq extended with a sound big-step semantics, functions as closures and records as lists.

This project starts with Software Foundation's ("SF's") simply typed lambda calculus (STLC) 
as defined in Coq and extends it in various ways:

- Added a big-step semantics in the form of an `evalF` function that uses a
	runtime context, function closures and a
	return type that has normal return, "no gas" and "stuck" alternatives.
	See [LEval.v](LEval.v)

- Proved soundness wrt `evalF`: on a well-typed term, `evalF` does not get stuck.
	See [LEProps.v](LEProps.v).

- Added records as lists, where a record term contains a list of definitions
	and a record type contains a list of declarations.
	Defined custom recursion and induction principles.
	Also changed the typing context to be a list of declarations.
	See [LDef.v](LDef.v), [LProps.v](LProps.v), [LEval.v](LEval.v) and [LEProps.v](LEProps.v).

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
	- a `may_eval_to` relation (`t / g =>: T`) that says `evalF` on term `t` 
		with runtime-context `g` will either run out of gas or 
		yield a value of type `T`;
	- other relations;
	- lemmas for "inverting" the `value_has_type` function;
	- lemmas for reasoning about contexts and lookup;
	- lemmas that simplify later proofs.
	
	The relations are defined as fixpoints to get around the problems identified in LEProps3.
	However, there is some Coq-imposed ugliness that would be nice to clean up.

- [LEProps3.v](LEProps3.v): This is an earlier attempt at soundness using an inductive 
	relation for `value_has_type`. However, it ran into a problem with Coq's 
	"Non strictly positive occurrence" error.
	Using admitted (faked) lemmas to get around this
	problem, the soundness theorem goes through.
	However, it has not been updated to handle records.

- [LDef.v](LDef.v): This started as SF's Stlc.v with non-essential material removed. 
	Records have been added along with definitions
	and declarations.  The typing context is now a list of declarations.

Notes:

-	This approach to records differs from that of SF's Records.v which "flattens"
	records into the other elements, so, for example, a term could be `(trcons x ttrue tfalse)`,
	which does not make sense. To deal with this, they define a predicate, `well_formed_tm`, that
	ensures that the final term of `trcons` is either `trnil` or another `trcons`.
	
	The approach given here has `trcons` containing a list of definitions (identifier/term pairs),
	with custom induction principles provided to make up for the 
	weak ones defined automatically by Coq.

Additional files are:

- [LProps.v](LProps.v): SF's StlcProp.v, modified for the changes to 
  	LDef.v as described above.
- [Tests.v](Tests.v): The examples factored out of Pierce's Stlc.v.
- [Tests2.v](Tests2.v): Tests of the big-step evaluation relations of [LEval.v](LEval.v).

There is also a file [Utils.v](Utils.v) that has some useful tactics (and related lemmas):

- Two tactics that deal with hypotheses of the form `H:P->Q` or `H:forall x, P->Q` 
	(where `Q` does not match the goal) by generating `P` as a subgoal, with `x` as an
	"existential" variable in the second case.
- A tactic for simplifying terms contained in a hypothesis.
