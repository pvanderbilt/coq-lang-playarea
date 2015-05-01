# coq-lang-playarea
A repository for experimenting with Coq and programming language properties.

The current experiment is to prove the soundness of a big-step semantics for Pierce's
version of STLC.  This semantics is based on an `evalF` function that uses a
runtime context (a mapping identifiers to values), function closures and a
return type that has normal return, "no gas" and "stuck" alternatives.  In this
context, I define soundness to mean that a well-typed term does not get stuck.
I believe I have accomplished this, see [LEProps.v](LEProps.v).

To use this software:

- Obtain the Coq interactive theorem prover [here](https://coq.inria.fr/download) .

- Obtain Pierce's "Software Foundations" 
	[sf.tar.qz](http://www.seas.upenn.edu/~bcpierce/sf/current/sf.tar.gz),
	unpack it someplace and change the `LoadPath` lines of each .v file.

The main files are:

- [LEval.v](LEval.v): Contains the definitions of the `eval` relation and `evalF` function;
	the latter is the key one. It also defines association lists, an `evalue` type, 
	and runtime contexts.

- [LEProps.v](LEProps.v): The main content is a proof that `evalF`, 
	when applied a term of type `T`, either yields a value of type `T` 
	or "runs out of gas"; it does not get stuck.  SOundness, as defined above, follows directly.

- [LEProps3.v](LEProps3.v): This is an earlier attempt at soundness using an inductive 
	relation for `value_has_type`. However, it ran into a problem with Coq's 
	"Non strictly positive occurrence" error.  Using admitted (faked) lemmas to get around this
	problem, the soundness theorem goes through.  This file also defines:
	- relations that relate `evalue` instances, `evalF` and STLC types (instances of `ty`);
	- the admitted lemmas for getting around the positive occurrence problem;
	- other useful lemmas.
	