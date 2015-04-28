# coq-lang-playarea
A repository for experimenting with Coq and programming language properties.

The current experiment is to prove the soundness of a big-step semantics for Pierce's
version of STLC.  This semantics is based on an `evalF` function that uses a
runtime context (a mapping identifiers to values), function closures and a
return type that has normal return, "no gas" and "stuck" alternatives.  In this
context, I define soundness to mean that a well-typed term does not get stuck.
However, I am running into a problem with Coq's "Non strictly positive occurrence" 
error.

To use this software:

- Obtain the Coq interactive theorem prover [here](https://coq.inria.fr/download) .

- Obtain Pierce's "Software Foundations" 
[sf.tar.qz](http://www.seas.upenn.edu/~bcpierce/sf/current/sf.tar.gz),
unpack it someplace and change the `LoadPath` lines of each .v file.

The main files are:

- [LEval.v](LEval.v): Contains the definitions of the `eval` relation and `evalF` function;
  the latter is the key one. It also defines association lists, an `evalue` type, and runtime contexts.
	
- [LEProps3.v](LEProps3.v): The main content is the proof of soundess of `evalF` 
	(using admitted (faked) lemmas to get around the positive occurrence problem).
	But first it defines:
	- relations that relate `evalue` instances, `evalF` and STLC types (instances of `ty`);
	- the admitted lemmas for getting around the positive occurrence problem;
	- other useful lemmas.
	