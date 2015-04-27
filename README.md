# coq-lang-playarea
A repository for experimenting with Coq and programming language properties.

This repository is for experimenting with the Coq theorem prover as applied to
proving properties of programming languages.

The current experiment is to prove sound a big-step semantics for Pierce's
version of STLC. This semantics is based on an evalF function that uses a
runtime context (a mapping identifiers to values), function closures and a
return type that has normal return, "no gas" and "stuck" alternatives. In this
context, I define soundness to mean that a well-typed term does not get stuck.

To use this, obtain Pierce's "Software Foundations" download at
http://www.seas.upenn.edu/~bcpierce/sf/current/sf.tar.gz,
install it someplace and change the LoadPath lines of each .v file.
