# Programming language semantics in Lean

This repo contains proofs of some classic results of programming langauge semantics in the [Lean](https://lean-lang.org/) theorem prover. We define a simple imperative language `IMP`[^1] and construct its big-step, small-step and relational semantics concluding that they are all equivalent.

[^1]: Inspired by [Winskel](https://mitpress.mit.edu/9780262731034/the-formal-semantics-of-programming-languages/).

## Structure

The `Semantics` folder contains files with general results that we need for our proofs. In `Set` we develop a small part of set theory necessary to construct the denotational semantics, in `ReflTransGen` we define reflexive-transitive relations for the small-step semantics and so on... The `IMP` folder contains the syntactical definition of the language in `Lang`, the rest of the files describe the semantics, and in `Equivalence` we prove that they are equivalent.
