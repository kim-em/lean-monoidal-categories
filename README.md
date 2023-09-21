# Archived, this repository is obsolete!

The entire contents have long ago become part of [Mathlib](https://github.com/leanprover-community/mathlib4).

---

[![Build Status](https://travis-ci.org/semorrison/lean-monoidal-categories.svg?branch=master)](https://travis-ci.org/semorrison/lean-monoidal-categories)

This repository contains some experimental work on monoidal categories, developed in the interactive
theorem prover Lean.

It depends on the Lean category theory library available at https://github.com/semorrison/lean-category-theory.

To download dependencies and compile, just run `leanpkg build`.

## Projects

* transporting structures along equivalences: e.g. given an equivalence of categories, transport a monoidal structure?

* define Day convolution: the monoidal structure on FunctorCategory C D when D is monoidal.
* is this known: a monoidal structure on monoidal functors from C to D when D is braided?

* enriched categories!
* additive categories, additive envelopes
* closed monoidal categories
