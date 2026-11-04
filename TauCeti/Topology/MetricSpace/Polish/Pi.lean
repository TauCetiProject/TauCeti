/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Polish

/-!
# Countable products of countable discrete spaces are Polish

A countable product of countable discrete spaces is separable and completely metrizable, hence
Polish. The main examples are Cantor space `ℕ → Bool`, the spaces `ℕ → Fin k`, and Baire space
`ℕ → ℕ`; they are the model spaces of descriptive set theory, and statements about Polish spaces
are applied to them and to their finite products such as `(ℕ → Bool) × (ℕ → Bool)`.

## Main results

* `TauCeti.polishSpace_pi_of_discreteTopology`: a countable product of countable discrete spaces
  is a Polish space.

## Implementation notes

Both ingredients of Mathlib's generic instance `PolishSpace.mk`, separability and complete
metrizability, are found by instance search for `ℕ → Bool`, and so is `PolishSpace Bool`, but
the search for `PolishSpace (ℕ → Bool)` itself fails: on the way it seeks separability of `Bool`
through `PolishSpace.toSecondCountableTopology`, which revisits the goal `PolishSpace Bool`
inside its own search. The same failure occurs for `ℕ → Fin k` and for
`(ℕ → Bool) × (ℕ → Bool)`, while `ℕ → ℕ` is found. The instance below gives the conclusion
directly for products of countable discrete spaces, so that Polish-space results apply to Cantor
space and its finite powers without a local instance.
-/

public section

namespace TauCeti

/-- **A countable product of countable discrete spaces is Polish.** In particular Cantor space
`ℕ → Bool` and the spaces `ℕ → Fin k` are Polish spaces. -/
instance polishSpace_pi_of_discreteTopology {ι : Type*} {π : ι → Type*} [Countable ι]
    [∀ i, TopologicalSpace (π i)] [∀ i, DiscreteTopology (π i)] [∀ i, Countable (π i)] :
    PolishSpace (∀ i, π i) :=
  PolishSpace.mk

end TauCeti
