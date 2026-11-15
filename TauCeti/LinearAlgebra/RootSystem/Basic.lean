/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root system that need no further theory.

## Main results

* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.nonempty_of_isIrreducible`: an irreducible root system has a root.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- An irreducible root system (whose roots span the nontrivial weight module) has at least one root
index. Kept as a theorem rather than an instance to avoid cycling with Mathlib's
`[Nonempty ι] [NeZero (2 : R)] [P.IsIrreducible] → P.IsRootSystem` instance. -/
theorem nonempty_of_isIrreducible (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsIrreducible] :
    Nonempty ι := by
  have := IsIrreducible.nontrivial P
  exact P.nonempty_of_isRootSystem

end RootPairing
