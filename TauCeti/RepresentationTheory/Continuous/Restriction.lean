/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Restriction of continuous representations

This file records basic compatibility results between continuous representations and restriction
along monoid homomorphisms.

## Main results

* `TauCeti.res_trivial`: restriction of a trivial representation is trivial on the nose.
-/

public section

namespace TauCeti

universe u v w

variable (R : Type u) [Ring R] [TopologicalSpace R] (G : Type v) [Monoid G]
  (M : Type w) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul R M]

/-- Restriction of a trivial representation along a monoid homomorphism is the corresponding
trivial representation of the source monoid, on the nose.

For groups, `TopRep.res` is a reducible abbreviation for the left-hand side, so this lemma also
proves the corresponding equality stated with `TopRep.res` verbatim. -/
lemma res_trivial {H : Type*} [Monoid H] (f : H →* G) :
    TopRep.of ((ContRepresentation.trivial R G M).restrict f) =
      TopRep.of (ContRepresentation.trivial R H M) := (rfl)

end TauCeti
