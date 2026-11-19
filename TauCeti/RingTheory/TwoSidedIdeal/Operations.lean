/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Carrier of the pullback of a two-sided ideal

Mathlib defines `TwoSidedIdeal.comap` via congruence relations (`RingCon.comap`) and provides the
pointwise membership lemma `TwoSidedIdeal.mem_comap`, but omits the set-level preimage
characterization `TwoSidedIdeal.coe_comap` matching `Ideal.coe_comap`, `Subring.coe_comap`, and
`NonUnitalStarSubalgebra.coe_comap`.

## Main results

* `TwoSidedIdeal.coe_comap`: `(I.comap f : Set R) = f ⁻¹' (I : Set S)`.
-/

public section

namespace TwoSidedIdeal

/-- Coercing `I.comap f` to `Set R` gives the set preimage `f ⁻¹' (I : Set S)`. -/
@[simp]
theorem coe_comap {F R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (I : TwoSidedIdeal S) (f : F) :
    (I.comap f : Set R) = f ⁻¹' (I : Set S) :=
  Set.ext fun _ ↦ TwoSidedIdeal.mem_comap f

end TwoSidedIdeal
