/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The units of a finite group with zero are its roots of unity

For a finite commutative group with zero `F` with `q` elements, every unit satisfies
`x ^ (q - 1) = 1`, so the group `μ_{q-1}` of `(q-1)`-st roots of unity is all of `Fˣ`. This file
records that identification. The main example is the multiplicative structure of a finite field.

Mathlib has the statement for the prime fields (`ZMod.rootsOfUnity_eq_top`); the version here is
for an arbitrary finite commutative group with zero and is indexed by `Nat.card`.

## Main results

* `TauCeti.rootsOfUnity_natCard_sub_one_eq_top` and `TauCeti.rootsOfUnityEquivUnits`: the
  `(q-1)`-st roots of unity of `F` are exactly its units.
-/

public section

noncomputable section

namespace TauCeti

variable (F : Type*) [Finite F]

section CommGroupWithZero

variable [CommGroupWithZero F]

/-- **Every unit of a finite commutative group with zero with `q` elements is a `(q-1)`-st root
of unity**; in particular every unit of a finite field is. -/
theorem rootsOfUnity_natCard_sub_one_eq_top : rootsOfUnity (Nat.card F - 1) F = ⊤ := by
  have := Fintype.ofFinite F
  ext α
  simp only [mem_rootsOfUnity', Subgroup.mem_top, iff_true, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one (α : F) α.ne_zero

/-- The `(q-1)`-st roots of unity of a finite commutative group with zero with `q` elements, a
finite field for instance, are its units. -/
def rootsOfUnityEquivUnits : rootsOfUnity (Nat.card F - 1) F ≃* Fˣ :=
  (MulEquiv.subgroupCongr (rootsOfUnity_natCard_sub_one_eq_top F)).trans Subgroup.topEquiv

@[simp]
theorem rootsOfUnityEquivUnits_apply (ζ : rootsOfUnity (Nat.card F - 1) F) :
    rootsOfUnityEquivUnits F ζ = (ζ : Fˣ) := by
  simp only [rootsOfUnityEquivUnits, MulEquiv.trans_apply, Subgroup.topEquiv_apply,
    MulEquiv.subgroupCongr_apply]

end CommGroupWithZero

end TauCeti
