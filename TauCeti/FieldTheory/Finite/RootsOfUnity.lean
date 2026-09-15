/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The unit group of a finite field is its group of roots of unity

For a finite field `F` with `q` elements, every unit satisfies `x ^ (q - 1) = 1`, so the group
`μ_{q-1}` of `(q-1)`-st roots of unity is all of `Fˣ`. This file records that identification and
the accompanying cast computation `(q - 1 : F) = -1`, which is what makes `q - 1` invertible in
any commutative local ring whose residue field is `F`.

Mathlib has the statement for the prime fields (`ZMod.rootsOfUnity_eq_top`); the version here is
for an arbitrary finite field and is indexed by `Nat.card`.

## Main results

* `TauCeti.natCast_natCard_sub_one_eq_neg_one`: `(q - 1 : F) = -1`.
* `TauCeti.rootsOfUnity_natCard_sub_one_eq_top` and `TauCeti.rootsOfUnityEquivUnits`: the
  `(q-1)`-st roots of unity of `F` are exactly its units.
-/

public section

noncomputable section

namespace TauCeti

variable (F : Type*) [Field F] [Finite F]

/-- In a finite field with `q` elements, `q - 1` reduces to `-1`; in particular it is nonzero. -/
theorem natCast_natCard_sub_one_eq_neg_one : ((Nat.card F - 1 : ℕ) : F) = -1 := by
  have := Fintype.ofFinite F
  have hq : ((Nat.card F : ℕ) : F) = 0 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.cast_sub Finite.one_lt_card.le, hq, Nat.cast_one, zero_sub]

/-- **Every unit of a finite field with `q` elements is a `(q-1)`-st root of unity.** -/
theorem rootsOfUnity_natCard_sub_one_eq_top : rootsOfUnity (Nat.card F - 1) F = ⊤ := by
  have := Fintype.ofFinite F
  ext α
  simp only [mem_rootsOfUnity', Subgroup.mem_top, iff_true, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one (α : F) α.ne_zero

/-- The `(q-1)`-st roots of unity of a finite field with `q` elements are its units. -/
def rootsOfUnityEquivUnits : rootsOfUnity (Nat.card F - 1) F ≃* Fˣ :=
  (MulEquiv.subgroupCongr (rootsOfUnity_natCard_sub_one_eq_top F)).trans Subgroup.topEquiv

@[simp]
theorem rootsOfUnityEquivUnits_apply (ζ : rootsOfUnity (Nat.card F - 1) F) :
    rootsOfUnityEquivUnits F ζ = (ζ : Fˣ) :=
  (rfl)

end TauCeti
