/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori
-- `PadicInt.finite_residueField` and `PadicInt.card_residueField`: the residue field of `ℤ_[p]`
-- has `p` elements.
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Iwahori subgroups of `GL_m(ℤ_p)`

The residue field of `ℤ_p` has `p` elements, so the general index formulas for Iwahori subgroups
over a local ring specialize to `[GL₂(ℤ_p) : Iw] = p + 1` and `[Iw : Iw₁] = (p - 1) ^ #m`.

In particular the pro-`p` Iwahori subgroup `Iw₁` of `GL_m(ℤ_p)` is the whole Iwahori subgroup
exactly when `p = 2` or `m` is empty: over `𝔽₂` every invertible upper-triangular matrix is
unitriangular, whereas for odd `p` the diagonal quotient `Iw ⧸ Iw₁ ≃ (𝔽_pˣ)^m` is nontrivial.

## Main declarations

* `TauCeti.index_iwahori_fin_two_padicInt`: `[GL₂(ℤ_p) : Iw] = p + 1`.
* `TauCeti.relIndex_iwahoriOne_iwahori_padicInt`: `[Iw : Iw₁] = (p - 1) ^ #m`.
* `TauCeti.iwahoriOne_eq_iwahori_padicInt_iff`: `Iw₁ = Iw` exactly when `p = 2` or `m` is
  empty.
-/

public section

namespace TauCeti

variable (m : Type*) [Fintype m] [LinearOrder m] (p : ℕ) [Fact p.Prime]

/-- The Iwahori subgroup of `GL₂(ℤ_p)` has index `p + 1`. -/
theorem index_iwahori_fin_two_padicInt : (iwahori (Fin 2) ℤ_[p]).index = p + 1 := by
  rw [index_iwahori_fin_two, PadicInt.card_residueField p]

/-- The pro-`p` Iwahori subgroup of `GL_m(ℤ_p)` has index `(p - 1) ^ #m` in the Iwahori
subgroup. -/
theorem relIndex_iwahoriOne_iwahori_padicInt :
    (iwahoriOne m ℤ_[p]).relIndex (iwahori m ℤ_[p]) = (p - 1) ^ Fintype.card m := by
  rw [relIndex_iwahoriOne_iwahori, PadicInt.card_residueField p]

/-- The pro-`p` Iwahori subgroup of `GL_m(ℤ_p)` is the whole Iwahori subgroup exactly when `p = 2`
or `m` is empty. -/
theorem iwahoriOne_eq_iwahori_padicInt_iff :
    iwahoriOne m ℤ_[p] = iwahori m ℤ_[p] ↔ p = 2 ∨ IsEmpty m := by
  have hp := (Fact.out : p.Prime).two_le
  rw [le_antisymm_iff, and_iff_right iwahoriOne_le_iwahori, ← Subgroup.relIndex_eq_one,
    relIndex_iwahoriOne_iwahori_padicInt, Nat.pow_eq_one, ← Fintype.card_eq_zero_iff]
  omega

end TauCeti
