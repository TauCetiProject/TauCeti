/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.NumberTheory.LocalField.QuadraticForm.AnisotropicQuaternary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo

/-!
# Kummer cup products over `ℚ_2`

The dyadic Hilbert-symbol values and the cup-norm comparison show that `(2) ∪ (5)` is
nonzero in `H²(G_{ℚ_2}, 𝔽₂)`. The classification of local quaternion algebras identifies
this cup with `(-1) ∪ (-1)`, since both Hilbert symbols are `-1`.

These computations use `TauCeti.cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one`,
`TauCeti.cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq`, and
`TauCeti.BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, for the dyadic Hilbert symbols.
* J.-P. Serre, *Local Fields*, Chapter XIV, §2, for the Kummer cup comparison.
-/

public section

noncomputable section

namespace TauCeti

local instance : Invertible (2 : ℚ_[2]) := invertibleOfNonzero (by norm_num)

/-- The cup `(2) ∪ (5)` over `ℚ_2` is nonzero, since `(2,5)_{ℚ_2} = -1`. -/
theorem cup_kummerClass_two_five_ne_zero_padicTwo :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
      (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) ≠ 0 := by
  rw [Ne, cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one,
    hilbertSymbol_two_five_padicTwo]
  norm_num

/-- Over `ℚ_2`, the two nonzero quaternion cups `(2) ∪ (5)` and `(-1) ∪ (-1)` agree. -/
theorem cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
      (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) =
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (-1)) (kummerClass (-1)) := by
  apply (cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq _ _ _ _).2
  exact (BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq _ _ _ _).2
    (hilbertSymbol_two_five_padicTwo.trans hilbertSymbol_neg_one_neg_one_padicTwo.symm)

end TauCeti
