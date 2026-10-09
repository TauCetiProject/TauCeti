/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.Algebra.QuadraticAlgebra.NormTrace
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.Value
public import TauCeti.NumberTheory.LocalField.QuadraticForm.AnisotropicQuaternary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo
import TauCeti.Algebra.Group.Units.Basic

/-!
# A nonzero Evens norm over `ℚ_2(i)`

The quadratic algebra `QuadraticAlgebra ℚ_[2] (-1) 0` is a field, since `-1` is not a
square in `ℚ_2`. Its generator `i` satisfies `i² = -1`. The unit `a = 1 + 2i` has trace
`2` and norm `5`, and its Kummer class has Evens norm `(2) ∪ (5) ≠ 0`.

The calculation specializes `TauCeti.galoisEvens2_kummerClass_one_add`; nonvanishing
uses `TauCeti.cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one` and the dyadic
Hilbert-symbol computations.

This calculation distinguishes the index-two Evens norm from a class differing by
`(-1) ∪ (-1)`: both classes restrict to the same class over `ℚ_2(i)`, but they are
unequal over `ℚ_2`. In particular, testing only after restriction cannot fix the
normalization of the norm.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. 78 (1984), Lemme II.2.1.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. 59
  (1984), Théorème 1′.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, for `(2,5)_{ℚ_2} = -1`.
-/

public section

noncomputable section

open scoped QuadraticAlgebra

namespace TauCeti

namespace DyadicSqrtNegOne

local notation "DyadicSqrtNegOne" => QuadraticAlgebra ℚ_[2] (-1) 0
local notation "i" => (QuadraticAlgebra.omega : DyadicSqrtNegOne)
local notation "finrank_eq_two" => QuadraticAlgebra.finrank_eq_two (-1 : ℚ_[2]) 0

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance : Nontrivial ℚ_[2] :=
  @DivisionRing.toNontrivial _ (instFieldPadic 2).toDivisionRing

local instance : StrongRankCondition ℚ_[2] := commRing_strongRankCondition _

/-- The nonsquareness of `-1` supplies Mathlib's field structure on `ℚ_2(i)`. -/
instance : Fact (¬ IsSquare (-1 : ℚ_[2])) := by
  refine ⟨?_⟩
  intro h
  have hunit : IsSquare (-1 : ℚ_[2]ˣ) := isSquare_units_val_iff.mp (by simpa using h)
  have := hilbertSymbol_eq_one_of_isSquare_left hunit (-1)
  rw [hilbertSymbol_neg_one_neg_one_padicTwo] at this
  norm_num at this

private theorem one_add_two_mul_i_ne_zero : (1 + 2 * i : DyadicSqrtNegOne) ≠ 0 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  norm_num at him

/-- The unit `1 + 2i` of `ℚ_2(i)`. -/
def oneAddTwoI : DyadicSqrtNegOneˣ := Units.mk0 (1 + 2 * i) one_add_two_mul_i_ne_zero

/-- The value of the distinguished unit. -/
@[simp]
theorem coe_oneAddTwoI : (oneAddTwoI : DyadicSqrtNegOne) = 1 + 2 * i := (rfl)

/-- The trace of `1 + 2i` is `2`. -/
@[simp]
theorem trace_oneAddTwoI : Algebra.trace ℚ_[2] DyadicSqrtNegOne oneAddTwoI = 2 := by
  rw [QuadraticAlgebra.algebraTrace_eq_trace]
  norm_num [QuadraticAlgebra.trace_def, coe_oneAddTwoI]

/-- The norm of `1 + 2i` is `5`. -/
@[simp]
theorem norm_oneAddTwoI : Algebra.norm ℚ_[2] (oneAddTwoI : DyadicSqrtNegOne) = 5 := by
  rw [QuadraticAlgebra.algebraNorm_eq_norm]
  norm_num [QuadraticAlgebra.norm_def, coe_oneAddTwoI]

/-- The finite extension `ℚ_2(i)/ℚ_2` is separable. -/
instance : Algebra.IsSeparable ℚ_[2] DyadicSqrtNegOne := by
  let : Algebra.IsAlgebraic ℚ_[2] DyadicSqrtNegOne := Algebra.IsAlgebraic.of_finite _ _
  let : PerfectField ℚ_[2] := PerfectField.ofCharZero
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

variable [Invertible (2 : ℚ_[2])]

/-- **A nonzero dyadic Evens norm.** Along every embedding of `ℚ_2(i)` in a separable
closure, the Evens norm of the class of `1 + 2i` is `(2) ∪ (5)`. -/
theorem galoisEvens_oneAddTwoI (σ : DyadicSqrtNegOne →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) :
    galoisEvens ℚ_[2] DyadicSqrtNegOne σ finrank_eq_two (kummerClass oneAddTwoI) =
      (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
        (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
        (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) := by
  let : Invertible (2 : DyadicSqrtNegOne) := invertibleOfNonzero (by norm_num)
  have h := galoisEvens2_kummerClass_one_add σ finrank_eq_two (-1) (x := i)
    (by
      rintro ⟨c, hc⟩
      have him := congrArg QuadraticAlgebra.im hc
      simp at him)
    (by simp [QuadraticAlgebra.omega_pow_two_eq_add]) (2 : ℚ_[2]) (by norm_num)
    oneAddTwoI (by simp [map_ofNat])
  have h2 : unitOfInvertible (2 : ℚ_[2]) = Units.mk0 2 two_ne_zero := by
    ext
    simp
  have h5 : Units.mk0 (1 - (2 : ℚ_[2]) ^ 2 * ((-1 : ℚ_[2]ˣ) : ℚ_[2])) (by norm_num) =
      Units.mk0 (5 : ℚ_[2]) (by norm_num) := by
    ext
    norm_num
  simpa only [h2, h5] using h

/-- The cup `(2) ∪ (5)` over `ℚ_2` is nonzero, since `(2,5)_{ℚ_2} = -1`. -/
theorem _root_.TauCeti.cup_kummerClass_two_five_ne_zero_padicTwo :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
      (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) ≠ 0 := by
  rw [Ne, cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one,
    hilbertSymbol_two_five_padicTwo]
  norm_num

/-- Kahn's expression gives the same value: its extra cup `(2) ∪ (-1)` vanishes. -/
theorem galoisEvens_oneAddTwoI_eq_kahn
    (σ : DyadicSqrtNegOne →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) :
    galoisEvens ℚ_[2] DyadicSqrtNegOne σ finrank_eq_two (kummerClass oneAddTwoI) =
      (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
        (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
        (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) +
      (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
        (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero)) (kummerClass (-1)) := by
  have hz := (cup_kummerClass_eq_zero_iff
    (Units.mk0 (2 : ℚ_[2]) two_ne_zero) (-1)).mpr ⟨1, 1, by norm_num⟩
  rw [hz, add_zero, galoisEvens_oneAddTwoI]

/-- The Evens norm of the Kummer class of `1 + 2i` is nonzero. -/
theorem galoisEvens_oneAddTwoI_ne_zero
    (σ : DyadicSqrtNegOne →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) :
    galoisEvens ℚ_[2] DyadicSqrtNegOne σ finrank_eq_two (kummerClass oneAddTwoI) ≠ 0 := by
  rw [galoisEvens_oneAddTwoI]
  exact cup_kummerClass_two_five_ne_zero_padicTwo

/-- Over `ℚ_2`, the two nonzero quaternion cups `(2) ∪ (5)` and `(-1) ∪ (-1)` agree. -/
theorem _root_.TauCeti.cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
      (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) =
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (-1)) (kummerClass (-1)) := by
  apply h2MuToUnits_injective ℚ_[2]
  rw [← brauerCohomologyEquiv_quaternionClass, ← brauerCohomologyEquiv_quaternionClass]
  congr 2
  exact (BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq _ _ _ _).2
    (hilbertSymbol_two_five_padicTwo.trans hilbertSymbol_neg_one_neg_one_padicTwo.symm)

/-- Adding the alternative correction `(-1) ∪ (-1)` makes the dyadic example zero,
whereas the genuine Evens norm is nonzero. -/
theorem galoisEvens_oneAddTwoI_add_cup_neg_one_eq_zero
    (σ : DyadicSqrtNegOne →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) :
    galoisEvens ℚ_[2] DyadicSqrtNegOne σ finrank_eq_two (kummerClass oneAddTwoI) +
      (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
        (kummerClass (-1)) (kummerClass (-1)) = 0 := by
  rw [galoisEvens_oneAddTwoI, ← cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo]
  exact (two_nsmul _).symm.trans (cohomF2.two_nsmul_eq_zero _ _ _)

/-- The nonzero Evens norm in this example restricts to zero over `ℚ_2(i)`. Thus
restriction alone cannot distinguish it from the alternative corrected value. -/
theorem galoisRes_galoisEvens_oneAddTwoI_eq_zero
    (σ : DyadicSqrtNegOne →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) :
    letI : Invertible (2 : DyadicSqrtNegOne) := invertibleOfNonzero (by norm_num)
    galoisRes ℚ_[2] DyadicSqrtNegOne σ 2
      (galoisEvens ℚ_[2] DyadicSqrtNegOne σ finrank_eq_two (kummerClass oneAddTwoI)) = 0 := by
  let : Invertible (2 : DyadicSqrtNegOne) := invertibleOfNonzero (by norm_num)
  have hi0 : i ≠ 0 := by
    intro h
    have him := congrArg QuadraticAlgebra.im h
    simp at him
  have hsquare : Units.map (algebraMap ℚ_[2] DyadicSqrtNegOne).toMonoidHom (-1) ∈
      Subgroup.square DyadicSqrtNegOneˣ := by
    apply Subgroup.mem_square.mpr
    refine ⟨Units.mk0 i hi0, Units.ext ?_⟩
    simp [← sq, QuadraticAlgebra.omega_pow_two_eq_add]
  rw [galoisEvens_oneAddTwoI, cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo,
    galoisRes_cup ℚ_[2] DyadicSqrtNegOne σ 1 1 (kummerClass (-1)) (kummerClass (-1)),
    galoisRes_kummerClass,
    (kummerClass_eq_zero_iff_square DyadicSqrtNegOne).mpr hsquare]
  simp

/-- The worked example has an actual embedding into a separable closure, and a nonzero
Evens norm there; it is not conditional on the existence of such an embedding. -/
theorem exists_galoisEvens_oneAddTwoI_ne_zero :
    ∃ σ : DyadicSqrtNegOne →ₐ[ℚ_[2]] SeparableClosure ℚ_[2],
      galoisEvens ℚ_[2] DyadicSqrtNegOne σ finrank_eq_two (kummerClass oneAddTwoI) ≠ 0 :=
  ⟨IsSepClosed.lift, galoisEvens_oneAddTwoI_ne_zero _⟩

end «DyadicSqrtNegOne»

end TauCeti
