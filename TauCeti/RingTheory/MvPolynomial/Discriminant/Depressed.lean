/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.HomogeneousUnits
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Graded localization of the generic depressed discriminant

Over any integral domain `R` with `(2 : R) ≠ 0` and `(m : R) ≠ 0` (such as `ℤ`), localizing
`MvPolynomial (Fin (m - 1)) R` (with `depressedWeight m`) away from `depressedDiscr R m` has
homogeneous unit degrees `m * (m - 1) ℤ` and shift class group `ZMod (m * (m - 1))` for every
`m ≥ 2` (`TauCeti.homogeneousUnitDegrees_awayGrading_depressedDiscr`,
`TauCeti.shiftClassGroupAwayGradingDepressedDiscrEquiv`). For `m ≥ 3` this uses primality of
`depressedDiscr R m` (`TauCeti.depressedDiscr_prime`), while for `m = 2` it uses
`depressedDiscr R 2 = -4 * X 0` as a nonzero scalar multiple of the prime `X 0`.

In particular, when `(2 : R) ≠ 0` and `(3 : R) ≠ 0`, the negative of the cubic depressed
discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short Weierstrass discriminant factor), is prime
of weight `12` for the weights `![4, 6]`, giving shift class group `ZMod 12`
(`TauCeti.shiftClassGroupAwayGradingWeierstrassEquiv`).

## Main definitions

* `TauCeti.shiftClassGroupAwayGradingDepressedDiscrEquiv`: the shift class group
  `ZMod (m * (m - 1))` after inverting `depressedDiscr R m` over an integral domain `R` with
  `m ≥ 2`, `(2 : R) ≠ 0`, and `(m : R) ≠ 0`.
* `TauCeti.shiftClassGroupAwayGradingWeierstrassEquiv`: the shift class group `ZMod 12` after
  inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` with weights `![4, 6]` over an integral domain `R` with
  `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.

## Main results

* `TauCeti.homogeneousUnitDegrees_awayGrading_depressedDiscr`: the homogeneous unit degrees after
  inverting `depressedDiscr R m` are `AddSubgroup.zmultiples (m * (m - 1))` for all `m ≥ 2` with
  `(2 : R) ≠ 0` and `(m : R) ≠ 0`.
* `TauCeti.mem_weightedHomogeneousSubmodule_weierstrass`: `4 * X 0 ^ 3 + 27 * X 1 ^ 2` has weight
  `12` for the weights `![4, 6]`.
* `TauCeti.prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq`: primality of
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` over any integral domain with `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.
-/

public section

namespace TauCeti

open MvPolynomial TauCeti.GradedAlgebra

attribute [local instance] MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields homogeneous unit degrees `m * (m - 1) ℤ` over any integral domain `R` with `m ≥ 2`,
`(2 : R) ≠ 0`, and `(m : R) ≠ 0`. -/
theorem homogeneousUnitDegrees_awayGrading_depressedDiscr {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      = AddSubgroup.zmultiples ((m : ℤ) * (m - 1)) := by
  rcases eq_or_lt_of_le hm with rfl | hm3
  · have h4 : (-4 : R) ≠ 0 := by
      intro h0
      exact mul_ne_zero h2 h2 (by linear_combination -h0)
    have hx : (X 0 : MvPolynomial (Fin 1) R) ∈
        weightedHomogeneousSubmodule R (depressedWeight 2) ((2 : ℤ) * (2 - 1)) := by
      rw [mem_weightedHomogeneousSubmodule]
      convert isWeightedHomogeneous_X R (depressedWeight 2) 0
      simp [depressedWeight_apply]
    exact homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_C_mul_prime
      (depressedWeight 2) (depressedDiscr_mem R 2) h4 hx prime_X
      (by rw [depressedDiscr_two, map_neg, map_ofNat])
  · exact homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_prime
      (depressedWeight m) (depressedDiscr_mem R m)
      (depressedDiscr_prime h2 hmR hm (fun h ↦ absurd h (by omega)))

/-- Inverting `depressedDiscr R m` in `MvPolynomial (Fin (m - 1)) R` with `depressedWeight m`
yields shift class group `ZMod (m * (m - 1))` over any integral domain `R` with `m ≥ 2`,
`(2 : R) ≠ 0`, and `(m : R) ≠ 0`. -/
noncomputable def shiftClassGroupAwayGradingDepressedDiscrEquiv {R : Type*} [CommRing R]
    [IsDomain R] (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m))
      ≃+ ZMod (m * (m - 1)) :=
  (ShiftClassGroup.equivZMod
      (homogeneousUnitDegrees_awayGrading_depressedDiscr h2 hmR hm)).trans
    (ZMod.ringEquivCongr (by
      have h : ((m : ℤ) * (m - 1)) = ((m * (m - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [h, Int.natAbs_natCast])).toAddEquiv

/-- The identification of the shift class group after inverting `depressedDiscr R m` with
`ZMod (m * (m - 1))` sends the class of `d` to `d mod m * (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayGradingDepressedDiscrEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hmR : (m : R) ≠ 0) (hm : 2 ≤ m) (d : ℤ) :
    shiftClassGroupAwayGradingDepressedDiscrEquiv h2 hmR hm d = d := by
  rw [shiftClassGroupAwayGradingDepressedDiscrEquiv, AddEquiv.trans_apply,
    ShiftClassGroup.equivZMod_mk, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv,
    map_intCast]

/-- The negative of the cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short
Weierstrass discriminant factor), has weight `12` when the variables have weights `4` and `6`. -/
theorem mem_weightedHomogeneousSubmodule_weierstrass (R : Type*) [CommRing R] :
    (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  have h3 : (depressedDiscr R 3).IsWeightedHomogeneous (depressedWeight 3) 6 :=
    (mem_weightedHomogeneousSubmodule R _ _ _).mp (depressedDiscr_mem R 3)
  have hscaled := h3.comp_weight (AddMonoidHom.mulLeft (2 : ℤ))
  have hw : (AddMonoidHom.mulLeft (2 : ℤ)) ∘ depressedWeight 3 = (![4, 6] : Fin 2 → ℤ) := by
    ext i
    fin_cases i <;> simp [depressedWeight_apply]
  rw [hw] at hscaled
  have hneg : -(depressedDiscr R 3) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 :=
    neg_mem ((mem_weightedHomogeneousSubmodule R _ _ _).mpr hscaled)
  rwa [depressedDiscr_three, show -(-4 * X 0 ^ 3 - 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) =
    4 * X 0 ^ 3 + 27 * X 1 ^ 2 by ring] at hneg

/-- Over any integral domain `R` in which `(2 : R) ≠ 0` and `(3 : R) ≠ 0`, the negative of the
cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short Weierstrass discriminant
factor), is prime. -/
theorem prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hassoc : Associated (depressedDiscr R 3)
      (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) :=
    ⟨-1, by simp [depressedDiscr_three]; ring⟩
  exact hassoc.prime_iff.mp
    (depressedDiscr_prime h2 (m := 3) (by norm_num; exact h3) (by norm_num)
      (fun h ↦ absurd h (by omega)))

/-- Inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` in `R[a, b]` with weights `4, 6` over an integral
domain `R` with `(2 : R) ≠ 0` and `(3 : R) ≠ 0` yields shift class group `ZMod 12`. -/
noncomputable def shiftClassGroupAwayGradingWeierstrassEquiv {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    ShiftClassGroup
        (awayGrading (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
          (mem_weightedHomogeneousSubmodule_weierstrass R)) ≃+ ZMod 12 :=
  shiftClassGroupAwayGradingWeightedEquiv (![4, 6] : Fin 2 → ℤ)
    (mem_weightedHomogeneousSubmodule_weierstrass R)
    (prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq h2 h3)

/-- The identification of the shift class group after inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2`
with `ZMod 12` sends the class of `d` to `d mod 12`. -/
@[simp]
theorem shiftClassGroupAwayGradingWeierstrassEquiv_mk {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (d : ℤ) :
    shiftClassGroupAwayGradingWeierstrassEquiv h2 h3 d = d :=
  shiftClassGroupAwayGradingWeightedEquiv_mk _ _ _ d

end TauCeti
