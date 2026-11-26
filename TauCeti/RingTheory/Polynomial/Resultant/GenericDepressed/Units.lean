/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.HomogeneousUnits
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Homogeneous units away from the generic depressed discriminant

Let `Δ = depressedDiscr R m` be the discriminant of the generic depressed polynomial
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` over `R[a₂, …, aₘ]`, where `aⱼ` has weight `j`. It is weighted homogeneous
of weight `m (m - 1)`, and over a domain in which `2 ≠ 0` and `(m : R) ≠ 0` (such as `ℤ`), the
degrees of the homogeneous units of `R[a₂, …, aₘ]_Δ` are the multiples of `m (m - 1)`
(`homogeneousUnitDegrees_awayGrading_depressedDiscr`), and its shift classes form
`ZMod (m (m - 1))` (`shiftClassGroupAwayGradingDepressedDiscrEquiv`). For `m ≥ 3` this uses
primality of `depressedDiscr R m` (`TauCeti.depressedDiscr_prime`), while for `m = 2` it uses
`depressedDiscr R 2 = -4 * X 0` as a nonzero scalar multiple of the prime `X 0`.

Geometrically, `𝔾_m` acts on the monic polynomials of degree `m` with roots of sum zero by scaling
the roots, `x ↦ t x`, which multiplies `aⱼ` by `tʲ`. The polynomials with distinct roots are the
invariant open subscheme `{Δ ≠ 0}`, whose graded ring is `R[a₂, …, aₘ]_Δ`. For `m = 2` the degrees
are `2ℤ` and for `m = 3` they are `6ℤ`.

The case `m = 3` with doubled weights is the graded ring of the short Weierstrass equations: the
curve `y² = x³ + a x + b` is invariant under `(x, y, a, b) ↦ (t² x, t³ y, t⁴ a, t⁶ b)`, and its
discriminant `-16 (4 a³ + 27 b²)` is `16` times `depressedDiscr R 3 = -4 a³ - 27 b²`, a unit
multiple when `2` is invertible. With `a, b` of weights `4, 6`, the discriminant has weight `12`
(`depressedDiscr_three_mem_four_six`), and when `2 ≠ 0` and `3 ≠ 0` in `R`, the degrees of the
homogeneous units of `R[a, b]_Δ` are the multiples of `12`
(`homogeneousUnitDegrees_awayGrading_depressedDiscr_three_four_six`), so its shift classes form
`ZMod 12` (`shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv`). The same holds for the
positive-sign short Weierstrass discriminant factor `4 a³ + 27 b²`
(`mem_weightedHomogeneousSubmodule_weierstrass`,
`prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq`,
`shiftClassGroupAwayGradingWeierstrassEquiv`). This is the graded ring behind Mumford's computation
`Pic M_{1,1} ≅ ℤ/12`.

## Main definitions

* `TauCeti.shiftClassGroupAwayGradingDepressedDiscrEquiv`: the shift classes of `R[a₂, …, aₘ]_Δ`
  form `ZMod (m (m - 1))`.
* `TauCeti.shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv`: for the weights `4, 6`, the
  shift classes of `R[a, b]_Δ` form `ZMod 12`.
* `TauCeti.shiftClassGroupAwayGradingWeierstrassEquiv`: the shift class group `ZMod 12` after
  inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` with weights `![4, 6]`.

## Main results

* `TauCeti.homogeneousUnitDegrees_awayGrading_depressedDiscr`: the homogeneous unit degrees of
  `R[a₂, …, aₘ]_Δ` are the multiples of `m (m - 1)`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_depressedDiscr_three_four_six`: for the weights
  `4, 6`, the homogeneous unit degrees of `R[a, b]_Δ` are the multiples of `12`.
* `TauCeti.mem_weightedHomogeneousSubmodule_weierstrass`: `4 * X 0 ^ 3 + 27 * X 1 ^ 2` has weight
  `12` for the weights `![4, 6]`.
* `TauCeti.prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq`: primality of
  `4 * X 0 ^ 3 + 27 * X 1 ^ 2` over any integral domain with `(2 : R) ≠ 0` and `(3 : R) ≠ 0`.

## References

* D. Mumford, *Picard groups of moduli problems*, in *Arithmetical Algebraic Geometry* (Purdue,
  1963), Harper & Row (1965), 33–81.
-/

public section

open MvPolynomial

namespace TauCeti

attribute [local instance] WeightedHomogeneousSubmodule.gradedMonoid

variable {R : Type*} [CommRing R]

/-- **Homogeneous units away from the generic depressed discriminant.** Over a domain in which
`2 ≠ 0` and `(m : R) ≠ 0` with `2 ≤ m`, the degrees of the homogeneous units of `R[a₂, …, aₘ]_Δ`,
with `aⱼ` of weight `j` and `Δ = depressedDiscr R m`, are the multiples of `m (m - 1)`. -/
theorem homogeneousUnitDegrees_awayGrading_depressedDiscr [IsDomain R] {m : ℕ} (h2 : (2 : R) ≠ 0)
    (hmR : (m : R) ≠ 0) (hm2 : 2 ≤ m) :
    homogeneousUnitDegrees (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m)) =
      AddSubgroup.zmultiples (m * (m - 1) : ℤ) := by
  rcases eq_or_lt_of_le hm2 with rfl | hm3
  · have h4 : (-4 : R) ≠ 0 := by
      intro h0
      exact mul_ne_zero h2 h2 (by linear_combination -h0)
    have hx : (X 0 : MvPolynomial (Fin 1) R) ∈
        weightedHomogeneousSubmodule R (depressedWeight 2) (2 * (2 - 1) : ℤ) := by
      rw [mem_weightedHomogeneousSubmodule]
      convert isWeightedHomogeneous_X R (depressedWeight 2) 0
      simp [depressedWeight_apply]
    exact homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_C_mul_prime
      (depressedWeight 2) (depressedDiscr_mem R 2) h4 hx prime_X
      (by rw [depressedDiscr_two, map_neg, map_ofNat])
  · exact homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_prime
      (depressedWeight m) (depressedDiscr_mem R m)
      (depressedDiscr_prime h2 hmR hm2 (fun h ↦ absurd h (by omega)))

/-- Over a domain in which `2 ≠ 0` and `(m : R) ≠ 0` with `2 ≤ m`, the shift classes of
`R[a₂, …, aₘ]_Δ`, with `aⱼ` of weight `j` and `Δ = depressedDiscr R m`, form `ZMod (m (m - 1))`. -/
noncomputable def shiftClassGroupAwayGradingDepressedDiscrEquiv [IsDomain R] {m : ℕ}
    (h2 : (2 : R) ≠ 0) (hmR : (m : R) ≠ 0) (hm2 : 2 ≤ m) :
    ShiftClassGroup (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m)) ≃+
      ZMod (m * (m - 1)) :=
  (ShiftClassGroup.equivZMod
      (homogeneousUnitDegrees_awayGrading_depressedDiscr h2 hmR hm2)).trans
    (ZMod.ringEquivCongr (by rw [Int.natAbs_mul, Int.natAbs_natCast]; congr 1; omega)).toAddEquiv

/-- The identification of the shift classes of `R[a₂, …, aₘ]_Δ` with `ZMod (m (m - 1))` sends the
class of a shift `c` to `c mod m (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayGradingDepressedDiscrEquiv_mk [IsDomain R] {m : ℕ} (h2 : (2 : R) ≠ 0)
    (hmR : (m : R) ≠ 0) (hm2 : 2 ≤ m) (c : ℤ) :
    shiftClassGroupAwayGradingDepressedDiscrEquiv h2 hmR hm2 c = c := by
  rw [shiftClassGroupAwayGradingDepressedDiscrEquiv, AddEquiv.trans_apply,
    ShiftClassGroup.equivZMod_mk, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv,
    map_intCast]

/-- **Homogeneous units away from the discriminant of the short Weierstrass equation.** Over a
domain in which `2 ≠ 0` and `3 ≠ 0`, the degrees of the homogeneous units of `R[a, b]_Δ`,
with `a, b` of weights `4, 6` and `Δ = -4 a³ - 27 b²`, are the multiples of `12`. -/
theorem homogeneousUnitDegrees_awayGrading_depressedDiscr_three_four_six [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    homogeneousUnitDegrees (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
        (depressedDiscr_three_mem_four_six R)) =
      AddSubgroup.zmultiples 12 :=
  homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_prime _ _
    (depressedDiscr_prime h2 (m := 3) (by exact_mod_cast h3) (by norm_num)
      (fun h ↦ absurd h (by omega)))

/-- Over a domain in which `2 ≠ 0` and `3 ≠ 0`, the shift classes of `R[a, b]_Δ`, with
`a, b` of weights `4, 6` and `Δ = -4 a³ - 27 b²`, form `ZMod 12`. -/
noncomputable def shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    ShiftClassGroup (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
        (depressedDiscr_three_mem_four_six R)) ≃+
      ZMod 12 :=
  -- The index `(12 : ℤ).natAbs` of `shiftClassGroupAwayGradingWeightedEquiv` reduces to `12`.
  shiftClassGroupAwayGradingWeightedEquiv _ _
    (depressedDiscr_prime h2 (m := 3) (by exact_mod_cast h3) (by norm_num)
      (fun h ↦ absurd h (by omega)))

/-- The identification of the shift classes of `R[a, b]_Δ` with `ZMod 12` sends the class of a
shift `c` to `c mod 12`. -/
@[simp]
theorem shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv_mk [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (c : ℤ) :
    shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv h2 h3 c = c :=
  shiftClassGroupAwayGradingWeightedEquiv_mk _ _ _ c

/-- The negative of the cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short
Weierstrass discriminant factor), has weight `12` when the variables have weights `4` and `6`. -/
theorem mem_weightedHomogeneousSubmodule_weierstrass (R : Type*) [CommRing R] :
    (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) ∈
      weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ) 12 := by
  have hneg := neg_mem (depressedDiscr_three_mem_four_six R)
  rwa [depressedDiscr_three, show -(-4 * X 0 ^ 3 - 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) =
    4 * X 0 ^ 3 + 27 * X 1 ^ 2 by ring] at hneg

/-- Over any integral domain `R` in which `(2 : R) ≠ 0` and `(3 : R) ≠ 0`, the negative of the
cubic depressed discriminant, `4 * X 0 ^ 3 + 27 * X 1 ^ 2` (the short Weierstrass discriminant
factor), is prime. -/
theorem prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
  have hassoc : Associated (depressedDiscr R 3)
      (4 * X 0 ^ 3 + 27 * X 1 ^ 2 : MvPolynomial (Fin 2) R) :=
    ⟨-1, by simp [depressedDiscr_three]; ring⟩
  exact hassoc.prime_iff.mp
    (depressedDiscr_prime h2 (m := 3) (by exact_mod_cast h3) (by norm_num)
      (fun h ↦ absurd h (by omega)))

/-- Inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2` in `R[a, b]` with weights `4, 6` over an integral
domain `R` with `(2 : R) ≠ 0` and `(3 : R) ≠ 0` yields shift class group `ZMod 12`. -/
noncomputable def shiftClassGroupAwayGradingWeierstrassEquiv [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    ShiftClassGroup (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
        (mem_weightedHomogeneousSubmodule_weierstrass R)) ≃+ ZMod 12 :=
  shiftClassGroupAwayGradingWeightedEquiv (![4, 6] : Fin 2 → ℤ)
    (mem_weightedHomogeneousSubmodule_weierstrass R)
    (prime_four_mul_X_pow_three_add_twentySeven_mul_X_sq h2 h3)

/-- The identification of the shift class group after inverting `4 * X 0 ^ 3 + 27 * X 1 ^ 2`
with `ZMod 12` sends the class of `d` to `d mod 12`. -/
@[simp]
theorem shiftClassGroupAwayGradingWeierstrassEquiv_mk [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (d : ℤ) :
    shiftClassGroupAwayGradingWeierstrassEquiv h2 h3 d = d :=
  shiftClassGroupAwayGradingWeightedEquiv_mk _ _ _ d

end TauCeti
