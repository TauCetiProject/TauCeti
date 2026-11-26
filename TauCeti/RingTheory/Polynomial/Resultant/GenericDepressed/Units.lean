/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.HomogeneousUnits
public import TauCeti.RingTheory.Polynomial.Resultant.GenericDepressed.Basic

/-!
# Homogeneous units away from the generic depressed discriminant

Let `Δ = depressedDiscr R m` be the discriminant of the generic depressed polynomial
`Xᵐ + a₂ Xᵐ⁻² + ⋯ + aₘ` over `R[a₂, …, aₘ]`, where `aⱼ` has weight `j`. It is weighted homogeneous
of weight `m (m - 1)`, and prime over a domain in which `2 ≠ 0` and `m ≥ 2` is invertible, for
instance over a field of characteristic `0`. So the degrees of the homogeneous units of
`R[a₂, …, aₘ]_Δ` are the multiples of `m (m - 1)`
(`homogeneousUnitDegrees_awayGrading_depressedDiscr`), and its shift classes form
`ZMod (m (m - 1))` (`shiftClassGroupAwayGradingDepressedDiscrEquiv`).

Geometrically, `𝔾_m` acts on the monic polynomials of degree `m` with roots of sum zero by scaling
the roots, `x ↦ t x`, which multiplies `aⱼ` by `tʲ`. The polynomials with distinct roots are the
invariant open subscheme `{Δ ≠ 0}`, whose graded ring is `R[a₂, …, aₘ]_Δ`. For `m = 2` the degrees
are `2ℤ` and for `m = 3` they are `6ℤ`.

The case `m = 3` with doubled weights is the graded ring of the short Weierstrass equations: the
curve `y² = x³ + a x + b` is invariant under `(x, y, a, b) ↦ (t² x, t³ y, t⁴ a, t⁶ b)`, and its
discriminant `-16 (4 a³ + 27 b²)` is `16` times `depressedDiscr R 3 = -4 a³ - 27 b²`, a unit
multiple when `2` is invertible. With `a, b` of weights `4, 6`, the discriminant has weight `12`
(`depressedDiscr_three_mem_four_six`), and when `2 ≠ 0` and `3` is invertible, for instance over a
field of characteristic neither `2` nor `3`, the degrees of the homogeneous units of `R[a, b]_Δ`
are the multiples of `12` (`homogeneousUnitDegrees_awayGrading_depressedDiscr_three_four_six`), so
its shift classes form `ZMod 12` (`shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv`).
This is the graded ring behind Mumford's computation `Pic M_{1,1} ≅ ℤ/12`.

## Main results

* `TauCeti.homogeneousUnitDegrees_awayGrading_depressedDiscr`: the homogeneous unit degrees of
  `R[a₂, …, aₘ]_Δ` are the multiples of `m (m - 1)`.
* `TauCeti.shiftClassGroupAwayGradingDepressedDiscrEquiv`: the shift classes of `R[a₂, …, aₘ]_Δ`
  form `ZMod (m (m - 1))`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_depressedDiscr_three_four_six`,
  `TauCeti.shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv`: for the weights `4, 6`, the
  homogeneous unit degrees of `R[a, b]_Δ` are the multiples of `12`, and its shift classes form
  `ZMod 12`.

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
`2 ≠ 0` and `m ≥ 2` is invertible, the degrees of the homogeneous units of `R[a₂, …, aₘ]_Δ`, with
`aⱼ` of weight `j` and `Δ = depressedDiscr R m`, are the multiples of `m (m - 1)`. -/
theorem homogeneousUnitDegrees_awayGrading_depressedDiscr [IsDomain R] {m : ℕ} (h2 : (2 : R) ≠ 0)
    (hm : IsUnit (m : R)) (hm2 : 2 ≤ m) :
    homogeneousUnitDegrees (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m)) =
      AddSubgroup.zmultiples (m * (m - 1) : ℤ) :=
  homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_prime _ _
    (depressedDiscr_prime h2 hm hm2)

/-- Over a domain in which `2 ≠ 0` and `m ≥ 2` is invertible, the shift classes of
`R[a₂, …, aₘ]_Δ`, with `aⱼ` of weight `j` and `Δ = depressedDiscr R m`, form `ZMod (m (m - 1))`. -/
noncomputable def shiftClassGroupAwayGradingDepressedDiscrEquiv [IsDomain R] {m : ℕ}
    (h2 : (2 : R) ≠ 0) (hm : IsUnit (m : R)) (hm2 : 2 ≤ m) :
    ShiftClassGroup (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (depressedWeight m)) (depressedDiscr_mem R m)) ≃+
      ZMod (m * (m - 1)) :=
  (shiftClassGroupAwayGradingWeightedEquiv _ (depressedDiscr_mem R m)
    (depressedDiscr_prime h2 hm hm2)).trans
    (ZMod.ringEquivCongr (by rw [Int.natAbs_mul, Int.natAbs_natCast]; congr 1; omega)).toAddEquiv

/-- The identification of the shift classes of `R[a₂, …, aₘ]_Δ` with `ZMod (m (m - 1))` sends the
class of a shift `c` to `c mod m (m - 1)`. -/
@[simp]
theorem shiftClassGroupAwayGradingDepressedDiscrEquiv_mk [IsDomain R] {m : ℕ} (h2 : (2 : R) ≠ 0)
    (hm : IsUnit (m : R)) (hm2 : 2 ≤ m) (c : ℤ) :
    shiftClassGroupAwayGradingDepressedDiscrEquiv h2 hm hm2 c = c := by
  simp [shiftClassGroupAwayGradingDepressedDiscrEquiv]

/-- **Homogeneous units away from the discriminant of the short Weierstrass equation.** Over a
domain in which `2 ≠ 0` and `3` is invertible, the degrees of the homogeneous units of `R[a, b]_Δ`,
with `a, b` of weights `4, 6` and `Δ = -4 a³ - 27 b²`, are the multiples of `12`. -/
theorem homogeneousUnitDegrees_awayGrading_depressedDiscr_three_four_six [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) :
    homogeneousUnitDegrees (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
        (depressedDiscr_three_mem_four_six R)) =
      AddSubgroup.zmultiples 12 :=
  homogeneousUnitDegrees_awayGrading_weightedHomogeneousSubmodule_of_prime _ _
    (depressedDiscr_prime h2 (by exact_mod_cast h3) (by norm_num))

/-- Over a domain in which `2 ≠ 0` and `3` is invertible, the shift classes of `R[a, b]_Δ`, with
`a, b` of weights `4, 6` and `Δ = -4 a³ - 27 b²`, form `ZMod 12`. -/
noncomputable def shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) :
    ShiftClassGroup (GradedAlgebra.awayGrading
        (weightedHomogeneousSubmodule R (![4, 6] : Fin 2 → ℤ))
        (depressedDiscr_three_mem_four_six R)) ≃+
      ZMod 12 :=
  -- The index `(12 : ℤ).natAbs` of `shiftClassGroupAwayGradingWeightedEquiv` reduces to `12`.
  shiftClassGroupAwayGradingWeightedEquiv _ _ (depressedDiscr_prime h2 (by exact_mod_cast h3)
    (by norm_num))

/-- The identification of the shift classes of `R[a, b]_Δ` with `ZMod 12` sends the class of a
shift `c` to `c mod 12`. -/
@[simp]
theorem shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv_mk [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : IsUnit (3 : R)) (c : ℤ) :
    shiftClassGroupAwayGradingDepressedDiscrThreeFourSixEquiv h2 h3 c = c :=
  shiftClassGroupAwayGradingWeightedEquiv_mk _ _ _ c

end TauCeti
