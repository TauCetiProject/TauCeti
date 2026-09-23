/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# The geometric mean of two positive elements

For a strictly positive element `a` of a unital algebra carrying a continuous functional calculus
and a nonnegative element `b`, the *geometric mean*

`geometricMean a b = √a * √(√a⁻¹ * b * √a⁻¹) * √a`

is the unique nonnegative solution `x` of the Riccati equation `x * a⁻¹ * x = b`. For positive
definite matrices, and for positive operators on a real Hilbert space, this is the classical
geometric mean. The element `geometricMean a⁻¹ b`, characterised here as the unique nonnegative
solution of `x * a * x = b`, is the linear map transporting a centred Gaussian law of covariance
`a` to one of covariance `b`, that is, the linear Brenier map from a nondegenerate source Gaussian
to a possibly degenerate target Gaussian.

The definition is phrased through Mathlib's `CFC.conjSqrt`, so all of the identities below reduce
to associativity together with `CFC.sqrt_mul_sqrt_self` and the uniqueness of nonnegative square
roots (`CFC.sqrt_unique`).

## Main declarations

* `TauCeti.geometricMean`: the geometric mean of two elements.
* `TauCeti.geometricMean_eq_sqrt_mul_mul`: the explicit square-root formula.
* `TauCeti.geometricMean_mul_ringInverse_mul_geometricMean`: it solves `x * a⁻¹ * x = b`.
* `TauCeti.eq_geometricMean_of_mul_ringInverse_mul`: it is the only nonnegative solution.
* `TauCeti.geometricMean_eq_iff`: the resulting characterisation.
* `TauCeti.geometricMean_comm`: the geometric mean is symmetric in its two arguments.
* `TauCeti.geometricMean_ringInverse_ringInverse`: it commutes with inversion.
* `TauCeti.geometricMean_add_geometricMean_le`: the arithmetic--geometric mean inequality.
* `TauCeti.eq_geometricMean_ringInverse_of_mul_mul`: the transport form `x * a * x = b`.

## References

* T. Ando, *Topics on operator inequalities*, Hokkaido University, 1978.
* W. Pusz and S. L. Woronowicz, *Functional calculus for sesquilinear forms and the purification
  map*, Rep. Math. Phys. **8** (1975), 159--170.
-/

public section

noncomputable section

open CFC Ring

namespace TauCeti

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A]

variable {a b x : A}

omit [IsSemitopologicalRing A] in
/-- Conjugation by a square root preserves nonnegativity. -/
theorem conjSqrt_nonneg [SeparatelyContinuousMul A] (c : A) (hb : 0 ≤ b := by cfc_tac) :
    0 ≤ conjSqrt c b := by
  simpa using conjSqrt_monotone (c := c) hb

omit [IsSemitopologicalRing A] in
/-- Moving a factor across a pair of square-root conjugations. This is pure associativity, and it
is the only computation behind the Riccati identities below. -/
theorem conjSqrt_mul_mul_conjSqrt [SeparatelyContinuousMul A] (c y w z : A) :
    conjSqrt c y * w * conjSqrt c z = conjSqrt c (y * conjSqrt c w * z) := by
  simp only [conjSqrt_apply, mul_assoc]

/-- The geometric mean `geometricMean a b = √a * √(√a⁻¹ * b * √a⁻¹) * √a` of two elements of a
unital algebra with a continuous functional calculus. The intended range of the definition is `a`
strictly positive and `b` nonnegative; the value is `0` whenever `a` fails to be nonnegative. -/
def geometricMean (a b : A) : A := conjSqrt a (sqrt (conjSqrt a⁻¹ʳ b))

theorem geometricMean_def (a b : A) :
    geometricMean a b = conjSqrt a (sqrt (conjSqrt a⁻¹ʳ b)) := (rfl)

@[simp]
theorem geometricMean_nonneg (a b : A) : 0 ≤ geometricMean a b := by
  rw [geometricMean_def, conjSqrt_apply]
  exact conjugate_nonneg_of_nonneg (sqrt_nonneg _) (sqrt_nonneg _)

/-- Outside the intended range, the geometric mean takes the junk value `0`. -/
theorem geometricMean_of_not_nonneg (ha : ¬0 ≤ a) (b : A) : geometricMean a b = 0 := by
  rw [geometricMean_def, conjSqrt_of_not_nonneg ha]

@[simp]
theorem geometricMean_zero (a : A) : geometricMean a 0 = 0 := by
  simp [geometricMean_def]

@[simp]
theorem zero_geometricMean (b : A) : geometricMean 0 b = 0 := by
  simp [geometricMean_def, conjSqrt_apply]

variable [T2Space A]

/-- The geometric mean written out through square roots rather than through `CFC.conjSqrt`. -/
theorem geometricMean_eq_sqrt_mul_mul (a b : A) :
    geometricMean a b = sqrt a * sqrt ((sqrt a)⁻¹ʳ * b * (sqrt a)⁻¹ʳ) * sqrt a := by
  rw [geometricMean_def, conjSqrt_apply, conjSqrt_apply, sqrt_ringInverse]

@[simp]
theorem one_geometricMean (b : A) : geometricMean 1 b = sqrt b := by
  simp [geometricMean_def, conjSqrt_apply]

@[simp]
theorem geometricMean_one (ha : IsStrictlyPositive a := by cfc_tac) :
    geometricMean a 1 = sqrt a := by
  rw [geometricMean_def, conjSqrt_one _ ha.ringInverse.nonneg, sqrt_ringInverse, conjSqrt_apply,
    inverse_mul_cancel_right _ _ (ha.isUnit_cfcSqrt a)]

@[simp]
theorem geometricMean_self (ha : IsStrictlyPositive a := by cfc_tac) :
    geometricMean a a = a := by
  rw [geometricMean_def, conjSqrt_ringInverse_self a ha, sqrt_one, conjSqrt_one a ha.nonneg]

/-- The geometric mean of `a` and `b` solves the Riccati equation `x * a⁻¹ * x = b`. -/
theorem geometricMean_mul_ringInverse_mul_geometricMean (ha : IsStrictlyPositive a := by cfc_tac)
    (hb : 0 ≤ b := by cfc_tac) : geometricMean a b * a⁻¹ʳ * geometricMean a b = b := by
  have h1 : conjSqrt a a⁻¹ʳ = 1 := by
    simpa [inverse_inverse ha.isUnit] using conjSqrt_ringInverse_self a⁻¹ʳ ha.ringInverse
  rw [geometricMean_def, conjSqrt_mul_mul_conjSqrt, h1, mul_one,
    sqrt_mul_sqrt_self _ (conjSqrt_nonneg _ hb), conjSqrt_conjSqrt_ringInverse a b ha]

/-- The Riccati equation `x * a⁻¹ * x = b` has at most one nonnegative solution. -/
theorem eq_geometricMean_of_mul_ringInverse_mul (h : x * a⁻¹ʳ * x = b)
    (ha : IsStrictlyPositive a := by cfc_tac) (hx : 0 ≤ x := by cfc_tac) :
    x = geometricMean a b := by
  have hy : conjSqrt a⁻¹ʳ x * conjSqrt a⁻¹ʳ x = conjSqrt a⁻¹ʳ b := by
    have hmul := conjSqrt_mul_mul_conjSqrt a⁻¹ʳ x 1 x
    rwa [mul_one, conjSqrt_one _ ha.ringInverse.nonneg, h] at hmul
  rw [geometricMean_def, sqrt_unique hy (conjSqrt_nonneg _ hx),
    conjSqrt_conjSqrt_ringInverse a x ha]

/-- The geometric mean of `a` and `b` is characterised as the nonnegative solution of the Riccati
equation `x * a⁻¹ * x = b`. -/
theorem geometricMean_eq_iff (ha : IsStrictlyPositive a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac)
    (hx : 0 ≤ x := by cfc_tac) : geometricMean a b = x ↔ x * a⁻¹ʳ * x = b :=
  ⟨fun h => h ▸ geometricMean_mul_ringInverse_mul_geometricMean ha hb,
    fun h => (eq_geometricMean_of_mul_ringInverse_mul h ha hx).symm⟩

@[simp]
theorem geometricMean_ringInverse_self (ha : IsStrictlyPositive a := by cfc_tac) :
    geometricMean a a⁻¹ʳ = 1 :=
  (eq_geometricMean_of_mul_ringInverse_mul (by rw [one_mul, mul_one]) ha zero_le_one).symm

/-- The geometric mean of two strictly positive elements is strictly positive. -/
theorem isStrictlyPositive_geometricMean (ha : IsStrictlyPositive a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) : IsStrictlyPositive (geometricMean a b) := by
  rw [geometricMean_def, isStrictlyPositive_conjSqrt_iff a _ ha]
  exact IsStrictlyPositive.sqrt _ ((isStrictlyPositive_conjSqrt_iff a⁻¹ʳ b ha.ringInverse).mpr hb)

/-- The inverse of the geometric mean conjugates `a` onto `b⁻¹`. -/
private theorem conjugate_geometricMean_ringInverse (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) :
    (geometricMean a b)⁻¹ʳ * a * (geometricMean a b)⁻¹ʳ = b⁻¹ʳ := by
  set X := geometricMean a b
  have hu : IsUnit X := (isStrictlyPositive_geometricMean ha hb).isUnit
  have hXa : X * a⁻¹ʳ * X = b := geometricMean_mul_ringInverse_mul_geometricMean ha hb.nonneg
  have hkey : b * (X⁻¹ʳ * a * X⁻¹ʳ) = 1 := by
    rw [← hXa]
    calc X * a⁻¹ʳ * X * (X⁻¹ʳ * a * X⁻¹ʳ)
        = X * a⁻¹ʳ * (X * X⁻¹ʳ) * a * X⁻¹ʳ := by simp only [mul_assoc]
      _ = 1 := by
          rw [mul_inverse_cancel X hu, mul_one, mul_assoc X a⁻¹ʳ a,
            inverse_mul_cancel a ha.isUnit, mul_one, mul_inverse_cancel X hu]
  have h1 : b⁻¹ʳ * (b * (X⁻¹ʳ * a * X⁻¹ʳ)) = b⁻¹ʳ * 1 := by rw [hkey]
  rwa [inverse_mul_cancel_left b _ hb.isUnit, mul_one] at h1

/-- The geometric mean is symmetric in its two arguments. -/
theorem geometricMean_comm (ha : IsStrictlyPositive a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) : geometricMean a b = geometricMean b a := by
  have hu : IsUnit (geometricMean a b) := (isStrictlyPositive_geometricMean ha hb).isUnit
  refine eq_geometricMean_of_mul_ringInverse_mul ?_ hb (geometricMean_nonneg a b)
  rw [← conjugate_geometricMean_ringInverse ha hb]
  calc geometricMean a b * ((geometricMean a b)⁻¹ʳ * a * (geometricMean a b)⁻¹ʳ) *
        geometricMean a b
      = geometricMean a b * (geometricMean a b)⁻¹ʳ * a *
        ((geometricMean a b)⁻¹ʳ * geometricMean a b) := by simp only [mul_assoc]
    _ = a := by rw [mul_inverse_cancel _ hu, inverse_mul_cancel _ hu, one_mul, mul_one]

/-- The geometric mean commutes with inversion. -/
theorem geometricMean_ringInverse_ringInverse (ha : IsStrictlyPositive a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) :
    geometricMean a⁻¹ʳ b⁻¹ʳ = (geometricMean a b)⁻¹ʳ := by
  refine (eq_geometricMean_of_mul_ringInverse_mul ?_ ha.ringInverse
    (isStrictlyPositive_geometricMean ha hb).ringInverse.nonneg).symm
  rw [inverse_inverse ha.isUnit]
  exact conjugate_geometricMean_ringInverse ha hb

/-- The **arithmetic--geometric mean inequality** for positive elements:
`geometricMean a b + geometricMean a b ≤ a + b`. -/
theorem geometricMean_add_geometricMean_le (ha : IsStrictlyPositive a := by cfc_tac)
    (hb : 0 ≤ b := by cfc_tac) : geometricMean a b + geometricMean a b ≤ a + b := by
  set c := conjSqrt a⁻¹ʳ b with hc
  have hc0 : 0 ≤ c := conjSqrt_nonneg _ hb
  have hsq : IsSelfAdjoint (1 - sqrt c) := (IsSelfAdjoint.one A).sub (sqrt_nonneg c).isSelfAdjoint
  have hexp : (1 - sqrt c) * (1 - sqrt c) = 1 + c - (sqrt c + sqrt c) := by
    rw [sub_mul, mul_sub, mul_sub, sqrt_mul_sqrt_self c hc0]
    noncomm_ring
  have hkey : sqrt c + sqrt c ≤ 1 + c := by
    have h := hsq.mul_self_nonneg
    rw [hexp] at h
    exact sub_nonneg.mp h
  have hmono := conjSqrt_monotone (c := a) hkey
  rw [map_add, map_add, conjSqrt_one a ha.nonneg, hc,
    conjSqrt_conjSqrt_ringInverse a b ha] at hmono
  rw [geometricMean_def]
  exact hmono

/-- The **transport identity**: `geometricMean a⁻¹ b` solves `x * a * x = b`. Read through the
covariances of two centred Gaussian laws, this is the linear Brenier map from the first to the
second. -/
theorem geometricMean_ringInverse_mul_mul_geometricMean_ringInverse
    (ha : IsStrictlyPositive a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    geometricMean a⁻¹ʳ b * a * geometricMean a⁻¹ʳ b = b := by
  have h := geometricMean_mul_ringInverse_mul_geometricMean ha.ringInverse hb
  rwa [inverse_inverse ha.isUnit] at h

/-- The equation `x * a * x = b` has at most one nonnegative solution. -/
theorem eq_geometricMean_ringInverse_of_mul_mul (h : x * a * x = b)
    (ha : IsStrictlyPositive a := by cfc_tac) (hx : 0 ≤ x := by cfc_tac) :
    x = geometricMean a⁻¹ʳ b := by
  refine eq_geometricMean_of_mul_ringInverse_mul ?_ ha.ringInverse hx
  rwa [inverse_inverse ha.isUnit]

end TauCeti
