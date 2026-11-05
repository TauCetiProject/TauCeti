/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Series
import TauCeti.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The formal S-series

For a normalized functional and an element with invertible mean, write
`Ψ = M - 1` and `C₀ = C - 1 = X * R`, where `M`, `C`, and `R` are the moment,
free cumulant, and R-series. The formal S-series is

`S(X) = (1 + X) Ψ⁻¹(X) / X = C₀⁻¹(X) / X`.

Here inverses are compositional inverses, not multiplicative inverses. Division by `X`
is the coefficient shift of a series whose constant coefficient is zero. We prove the
agreement of the two formulas, both inverse equations for `X * S`, and uniqueness.
These identities provide the formal change of coordinates used for multiplicative free
convolution. They do not assert an analytic inverse or the multiplicative convolution theorem.

The construction works over a commutative ring when the mean is a unit. Over a field this
is precisely the nonzero-mean condition. No positivity or trace assumption is used.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 18.

The compositional inverses and their uniqueness are Mathlib's
`PowerSeries.substInvOfIsUnit` and `PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X`.
-/

public section

open PowerSeries

namespace TauCeti

variable {R A : Type*} [CommRing R]

section Monoid

variable [Monoid A]

/-- The linear coefficient of `M - 1` is the mean, so an invertible mean makes it
invertible for composition when the functional is normalized. -/
theorem isUnit_coeff_one_momentSeries_sub_one (φ : A → R) (a : A)
    (hmean : IsUnit (φ a)) : IsUnit (coeff 1 (momentSeries φ a - 1)) := by
  simpa using hmean

/-- The linear coefficient of `C - 1` is the mean. -/
theorem isUnit_coeff_one_freeCumulantSeries_sub_one (φ : A → R) (a : A)
    (hmean : IsUnit (φ a)) : IsUnit (coeff 1 (freeCumulantSeries φ a - 1)) := by
  simpa [coeff_one_freeCumulantSeries] using hmean

/-- The formal S-series `(1 + X) Ψ⁻¹(X) / X`, where `Ψ = M - 1`. The mean must be a unit;
normalization of the functional is imposed separately in the inverse identities. -/
noncomputable def sSeries (φ : A → R) (a : A) (hmean : IsUnit (φ a)) : R⟦X⟧ :=
  (1 + X) * mk (fun n ↦ coeff (n + 1) ((momentSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_momentSeries_sub_one φ a hmean)))

/-- Multiplying the S-series by `X` removes the coefficient shift in its definition.
The compositional inverse has zero constant coefficient, so no remainder is lost. -/
theorem X_mul_sSeries (φ : A → R) (a : A) (hmean : IsUnit (φ a)) :
    X * sSeries φ a hmean = (1 + X) * (momentSeries φ a - 1).substInvOfIsUnit
      (isUnit_coeff_one_momentSeries_sub_one φ a hmean) := by
  have h := ((momentSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_momentSeries_sub_one φ a hmean)).eq_X_mul_shift_add_const
  simp only [constantCoeff_substInvOfIsUnit, map_zero, add_zero] at h
  rw [sSeries, mul_left_comm, ← h]

/-- The constant coefficient of the S-series is the inverse of the mean. -/
@[simp]
theorem constantCoeff_sSeries (φ : A → R) (a : A) (hmean : IsUnit (φ a)) :
    constantCoeff (sSeries φ a hmean) = ↑hmean.unit⁻¹ := by
  have hu : (isUnit_coeff_one_momentSeries_sub_one φ a hmean).unit = hmean.unit := by
    apply Units.ext
    simp
  simp only [sSeries, map_mul, map_add, map_one, constantCoeff_X, add_zero,
    one_mul, constantCoeff_mk, Nat.zero_add, coeff_one_substInvOfIsUnit, hu]

/-- The S-series is a multiplicative unit, since its constant coefficient is a unit. -/
theorem isUnit_sSeries (φ : A → R) (a : A) (hmean : IsUnit (φ a)) :
    IsUnit (sSeries φ a hmean) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_sSeries]
  exact Units.isUnit _

/-- Equal moment series give equal S-series, even in different ambient monoids. -/
theorem sSeries_congr {B : Type*} [Monoid B] {φ : A → R} {ψ : B → R} {a : A} {b : B}
    (h : momentSeries φ a = momentSeries ψ b) (ha : IsUnit (φ a)) (hb : IsUnit (ψ b)) :
    sSeries φ a ha = sSeries ψ b hb := by
  apply X_mul_cancel
  rw [X_mul_sSeries, X_mul_sSeries]
  congr 2
  rw [h]

variable {φ : A → R} (a : A) (hφ : φ 1 = 1) (hmean : IsUnit (φ a))

include hφ

/-- The nonconstant cumulant series evaluated at `X * M` is the nonconstant moment series. -/
theorem freeCumulantSeries_sub_one_subst_X_mul_momentSeries :
    (freeCumulantSeries φ a - 1).subst (X * momentSeries φ a) = momentSeries φ a - 1 := by
  rw [subst_sub (.of_constantCoeff_zero' (by simp)), subst_one
    (.of_constantCoeff_zero' (by simp)), freeCumulantSeries_subst_X_mul_momentSeries a hφ]

/-- The inverse of `C - 1` is `(1 + X)` times the inverse of `M - 1`.
This is the moment–cumulant change of coordinates underlying the S-series. -/
theorem substInvOfIsUnit_freeCumulantSeries_sub_one :
    (freeCumulantSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_freeCumulantSeries_sub_one φ a hmean) =
      (1 + X) * (momentSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_momentSeries_sub_one φ a hmean) := by
  let Q := (momentSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_momentSeries_sub_one φ a hmean)
  have hQ : HasSubst Q := .substInvOfIsUnit _ _
  have hM : (momentSeries φ a).subst Q = 1 + X := by
    have h := (momentSeries φ a - 1).subst_substInvOfIsUnit_right
      (by simp [hφ]) (isUnit_coeff_one_momentSeries_sub_one φ a hmean)
    rw [subst_sub hQ, subst_one hQ] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hchange : ((X * momentSeries φ a).subst Q) = (1 + X) * Q := by
    rw [subst_mul hQ, subst_X hQ, hM, mul_comm]
  apply Eq.symm
  apply (freeCumulantSeries φ a - 1).eq_substInvOfIsUnit_of_subst_eq_X
    (by simp) (isUnit_coeff_one_freeCumulantSeries_sub_one φ a hmean)
    (.of_constantCoeff_zero' (by simp))
  rw [← hchange, ← subst_comp_subst_apply
    (.of_constantCoeff_zero' (by simp)) hQ,
    freeCumulantSeries_sub_one_subst_X_mul_momentSeries a hφ]
  exact (momentSeries φ a - 1).subst_substInvOfIsUnit_right (by simp [hφ]) _

/-- The S-series also equals `C₀⁻¹(X) / X`, where `C₀ = C - 1 = X * R`.
In particular, `X * S` is the compositional inverse of the nonconstant cumulant series. -/
theorem X_mul_sSeries_eq_substInvOfIsUnit :
    X * sSeries φ a hmean = (freeCumulantSeries φ a - 1).substInvOfIsUnit
      (isUnit_coeff_one_freeCumulantSeries_sub_one φ a hmean) := by
  rw [X_mul_sSeries, substInvOfIsUnit_freeCumulantSeries_sub_one a hφ hmean]

/-- The cumulant-inverse formula for the S-series, with division by `X` expressed
as a coefficient shift. -/
theorem sSeries_eq_shift_substInvOfIsUnit :
    sSeries φ a hmean = mk (fun n ↦ coeff (n + 1)
      ((freeCumulantSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_freeCumulantSeries_sub_one φ a hmean))) := by
  apply X_mul_cancel
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ hmean]
  simpa using ((freeCumulantSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_freeCumulantSeries_sub_one φ a hmean)).eq_X_mul_shift_add_const

/-- The right inverse equation `(C - 1)(X * S) = X`. -/
theorem freeCumulantSeries_sub_one_subst_X_mul_sSeries :
    (freeCumulantSeries φ a - 1).subst (X * sSeries φ a hmean) = X := by
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ hmean]
  exact (freeCumulantSeries φ a - 1).subst_substInvOfIsUnit_right (by simp) _

/-- The left inverse equation `(X * S)(C - 1) = X`. -/
theorem X_mul_sSeries_subst_freeCumulantSeries_sub_one :
    (X * sSeries φ a hmean).subst (freeCumulantSeries φ a - 1) = X := by
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ hmean]
  exact (freeCumulantSeries φ a - 1).subst_substInvOfIsUnit_left (by simp) _

/-- The S-series is characterized by the right inverse equation for `C - 1`. -/
theorem eq_sSeries_iff {S : R⟦X⟧} :
    S = sSeries φ a hmean ↔ (freeCumulantSeries φ a - 1).subst (X * S) = X := by
  constructor
  · rintro rfl
    exact freeCumulantSeries_sub_one_subst_X_mul_sSeries a hφ hmean
  · intro h
    apply X_mul_cancel
    rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ hmean]
    exact (freeCumulantSeries φ a - 1).eq_substInvOfIsUnit_of_subst_eq_X (by simp)
      _ (.of_constantCoeff_zero' (by simp)) h

end Monoid

section Algebra

variable [Semiring A] [Algebra R A]

/-- The S-series of a scalar law with unit scalar is the constant inverse scalar.
The unit hypothesis is essential for the compositional inverse. -/
@[simp]
theorem sSeries_algebraMap (φ : A →ₗ[R] R) (hφ : φ 1 = 1) (c : Rˣ) :
    sSeries φ (algebraMap R A (c : R))
      (by simp [Algebra.algebraMap_eq_smul_one, hφ]) = C (↑c⁻¹ : R) := by
  symm
  apply (eq_sSeries_iff _ hφ _).2
  have hC : freeCumulantSeries φ (algebraMap R A (c : R)) - 1 = C (c : R) * X := by
    rw [freeCumulantSeries_eq_one_add_X_mul_rSeries, rSeries_algebraMap hφ,
      add_sub_cancel_left, mul_comm]
  rw [hC, subst_mul (.of_constantCoeff_zero' (by simp)), subst_C,
    subst_X (.of_constantCoeff_zero' (by simp))]
  rw [← C_apply, mul_left_comm, ← map_mul]
  simp

end Algebra

end TauCeti
