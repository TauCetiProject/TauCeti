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

For a normalized function `φ : A → R` on a monoid and an element `a` with unit mean, put
`Ψ(z) = M(z) - 1`. Its formal S-series is

`S(z) = (1 + z) Ψ⁻¹(z) / z`,

where the inverse is for substitution and division by `z` removes its zero constant
coefficient. The moment–cumulant equation identifies this series with `C₀⁻¹(z) / z`, where
`C₀(z) = C(z) - 1 = z R(z)`. In particular its constant coefficient is the inverse mean and
it is a unit power series. These are formal identities over a commutative ring; they assert
neither analytic convergence nor multiplicativity on free products.

The definition also makes sense without normalization, following the convention for
`momentSeries`; the interpretation as the inverse of `Ψ` and the cumulant comparison use
`φ 1 = 1`. Requiring a unit mean is the ring-valued form of the nonzero-mean condition over
a field.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 16–18.
* The formal construction uses Mathlib's `PowerSeries.substInvOfIsUnit` and its substitution
  inverse laws, and `PowerSeries.eq_X_mul_shift_add_const` to remove a factor of `X`.
-/

public section

open PowerSeries

namespace TauCeti

variable {R A : Type*} [CommRing R]

section Monoid

variable [Monoid A] (φ : A → R) (a : A)

/-- A unit mean gives a unit linear coefficient of the reduced moment series `Ψ = M - 1`. -/
theorem isUnit_coeff_one_momentSeries_sub_one (ha : IsUnit (φ a)) :
    IsUnit (coeff 1 (momentSeries φ a - 1)) := by
  simpa using ha

/-- A unit mean gives a unit linear coefficient of `C₀ = C - 1`. -/
theorem isUnit_coeff_one_freeCumulantSeries_sub_one (ha : IsUnit (φ a)) :
    IsUnit (coeff 1 (freeCumulantSeries φ a - 1)) := by
  simpa [coeff_one_freeCumulantSeries] using ha

/-- The formal S-series `(1 + X) Ψ⁻¹ / X` of an element with unit mean. For its usual
interpretation as an inverse-transform expression, the functional must satisfy `φ 1 = 1`.
The factor `X` is removed by shifting the coefficients of the compositional inverse. -/
noncomputable def sSeries (ha : IsUnit (φ a)) : R⟦X⟧ :=
  (1 + X) * mk (fun n => coeff (n + 1)
    ((momentSeries φ a - 1).substInvOfIsUnit (isUnit_coeff_one_momentSeries_sub_one φ a ha)))

/-- The defining expression for the formal S-series, with division by `X` written as a
coefficient shift. -/
theorem sSeries_def (ha : IsUnit (φ a)) :
    sSeries φ a ha = (1 + X) * mk (fun n => coeff (n + 1)
      ((momentSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_momentSeries_sub_one φ a ha))) := (rfl)

/-- Multiplication by `X` restores the compositional inverse in the definition of `S`. -/
theorem X_mul_sSeries (ha : IsUnit (φ a)) :
    X * sSeries φ a ha = (1 + X) * (momentSeries φ a - 1).substInvOfIsUnit
      (isUnit_coeff_one_momentSeries_sub_one φ a ha) := by
  rw [sSeries_def, ← mul_assoc, mul_comm X (1 + X), mul_assoc]
  congr 1
  simpa using (eq_X_mul_shift_add_const ((momentSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_momentSeries_sub_one φ a ha))).symm

/-- The constant coefficient of the S-series is the inverse of the mean. -/
@[simp]
theorem constantCoeff_sSeries (ha : IsUnit (φ a)) :
    constantCoeff (sSeries φ a ha) = Ring.inverse (φ a) := by
  rw [sSeries_def, map_mul, map_add, map_one, constantCoeff_X, add_zero, one_mul,
    constantCoeff_mk, zero_add, coeff_one_substInvOfIsUnit, ← Ring.inverse_of_isUnit]
  simp

/-- The S-series of an element with unit mean is a unit of the power series ring. -/
theorem isUnit_sSeries (ha : IsUnit (φ a)) : IsUnit (sSeries φ a ha) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_sSeries]
  exact ha.ringInverse

variable {φ}

/-- The cumulant expression for the S-series: `X S = C₀⁻¹`, where `C₀ = C - 1`. -/
theorem X_mul_sSeries_eq_substInvOfIsUnit (hφ : φ 1 = 1) (ha : IsUnit (φ a)) :
    X * sSeries φ a ha = (freeCumulantSeries φ a - 1).substInvOfIsUnit
      (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha) := by
  let I := (momentSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_momentSeries_sub_one φ a ha)
  have hI : HasSubst I := .substInvOfIsUnit _ _
  have hM : HasSubst (X * momentSeries φ a) := .of_constantCoeff_zero' (by simp)
  have hMI : (momentSeries φ a).subst I = 1 + X := by
    have h := (momentSeries φ a - 1).subst_substInvOfIsUnit_right
      (by simp [hφ]) (isUnit_coeff_one_momentSeries_sub_one φ a ha)
    rw [subst_sub hI, subst_one hI] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hcomp : (X * momentSeries φ a).subst I = (1 + X) * I := by
    rw [subst_mul hI, subst_X hI, hMI, mul_comm]
  rw [X_mul_sSeries]
  apply (freeCumulantSeries φ a - 1).eq_substInvOfIsUnit_of_subst_eq_X (by simp) _
    (.of_constantCoeff_zero' (by simp))
  rw [← hcomp, ← subst_comp_subst_apply hM hI, subst_sub hM, subst_one hM,
    freeCumulantSeries_subst_X_mul_momentSeries a hφ,
    subst_substInvOfIsUnit_right _ (by simp [hφ])]

/-- The formal S-series agrees with `C₀⁻¹ / X`, with division expressed by a coefficient
shift. This identifies the moment and cumulant definitions of the S-transform. -/
theorem sSeries_eq_shift_substInvOfIsUnit (hφ : φ 1 = 1) (ha : IsUnit (φ a)) :
    sSeries φ a ha = mk (fun n => coeff (n + 1)
      ((freeCumulantSeries φ a - 1).substInvOfIsUnit
        (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha))) := by
  apply X_mul_injective
  dsimp only
  rw [X_mul_sSeries_eq_substInvOfIsUnit a hφ ha]
  simpa using eq_X_mul_shift_add_const ((freeCumulantSeries φ a - 1).substInvOfIsUnit
    (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha))

/-- A series is the S-series if multiplying it by `X` gives a right compositional inverse
of `C₀ = C - 1`. -/
theorem eq_sSeries_of_subst_X_mul_eq (hφ : φ 1 = 1) (ha : IsUnit (φ a)) {S : R⟦X⟧}
    (hS : (freeCumulantSeries φ a - 1).subst (X * S) = X) : S = sSeries φ a ha := by
  apply X_mul_injective
  exact ((freeCumulantSeries φ a - 1).eq_substInvOfIsUnit_of_subst_eq_X
    (by simp) (isUnit_coeff_one_freeCumulantSeries_sub_one φ a ha)
    (.of_constantCoeff_zero' (by simp)) hS).trans
      (X_mul_sSeries_eq_substInvOfIsUnit a hφ ha).symm

/-- Equal moment series give equal S-series, even when the underlying monoids differ. -/
theorem sSeries_congr {B : Type*} [Monoid B] {ψ : B → R} {b : B}
    (ha : IsUnit (φ a)) (hb : IsUnit (ψ b))
    (h : momentSeries φ a = momentSeries ψ b) : sSeries φ a ha = sSeries ψ b hb := by
  rw [sSeries_def, sSeries_def]
  congr 1
  ext n
  simp only [coeff_mk]
  congr 1
  congr 1
  exact congrArg (· - 1) h

end Monoid

section Algebra

variable [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- A scalar variable of unit value has the constant S-series given by its inverse. -/
@[simp]
theorem sSeries_algebraMap (hφ : φ 1 = 1) (c : R) (hc : IsUnit c) :
    sSeries φ (algebraMap R A c) (by simpa [Algebra.algebraMap_eq_smul_one, hφ] using hc) =
      C (Ring.inverse c) := by
  have hC : freeCumulantSeries φ (algebraMap R A c) - 1 = C c * X := by
    ext (_ | _ | n)
    · simp
    · simp [Algebra.algebraMap_eq_smul_one, hφ]
    · have hz := freeCumulant_add_algebraMap (s := Finset.univ) φ (fun _ : Fin (n + 2) => 0) hφ
        (fun _ => c) (by simp)
      have hz' : freeCumulant φ (fun _ : Fin (n + 2) => algebraMap R A c) Finset.univ = 0 := by
        simpa only [zero_add] using hz.trans
          ((freeCumulantMultilinear_apply φ _).symm.trans
            ((freeCumulantMultilinear φ).map_coord_zero (0 : Fin (n + 2)) rfl))
      simp [coeff_freeCumulantSeries, hz', coeff_succ_mul_X]
  apply (eq_sSeries_of_subst_X_mul_eq (algebraMap R A c) hφ _ ?_).symm
  rw [hC, subst_mul (.of_constantCoeff_zero' (by simp)), subst_C,
    subst_X (.of_constantCoeff_zero' (by simp))]
  rw [← C_apply, mul_left_comm, ← map_mul, Ring.mul_inverse_cancel c hc, map_one, mul_one]

end Algebra

end TauCeti
