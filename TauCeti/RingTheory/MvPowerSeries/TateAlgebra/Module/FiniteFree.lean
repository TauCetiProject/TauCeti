/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Pi
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Gauss norms and finite-coordinate presentations

Separating a finite tuple of coefficients is an isometry for the weighted Gauss norm and the
maximum norm on tuples of restricted series. The comparison works at every positive real
polyradius, for arbitrary variable sets and seminormed coefficient modules, including an empty
coordinate set. For ring-valued coordinates it identifies restricted families with a finite free
module over the native restricted-series ring, linearly for the convolution action.

Coefficient matrices act through the same matrices after this comparison, with entries included
as constant series. Thus finite free coefficient-module presentations can be transported to
Gauss-topological restricted families without changing their matrices or norms. These results
extend the algebraic comparisons in `Module.Pi`; no completeness is needed.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss

open _root_.MvPowerSeries

variable {σ ι R : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)]
  [SeminormedRing R] [∀ i, Module R (E i)] [∀ i, IsBoundedSMul R (E i)]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

variable (R c) in
/-- Separating finitely many coefficient coordinates preserves the weighted Gauss norm.
The target carries the maximum seminorm, also when the coordinate set is empty. -/
def piLinearIsometryEquiv : Gauss c (∀ i, E i) ≃ₗᵢ[R] ∀ i, Gauss c (E i) where
  toLinearEquiv := (toAddSubgroupLinearEquiv R).trans
    ((IsRestrictedFamily.piLinearEquiv R c).trans
      (LinearEquiv.piCongrRight fun _ ↦ (toAddSubgroupLinearEquiv R).symm))
  norm_map' a := by
    simp only [LinearEquiv.trans_apply, toAddSubgroupLinearEquiv_apply]
    let b : ∀ i, Gauss c (E i) := fun i ↦
      ofAddSubgroup (IsRestrictedFamily.piLinearEquiv R c a.toAddSubgroup i)
    have heq : (LinearEquiv.piCongrRight fun _ ↦ (toAddSubgroupLinearEquiv R).symm)
        (IsRestrictedFamily.piLinearEquiv R c a.toAddSubgroup) = b := by
      funext i
      simp only [LinearEquiv.piCongrRight_apply, toAddSubgroupLinearEquiv_symm_apply, b]
    rw [heq]
    have hb (i : ι) (t : σ →₀ ℕ) : b i t = a t i := by
      simp only [b, IsRestrictedFamily.piLinearEquiv_apply]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
      intro i
      apply norm_le_iff.mpr
      intro t
      rw [hb]
      exact (mul_le_mul_of_nonneg_right (norm_le_pi_norm (a t) i)
        (prod_pow_pos t).le).trans (norm_coeff_mul_prod_le a t)
    · apply norm_le_iff.mpr
      intro t
      have h (i : ι) : ‖a t i‖ ≤ (t.prod (c · ^ ·))⁻¹ * ‖b‖ := by
        rw [← hb]
        exact (norm_coeff_le (b i) t).trans
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm b i) (inv_nonneg.mpr (prod_pow_pos t).le))
      have hpi := (pi_norm_le_iff_of_nonneg
        (mul_nonneg (inv_nonneg.mpr (prod_pow_pos t).le) (norm_nonneg b))).mpr h
      calc
        ‖a t‖ * t.prod (c · ^ ·) ≤
            ((t.prod (c · ^ ·))⁻¹ * ‖b‖) * t.prod (c · ^ ·) :=
          mul_le_mul_of_nonneg_right hpi (prod_pow_pos t).le
        _ = ‖b‖ := by field_simp [(prod_pow_pos (c := c) t).ne']

/-- The isometric comparison takes each coordinate of each coefficient. -/
@[simp]
theorem piLinearIsometryEquiv_apply (a : Gauss c (∀ i, E i)) (i : ι) (t : σ →₀ ℕ) :
    piLinearIsometryEquiv R c a i t = a t i := by
  simp [piLinearIsometryEquiv]

/-- The inverse comparison assembles the coefficient vectors. -/
@[simp]
theorem piLinearIsometryEquiv_symm_apply (a : ∀ i, Gauss c (E i)) (t : σ →₀ ℕ) (i : ι) :
    (piLinearIsometryEquiv R c).symm a t i = a i t := by
  have h := piLinearIsometryEquiv_apply (R := R) ((piLinearIsometryEquiv R c).symm a) i t
  simpa using h.symm

/-- Finite-support inclusion commutes with the normed coordinate comparison. -/
@[simp]
theorem piLinearIsometryEquiv_ofFinsupp (a : (σ →₀ ℕ) →₀ ∀ i, E i) (i : ι) :
    piLinearIsometryEquiv R c (ofFinsupp R c a) i =
      ofFinsupp R c (Finsupp.mapRange.linearMap (LinearMap.proj (R := R) i) a) := by
  ext t
  simp

section FiniteFree

variable {K : Type*} [NormedRing K] [IsUltrametricDist K]

/-- Restricted families in a finite free coefficient module are isometrically a finite free
module over the restricted-series ring. Linearity uses convolution by scalar series. -/
def piRingLinearIsometryEquiv (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    Gauss c (ι → K) ≃ₗᵢ[IsRestricted.subring (R := K) c]
      ι → IsRestricted.subring (R := K) c where
  toLinearEquiv :=
    { toAddSubgroupAddEquiv.trans (IsRestrictedFamily.piRingLinearEquiv K c).toAddEquiv with
      map_smul' := fun f a ↦ by simp }
  norm_map' a := by
    have h (i : ι) :
        ‖IsRestrictedFamily.piRingLinearEquiv K c a.toAddSubgroup i‖ =
          ‖piLinearIsometryEquiv K c a i‖ := by
      rw [← norm_subringLinearEquiv]
      congr 1
      ext t
      simp
    have hpi : ‖IsRestrictedFamily.piRingLinearEquiv K c a.toAddSubgroup‖ =
        ‖piLinearIsometryEquiv K c a‖ := by
      simp only [Pi.norm_def]
      congr 2
      funext i
      exact NNReal.eq (h i)
    simpa using hpi.trans ((piLinearIsometryEquiv K c).norm_map a)

/-- Each coordinate series has the corresponding coordinate coefficients. -/
@[simp]
theorem coeff_piRingLinearIsometryEquiv (a : Gauss c (ι → K)) (i : ι) (t : σ →₀ ℕ) :
    _root_.MvPowerSeries.coeff t (piRingLinearIsometryEquiv c a i : MvPowerSeries σ K) =
      a t i := by
  simp [piRingLinearIsometryEquiv]

/-- The inverse finite-free isometry assembles a tuple of series coefficientwise. -/
@[simp]
theorem piRingLinearIsometryEquiv_symm_apply
    (a : ι → IsRestricted.subring (R := K) c) (t : σ →₀ ℕ) (i : ι) :
    (piRingLinearIsometryEquiv c).symm a t i =
      _root_.MvPowerSeries.coeff t (a i : MvPowerSeries σ K) := by
  have h := coeff_piRingLinearIsometryEquiv ((piRingLinearIsometryEquiv c).symm a) i t
  simpa using h.symm

end FiniteFree

section Matrices

variable {κ K : Type*} [Fintype κ] [NormedCommRing K] [IsUltrametricDist K]

/-- A bounded coefficient matrix induces the same matrix on restricted series, with each
entry included as a constant series. This identifies the matrix in a transported finite free
presentation. The bound is on the coefficient map, not on individual entries. -/
theorem _root_.Matrix.piRingLinearIsometryEquiv_mapLinearMap (A : Matrix κ ι K) {C : ℝ}
    (hA : ∀ x, ‖A.mulVecLin x‖ ≤ C * ‖x‖) (a : Gauss c (ι → K)) :
    piRingLinearIsometryEquiv c (mapLinearMap A.mulVecLin hA a) =
      (A.map (algebraMap K (IsRestricted.subring (R := K) c))).mulVec
        (piRingLinearIsometryEquiv c a) := by
  ext i t
  simp [Matrix.mulVec, dotProduct, coe_algebraMap_isRestrictedSubring,
    _root_.MvPowerSeries.coeff_C_mul]

end Matrices

end TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss
