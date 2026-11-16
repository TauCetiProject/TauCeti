/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Inverse-coercive ellipticity

For nonsymmetric matrices, a lower bound on the quadratic form of the inverse is different
from an upper operator bound. This file defines almost-everywhere inverse-coercive
ellipticity and converts it to the operator-bound convention used by the energy estimates.
The forward conversion keeps the upper constant; the reverse conversion changes an operator
bound `M` to `M² / λ`. Neither conversion requires symmetry or coefficient continuity.

The inverse-coercive convention and the argument deriving the mixed bound follow
S. Armstrong and J. Kempe, *Formalization of De Giorgi–Nash–Moser theory in Lean*
(arXiv:2604.05984), specifically the `EllipticCoeff`, `quadratic_upper` and `mixed_bound`
construction. No formalization code is copied.
-/

public section

open MeasureTheory Set Matrix
open scoped Matrix

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Matrix ι ι ℝ} {lam Lam M : ℝ}

/-- A positive quadratic lower bound makes even a nonsymmetric real matrix invertible. -/
theorem isUnit_of_quadratic_lower_bound (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A *ᵥ ξ)) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : A *ᵥ (v - w) = 0 := by simp [mulVec_sub, hvw]
  have h := hA (WithLp.toLp 2 (v - w))
  simp only [hz, dotProduct_zero] at h
  have hn : ‖(WithLp.toLp 2 (v - w) : EuclideanSpace ℝ ι)‖ = 0 := by
    have hs := nonpos_of_mul_nonpos_right h hlam
    nlinarith [norm_nonneg (WithLp.toLp 2 (v - w) : EuclideanSpace ℝ ι)]
  have hz' : v - w = 0 := by simpa using congrArg WithLp.ofLp (norm_eq_zero.mp hn)
  exact sub_eq_zero.mp hz'

/-- Inverse coercivity controls the squared norm of the image by its diagonal energy. -/
theorem norm_mulVec_sq_le_of_inverse_lower_bound (hLam : 0 < Lam)
    (hinv : ∀ ξ : EuclideanSpace ℝ ι,
      Lam⁻¹ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ)) (ξ : EuclideanSpace ℝ ι) :
    ‖(WithLp.toLp 2 (A *ᵥ ξ) : EuclideanSpace ℝ ι)‖ ^ 2 ≤
      Lam * (ξ ⬝ᵥ (A *ᵥ ξ)) := by
  have hA := Matrix.isUnit_nonsing_inv_iff.mp
    (isUnit_of_quadratic_lower_bound (inv_pos.mpr hLam) hinv)
  have h := hinv (WithLp.toLp 2 (A *ᵥ ξ))
  rw [WithLp.ofLp_toLp, mulVec_mulVec,
    A.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det A).mp hA), one_mulVec,
    dotProduct_comm] at h
  exact (inv_mul_le_iff₀ hLam).mp h

/-- Inverse coercivity implies the mixed bound with the same upper constant. -/
theorem abs_dotProduct_mulVec_le_of_inverse_lower_bound (hLam : 0 < Lam)
    (hinv : ∀ ξ : EuclideanSpace ℝ ι,
      Lam⁻¹ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ)) (η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (A *ᵥ ξ)
  have hcs (ζ : EuclideanSpace ℝ ι) : |ζ ⬝ᵥ (A *ᵥ ξ)| ≤ ‖ζ‖ * ‖v‖ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, v, dotProduct_comm] using
      abs_real_inner_le_norm ζ v
  have he : ‖v‖ ^ 2 ≤ Lam * (ξ ⬝ᵥ (A *ᵥ ξ)) :=
    norm_mulVec_sq_le_of_inverse_lower_bound hLam hinv ξ
  have hn : ‖v‖ ≤ Lam * ‖ξ‖ := by
    have hc := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (hcs ξ)) hLam.le
    by_cases hv : v = 0
    · simpa only [hv, norm_zero] using mul_nonneg hLam.le (norm_nonneg ξ)
    exact le_of_mul_le_mul_left (by nlinarith [he, hc]) (norm_pos_iff.mpr hv)
  exact (hcs η).trans (by nlinarith [norm_nonneg η])

/-- An operator bound and coercivity give inverse coercivity with constant `M² / λ`. -/
theorem inverse_quadratic_lower_bound_of_bounds (hlam : 0 < lam)
    (hlower : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A *ᵥ ξ))
    (hupper : ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ (A *ᵥ ξ)| ≤ M * ‖η‖ * ‖ξ‖) (ξ : EuclideanSpace ℝ ι) :
    (M ^ 2 / lam)⁻¹ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  have hM : 0 < M := by
    have hn : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hξ)
    have hle := (hlower ξ).trans ((le_abs_self _).trans (hupper ξ ξ))
    have : lam ≤ M := (mul_le_mul_iff_left₀ hn).mp (by nlinarith [hle])
    exact hlam.trans_le this
  have hA := isUnit_of_quadratic_lower_bound hlam hlower
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (A⁻¹ *ᵥ ξ)
  have hav : A *ᵥ v = ξ := by
    simp [v, mulVec_mulVec, A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
  have hl := hlower v
  rw [hav, dotProduct_comm] at hl
  have hu := hupper ξ v
  rw [hav] at hu
  have hself : ξ ⬝ᵥ ξ = ‖ξ‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      real_inner_self_eq_norm_sq ξ
  rw [hself, abs_of_nonneg (sq_nonneg _)] at hu
  have hn : ‖ξ‖ ≤ M * ‖v‖ :=
    le_of_mul_le_mul_left (by nlinarith [hu]) (norm_pos_iff.mpr hξ)
  have hs : ‖ξ‖ ^ 2 ≤ M ^ 2 * ‖v‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg ξ) hn]
  rw [inv_div, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hM)]
  have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg M)
  have hh' := mul_le_mul_of_nonneg_left hs hlam.le
  simpa only [v, WithLp.ofLp_toLp] using le_trans hh' (by nlinarith [hh])

variable {X : Type*} [MeasurableSpace X] {mu : Measure X} {Ω Ω' : Set X}
  {a b : X → Matrix ι ι ℝ}

/-- Almost-everywhere inverse-coercive ellipticity: both `a` and its inverse have positive
quadratic lower bounds, with constants `λ` and `Λ⁻¹`. No symmetry is required. -/
def IsUniformlyEllipticAE (mu : Measure X) (Ω : Set X) (a : X → Matrix ι ι ℝ)
    (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧ ∀ᵐ x ∂mu.restrict Ω,
    (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) ∧
      ∀ ξ : EuclideanSpace ℝ ι, Lam⁻¹ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ((a x)⁻¹ *ᵥ ξ)

/-- The two quadratic lower bounds characterize inverse-coercive ellipticity. -/
theorem isUniformlyEllipticAE_iff : IsUniformlyEllipticAE mu Ω a lam Lam ↔
    0 < lam ∧ lam ≤ Lam ∧ ∀ᵐ x ∂mu.restrict Ω,
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) ∧
        ∀ ξ : EuclideanSpace ℝ ι, Lam⁻¹ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ((a x)⁻¹ *ᵥ ξ) := Iff.rfl

namespace IsUniformlyEllipticAE

/-- The lower ellipticity constant is positive. -/
@[grind →]
theorem pos (h : IsUniformlyEllipticAE mu Ω a lam Lam) : 0 < lam := h.1

/-- The constants of inverse-coercive ellipticity are ordered. -/
@[grind →]
theorem le (h : IsUniformlyEllipticAE mu Ω a lam Lam) : lam ≤ Lam := h.2.1

/-- Both quadratic lower bounds hold on a common full-measure set, for every vector. -/
theorem ae_bounds (h : IsUniformlyEllipticAE mu Ω a lam Lam) :
    ∀ᵐ x ∂mu.restrict Ω,
      (∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) ∧
        ∀ ξ : EuclideanSpace ℝ ι, Lam⁻¹ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ((a x)⁻¹ *ᵥ ξ) := h.2.2

/-- The principal matrix is invertible almost everywhere in the domain. -/
theorem ae_isUnit (h : IsUniformlyEllipticAE mu Ω a lam Lam) :
    ∀ᵐ x ∂mu.restrict Ω, IsUnit (a x) :=
  h.ae_bounds.mono fun _ hx => isUnit_of_quadratic_lower_bound h.pos hx.1

/-- Inverse-coercive ellipticity supplies the mixed bound with the same `Λ`. -/
theorem ae_upper_bound (h : IsUniformlyEllipticAE mu Ω a lam Lam) :
    ∀ᵐ x ∂mu.restrict Ω, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  filter_upwards [h.ae_bounds] with x hx
  exact abs_dotProduct_mulVec_le_of_inverse_lower_bound (h.pos.trans_le h.le) hx.2

/-- Lowering the positive lower constant and raising the upper constant preserves
inverse-coercive ellipticity. -/
theorem mono_constants (h : IsUniformlyEllipticAE mu Ω a lam Lam) {lam' Lam' : ℝ}
    (hlam' : 0 < lam') (hle : lam' ≤ lam) (hLam : Lam ≤ Lam') :
    IsUniformlyEllipticAE mu Ω a lam' Lam' := by
  refine ⟨hlam', hle.trans (h.le.trans hLam), ?_⟩
  filter_upwards [h.ae_bounds] with x hx
  exact ⟨fun ξ => (mul_le_mul_of_nonneg_right hle (sq_nonneg _)).trans (hx.1 ξ),
    fun ξ => (mul_le_mul_of_nonneg_right
      (inv_anti₀ (h.pos.trans_le h.le) hLam) (sq_nonneg _)).trans (hx.2 ξ)⟩

/-- Restricting the domain preserves inverse-coercive ellipticity. -/
theorem mono_set (h : IsUniformlyEllipticAE mu Ω a lam Lam) (hΩ : Ω' ⊆ Ω) :
    IsUniformlyEllipticAE mu Ω' a lam Lam :=
  ⟨h.pos, h.le, h.ae_bounds.filter_mono (ae_mono (Measure.restrict_mono hΩ le_rfl))⟩

/-- Changing the coefficient field on a null set preserves inverse-coercive ellipticity. -/
theorem congr_ae (h : IsUniformlyEllipticAE mu Ω a lam Lam)
    (hab : a =ᵐ[mu.restrict Ω] b) : IsUniformlyEllipticAE mu Ω b lam Lam := by
  refine ⟨h.pos, h.le, ?_⟩
  filter_upwards [h.ae_bounds, hab] with x hx habx
  simpa only [← habx] using hx

/-- Multiplying the coefficient field by `c > 0` multiplies both constants of inverse-coercive
ellipticity by `c`, so the ratio `Λ / λ` is unchanged. -/
theorem const_smul (h : IsUniformlyEllipticAE mu Ω a lam Lam) {c : ℝ} (hc : 0 < c) :
    IsUniformlyEllipticAE mu Ω (c • a) (c * lam) (c * Lam) := by
  refine ⟨mul_pos hc h.pos, mul_le_mul_of_nonneg_left h.le hc.le, ?_⟩
  filter_upwards [h.ae_bounds, h.ae_isUnit] with x hx hu
  let _ : Invertible c := invertibleOfNonzero hc.ne'
  refine ⟨fun ξ => ?_, fun ξ => ?_⟩
  · simp only [Pi.smul_apply, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_assoc]
    gcongr
    exact hx.1 ξ
  · simp only [Pi.smul_apply, Matrix.inv_smul (a x) c ((isUnit_iff_isUnit_det _).mp hu),
      invOf_eq_inv, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_inv, mul_assoc]
    gcongr
    exact hx.2 ξ

/-- The principal bilinear form is essentially bounded by the inverse-coercive upper
constant, as required for boundedness of the energy form. -/
theorem ae_opNorm_matrixBilinearForm_le (h : IsUniformlyEllipticAE mu Ω a lam Lam) :
    ∀ᵐ x ∂mu.restrict Ω, ‖matrixBilinearForm (a x)‖ ≤ Lam := by
  filter_upwards [h.ae_upper_bound] with x hx
  exact matrixBilinearForm_opNorm_le_of_upper_bound (a x) (h.pos.le.trans h.le) hx

/-- An inverse-coercive field has an almost-everywhere equal representative satisfying
the pointwise operator-bound predicate everywhere, with the same constants. Thus pointwise
energy and regularity estimates can be used without requiring an open full-measure subset.
The representative is filled in by `λ I` where the bounds fail. -/
theorem exists_ae_eq_uniformlyEllipticOn (h : IsUniformlyEllipticAE mu Ω a lam Lam) :
    ∃ b : X → Matrix ι ι ℝ, a =ᵐ[mu.restrict Ω] b ∧
      UniformlyEllipticOn univ b lam Lam := by
  classical
  let s := {x | (∀ ξ : EuclideanSpace ℝ ι,
    lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) ∧ ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖}
  refine ⟨fun x => if x ∈ s then a x else lam • 1, ?_, ?_⟩
  · filter_upwards [h.ae_bounds, h.ae_upper_bound] with x hx hu
    have hxs : x ∈ s := ⟨hx.1, hu⟩
    exact (ite_eq_left hxs).symm
  · rw [uniformlyEllipticOn_iff]
    refine ⟨h.pos, h.le, fun {x} _ => ?_⟩
    by_cases hx : x ∈ s
    · simp only [ite_eq_left hx]
      simpa only [Matrix.toQuadraticForm'_apply, s, mem_ofPred_eq] using hx
    · simp only [ite_eq_right hx]
      have hc := uniformlyEllipticOn_const_smul_one (n := ι) (X := X) univ
        h.pos le_rfl h.le
      exact ⟨hc.lower_bound (mem_univ x), hc.upper_bound (mem_univ x)⟩

end IsUniformlyEllipticAE

/-- Pointwise operator-bound ellipticity with constants `(λ, M)` implies almost-everywhere
inverse-coercive ellipticity with constants `(λ, M² / λ)`, not generally `(λ, M)`. -/
theorem UniformlyEllipticOn.isUniformlyEllipticAE (h : UniformlyEllipticOn Ω a lam M)
    (hΩ : NullMeasurableSet Ω mu) :
    IsUniformlyEllipticAE mu Ω a lam (M ^ 2 / lam) := by
  have hconst : lam ≤ M ^ 2 / lam :=
    (le_div_iff₀ h.pos).mpr (by nlinarith [mul_self_le_mul_self h.pos.le h.le])
  refine ⟨h.pos, hconst, ?_⟩
  filter_upwards [ae_restrict_mem₀ hΩ] with x hx
  have hl : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ) := by
    simpa only [Matrix.toQuadraticForm'_apply] using h.lower_bound hx
  exact ⟨hl, inverse_quadratic_lower_bound_of_bounds h.pos hl (h.upper_bound hx)⟩

end TauCeti.PDE
