/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Inverse-coercive ellipticity

For nonsymmetric matrices, a lower bound on the quadratic form of the inverse is different
from an upper operator bound. This file defines almost-everywhere inverse-coercive
ellipticity and converts it to the operator-bound convention used by the energy estimates.
The forward conversion keeps the upper constant; the reverse conversion changes an operator
bound `M` to `M² / λ`. Neither conversion requires symmetry or coefficient continuity.

Neither conversion is an identity of constants. In the plane, with `J = !![0, -1; 1, 0]`, the
constant coefficient `1 + k J` has least operator constant `√(1 + k²)`
(`TauCeti.PDE.isLeast_uniformlyEllipticOn_one_add_smul_skew`) and least inverse-coercive constant
`1 + k²` (`TauCeti.PDE.isLeast_isUniformlyEllipticAE_one_add_smul_skew`), both with lower
constant `1`: the conversion from operator to inverse-coercive constants is exact on it, and the
other one is not when `k ≠ 0`.

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

/-! ### The planar coefficient `1 + k J`

With `J = !![0, -1; 1, 0]`, the constant coefficient `1 + k J = !![1, -k; k, 1]` has the quadratic
form `ξ ↦ ‖ξ‖²`, operator norm `√(1 + k²)` and inverse `(1 + k²)⁻¹ (1 - k J)`, whose quadratic form
is `ξ ↦ ‖ξ‖² / (1 + k²)`. So its least operator-bound constant with lower constant `1` is
`√(1 + k²)`, and its least inverse-coercive constant is `1 + k²`. The conversion
`TauCeti.PDE.UniformlyEllipticOn.isUniformlyEllipticAE` from operator constants `(1, M)` to
inverse-coercive constants `(1, M²)` is exact here, while the conversion
`TauCeti.PDE.IsUniformlyEllipticAE.ae_upper_bound` in the other direction keeps `1 + k²`, which
exceeds `√(1 + k²)` when `k ≠ 0`. Neither conversion is an identity of constants. -/

section Skew

variable {X : Type*} {s : Set X}

private theorem dotProduct_mulVec_one_add_smul_skew (k : ℝ) (η ξ : EuclideanSpace ℝ (Fin 2)) :
    η ⬝ᵥ ((1 + k • !![(0 : ℝ), -1; 1, 0]) *ᵥ ξ) =
      η 0 * ξ 0 + η 1 * ξ 1 + k * (η 1 * ξ 0 - η 0 * ξ 1) := by
  simp [dotProduct, mulVec, Fin.sum_univ_two, Matrix.one_apply]
  ring

/-- The coefficient `1 + k J` has the quadratic form `ξ ↦ ‖ξ‖²`. -/
theorem dotProduct_mulVec_one_add_smul_skew_self (k : ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ξ ⬝ᵥ ((1 + k • !![(0 : ℝ), -1; 1, 0]) *ᵥ ξ) = ‖ξ‖ ^ 2 := by
  rw [dotProduct_mulVec_one_add_smul_skew, EuclideanSpace.norm_sq_fin_two]
  ring

/-- The coefficient `1 + k J` satisfies the mixed bound `|η · (1 + k J) ξ| ≤ √(1 + k²) ‖η‖ ‖ξ‖`. -/
theorem abs_dotProduct_mulVec_one_add_smul_skew_le (k : ℝ) (η ξ : EuclideanSpace ℝ (Fin 2)) :
    |η ⬝ᵥ ((1 + k • !![(0 : ℝ), -1; 1, 0]) *ᵥ ξ)| ≤ √(1 + k ^ 2) * ‖η‖ * ‖ξ‖ := by
  rw [dotProduct_mulVec_one_add_smul_skew, mul_assoc, ← Real.sqrt_sq (norm_nonneg η),
    ← Real.sqrt_sq (norm_nonneg ξ), ← Real.sqrt_mul (sq_nonneg _),
    ← Real.sqrt_mul (by positivity), EuclideanSpace.norm_sq_fin_two,
    EuclideanSpace.norm_sq_fin_two]
  refine Real.abs_le_sqrt ?_
  nlinarith [sq_nonneg (k * (η 0 * ξ 0 + η 1 * ξ 1) - (η 1 * ξ 0 - η 0 * ξ 1)),
    sq_nonneg (η 0 * ξ 1 - η 1 * ξ 0), sq_nonneg (η 0 * ξ 0 + η 1 * ξ 1)]

/-- The inverse of `1 + k J` is `(1 + k²)⁻¹ (1 - k J)`. -/
theorem inv_one_add_smul_skew (k : ℝ) :
    (1 + k • !![(0 : ℝ), -1; 1, 0])⁻¹ = (1 + k ^ 2)⁻¹ • (1 - k • !![(0 : ℝ), -1; 1, 0]) := by
  refine Matrix.inv_eq_right_inv ?_
  have hk : (1 + k ^ 2) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- The inverse of the coefficient `1 + k J` has the quadratic form `ξ ↦ ‖ξ‖² / (1 + k²)`. -/
theorem dotProduct_mulVec_inv_one_add_smul_skew_self (k : ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ξ ⬝ᵥ ((1 + k • !![(0 : ℝ), -1; 1, 0])⁻¹ *ᵥ ξ) = (1 + k ^ 2)⁻¹ * ‖ξ‖ ^ 2 := by
  rw [inv_one_add_smul_skew, smul_mulVec, dotProduct_smul, sub_eq_add_neg, ← neg_smul,
    dotProduct_mulVec_one_add_smul_skew_self, smul_eq_mul]

/-- **The operator constant of `1 + k J`.** On a nonempty set, the least upper constant `M` for
which the constant coefficient `1 + k J` is uniformly elliptic with constants `(1, M)` in the
operator-bound convention is `√(1 + k²)`, the operator norm of `1 + k J`. -/
theorem isLeast_uniformlyEllipticOn_one_add_smul_skew (hs : s.Nonempty) (k : ℝ) :
    IsLeast {M | UniformlyEllipticOn s (fun _ ↦ 1 + k • !![(0 : ℝ), -1; 1, 0]) 1 M}
      √(1 + k ^ 2) := by
  refine ⟨uniformlyEllipticOn_iff.2 ⟨one_pos, Real.one_le_sqrt.2 (by nlinarith [sq_nonneg k]),
    fun x _ ↦ ⟨fun ξ ↦ ?_, abs_dotProduct_mulVec_one_add_smul_skew_le k⟩⟩, fun M hM ↦ ?_⟩
  · rw [Matrix.toQuadraticForm'_apply, dotProduct_mulVec_one_add_smul_skew_self, one_mul]
  -- Test the mixed bound with `ξ = e₀` and `η = (1 + k J) e₀ = (1, k)`.
  obtain ⟨x, hx⟩ := hs
  have h := hM.upper_bound hx (WithLp.toLp 2 ![1, k]) (EuclideanSpace.single 0 1)
  have hη : ‖(WithLp.toLp 2 ![1, k] : EuclideanSpace ℝ (Fin 2))‖ = √(1 + k ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_fin_two]
    simp
  have hsq : √(1 + k ^ 2) * √(1 + k ^ 2) = 1 + k ^ 2 := Real.mul_self_sqrt (by positivity)
  rw [dotProduct_mulVec_one_add_smul_skew, hη] at h
  replace h : |1 + k * k| ≤ M * √(1 + k ^ 2) := by simpa using h
  rw [abs_of_nonneg (by nlinarith [mul_self_nonneg k])] at h
  refine le_of_mul_le_mul_right ?_ (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + k ^ 2))
  nlinarith

/-- **The inverse-coercive constant of `1 + k J`.** On a set of positive measure, the least upper
constant `Λ` for which the constant coefficient `1 + k J` is inverse-coercive with constants
`(1, Λ)` is `1 + k²`. -/
theorem isLeast_isUniformlyEllipticAE_one_add_smul_skew [MeasurableSpace X] {mu : Measure X}
    (hs : mu s ≠ 0) (k : ℝ) :
    IsLeast {Λ | IsUniformlyEllipticAE mu s (fun _ ↦ 1 + k • !![(0 : ℝ), -1; 1, 0]) 1 Λ}
      (1 + k ^ 2) := by
  refine ⟨isUniformlyEllipticAE_iff.2 ⟨one_pos, by nlinarith [sq_nonneg k], .of_forall fun _ ↦
    ⟨fun ξ ↦ by rw [dotProduct_mulVec_one_add_smul_skew_self, one_mul],
      fun ξ ↦ (dotProduct_mulVec_inv_one_add_smul_skew_self k ξ).ge⟩⟩, fun Λ hΛ ↦ ?_⟩
  -- Test the inverse quadratic bound with `ξ = e₀` at some point of `s`.
  have : NeZero (mu.restrict s) := ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
  obtain ⟨_, hx⟩ := hΛ.ae_bounds.exists
  have h := hx.2 (EuclideanSpace.single 0 1)
  rw [dotProduct_mulVec_inv_one_add_smul_skew_self] at h
  simp only [PiLp.norm_single, norm_one, one_pow, mul_one] at h
  exact (inv_le_inv₀ (one_pos.trans_le hΛ.le) (by positivity)).1 h

end Skew

end TauCeti.PDE
