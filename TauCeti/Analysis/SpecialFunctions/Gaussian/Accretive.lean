/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Complex Gaussian integral for accretive matrices

A complex square matrix `A : Matrix ι ι ℂ` is *strictly accretive* (`Matrix.IsAccretive A`) if its
Hermitian part `A + Aᴴ` is positive definite. Every strictly accretive matrix is invertible and
congruent to a diagonal matrix whose entries have positive real part
(`Matrix.IsAccretive.exists_eq_conjTranspose_mul_diagonal_mul`).

Using this congruence together with the complex change-of-variables formula for additive Haar
measures (`TauCeti.map_mulVec_addHaar_eq_smul`), we evaluate the multivariate complex Gaussian
integral with linear shift:
`∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) = π ^ Fintype.card ι * A.det⁻¹`
(`TauCeti.integral_cexp_neg_star_dotProduct_mulVec`).

## Main results

* `Matrix.IsAccretive`: predicate `(A + Aᴴ).PosDef`.
* `Matrix.PosDef.isAccretive`: every positive definite complex matrix is accretive.
* `Matrix.IsAccretive.det_ne_zero`: every accretive matrix has nonzero determinant.
* `Matrix.IsAccretive.exists_eq_conjTranspose_mul_diagonal_mul`: congruence of an accretive matrix
  to a diagonal matrix with entries in the open right half-plane.
* `TauCeti.map_mulVec_addHaar_eq_smul`: pushforward of an additive Haar measure on `ι → ℂ` by an
  invertible complex matrix `u` scales the measure by `‖u.det‖⁻²`.
* `TauCeti.lintegral_eq_norm_det_sq_mul_lintegral_mulVec`: Lebesgue change of variables on `ι → ℂ`.
* `TauCeti.integral_cexp_neg_star_mul`: one-dimensional complex Gaussian integral
  `∫ z : ℂ, exp (-(star z * (d * (z - a)))) = π / d` for `0 < d.re`.
* `TauCeti.integral_cexp_neg_star_dotProduct_mulVec`: multivariate complex Gaussian integral for an
  accretive matrix `A` with linear shift `a`.
-/

public section

open MeasureTheory Matrix Complex Finset CStarAlgebra
open scoped ComplexOrder MatrixOrder NNReal

namespace Matrix

variable {ι : Type*} {A : Matrix ι ι ℂ}

/-- A complex square matrix `A` is strictly accretive if `A + Aᴴ` is positive definite. -/
def IsAccretive (A : Matrix ι ι ℂ) : Prop := (A + Aᴴ).PosDef

/-- Every positive definite complex matrix is strictly accretive. -/
theorem PosDef.isAccretive (hA : A.PosDef) : A.IsAccretive := hA.add hA.conjTranspose

/-- Every strictly accretive matrix has nonzero determinant. -/
theorem IsAccretive.det_ne_zero [Fintype ι] [DecidableEq ι] (hA : A.IsAccretive) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv_ne, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet
  have hpos : 0 < star v ⬝ᵥ (A + Aᴴ) *ᵥ v := hA.dotProduct_mulVec_pos hv_ne
  have hzero : star v ⬝ᵥ (A + Aᴴ) *ᵥ v = 0 := by
    rw [add_mulVec, dotProduct_add, hv, dotProduct_zero, zero_add, mulVec_conjTranspose,
      dotProduct_star, ← dotProduct_mulVec, star_star, hv, dotProduct_zero, star_zero]
  exact hpos.ne' hzero

/-- A strictly accretive matrix `A` is congruent to a diagonal matrix whose entries have strictly
positive real part. -/
theorem IsAccretive.exists_eq_conjTranspose_mul_diagonal_mul [Fintype ι] [DecidableEq ι]
    (hA : A.IsAccretive) :
    ∃ (p : GL ι ℂ) (d : ι → ℂ),
      A = (p : Matrix ι ι ℂ)ᴴ * diagonal d * (p : Matrix ι ι ℂ) ∧ ∀ i : ι, 0 < (d i).re := by
  obtain ⟨b, hb_unit, hb : A + Aᴴ = star b * b⟩ :=
    isStrictlyPositive_iff_eq_star_mul_self.mp hA.isStrictlyPositive
  lift b to GL ι ℂ using hb_unit with B
  set H : Matrix ι ι ℂ := star (B : Matrix ι ι ℂ)⁻¹ * imaginaryPart A * (B : Matrix ι ι ℂ)⁻¹
  have hH : H.IsHermitian := ((imaginaryPart A).prop.conjugate' B⁻¹).isHermitian
  set U : Matrix ι ι ℂ := ↑hH.eigenvectorUnitary
  have h_spectral : U * diagonal (ofReal ∘ hH.eigenvalues) * star U = H := by
    simpa using hH.spectral_theorem.symm
  let d : ι → ℂ := fun i ↦ I * hH.eigenvalues i + 2⁻¹
  have hd : diagonal d = I • diagonal (ofReal ∘ hH.eigenvalues) + (2⁻¹ : ℂ) • 1 := by
    simp [smul_one_eq_diagonal, ← diagonal_smul, d]
  refine ⟨Unitary.toUnits hH.eigenvectorUnitary⁻¹ * B, d, ?_, by simp [d]⟩
  calc
    A = I • (imaginaryPart A : Matrix ι ι ℂ) + (2⁻¹ : ℂ) • (A + Aᴴ) := by
      rw [imaginaryPart_apply_coe, smul_smul, mul_neg, I_mul_I, neg_neg, star_eq_conjTranspose]
      module
    _ = star (B : Matrix ι ι ℂ) * (I • H + (2⁻¹ : ℂ) • 1) * B := by
      simp [mul_add, add_mul, hb, H, ← mul_assoc, ← star_mul]
    _ = star (B : Matrix ι ι ℂ) * (U * diagonal d * star U) * B := by
      simp [hd, mul_add, add_mul, h_spectral, U]
    _ = _ := by simp [U, star_eq_conjTranspose, mul_assoc]

end Matrix

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The pushforward of an additive Haar measure `μ` on `ι → ℂ` under an invertible complex matrix
`u` is `‖u.det‖⁻² • μ`. -/
theorem map_mulVec_addHaar_eq_smul [DecidableEq ι] {μ : Measure (ι → ℂ)} [μ.IsAddHaarMeasure]
    {u : Matrix ι ι ℂ} (hu : u.det ≠ 0) :
    μ.map (fun x : ι → ℂ ↦ u *ᵥ x) = (ENNReal.ofReal (‖u.det‖ ^ 2))⁻¹ • μ := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := u.toLin'.restrictScalars ℝ
  have h_det : LinearMap.det f = ‖u.det‖ ^ 2 := by
    simp [f, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, ← Complex.sq_norm]
  change μ.map f = _
  simp [μ.map_linearMap_addHaar_eq_smul_addHaar, h_det, hu]

/-- Change of variables on `ι → ℂ` for any additive Haar measure `μ`: for an invertible complex
matrix `u` and any `g : (ι → ℂ) → ENNReal`,
`∫⁻ y, g y ∂μ = ‖u.det‖² * ∫⁻ y, g (u *ᵥ y) ∂μ`. -/
theorem lintegral_eq_norm_det_sq_mul_lintegral_mulVec [DecidableEq ι] {μ : Measure (ι → ℂ)}
    [μ.IsAddHaarMeasure] {u : Matrix ι ι ℂ} (hu : u.det ≠ 0) (g : (ι → ℂ) → ENNReal) :
    ∫⁻ y : ι → ℂ, g y ∂μ = ENNReal.ofReal (‖u.det‖ ^ 2) * ∫⁻ y : ι → ℂ, g (u *ᵥ y) ∂μ := by
  have h_emb : MeasurableEmbedding (fun y : ι → ℂ ↦ u *ᵥ y) :=
    Continuous.measurableEmbedding (by fun_prop) (mulVec_injective_of_det_ne_zero hu)
  rw [← h_emb.lintegral_map, map_mulVec_addHaar_eq_smul hu]
  simp [ENNReal.mul_inv_cancel_left, hu]

/-- One-dimensional complex Gaussian integral: if `0 < d.re`, then
`∫ z : ℂ, exp (-(star z * (d * (z - a)))) = π / d`. -/
theorem integral_cexp_neg_star_mul {d : ℂ} (hd : 0 < d.re) (a : ℂ) :
    ∫ z : ℂ, exp (-(star z * (d * (z - a)))) = Real.pi / d := by
  let c : Fin 2 → ℂ := (d * a) • ![1, -I]
  let g (v : Fin 2 → ℝ) : ℂ := exp (-d * ∑ i : Fin 2, (v i : ℂ) ^ 2 + ∑ i : Fin 2, c i * v i)
  have h_exponent (z : ℂ) : -(star z * (d * (z - a))) =
      -d * ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) + (d * a * z.re - I * (d * a) * z.im) := by
    rw [show star z = z.re - z.im * I by simp [Complex.ext_iff]]
    linear_combination (z.re - z.im * I) * d * re_add_im z + d * z.im ^ 2 * I_sq
  have h_coeff : ∑ i : Fin 2, c i ^ 2 = 0 := by simp [c, mul_pow]
  calc
    _ = ∫ z : ℂ, g (measurableEquivPi z) := by
      simp only [h_exponent]
      simp [g, c, sub_eq_add_neg, mul_comm]
    _ = ∫ v : Fin 2 → ℝ, g v := volume_preserving_equiv_pi.integral_comp' g
    _ = Real.pi / d := by
      simpa [h_coeff, g] using GaussianFourier.integral_cexp_neg_mul_sum_add hd c

/-- Multivariate complex Gaussian integral for a strictly accretive matrix `A`:
`∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) = π ^ Fintype.card ι * A.det⁻¹`. -/
theorem integral_cexp_neg_star_dotProduct_mulVec [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsAccretive) (a : ι → ℂ) :
    ∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) = (Real.pi : ℂ) ^ Fintype.card ι * A.det⁻¹ := by
  obtain ⟨p, d, rfl, hd⟩ := hA.exists_eq_conjTranspose_mul_diagonal_mul
  set P : Matrix ι ι ℂ := (p : Matrix ι ι ℂ)
  let g (i : ι) (z : ℂ) : ℂ := exp (-(star z * (d i * (z - (P *ᵥ a) i))))
  have h_form (x : ι → ℂ) :
      exp (-(star x ⬝ᵥ (Pᴴ * diagonal d * P) *ᵥ (x - a))) = ∏ i : ι, g i ((P *ᵥ x) i) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star,
      mulVec_sub]
    simp [g, dotProduct, mulVec_diagonal, ← exp_sum]
  have h_prod : ∫ y : ι → ℂ, ∏ i : ι, g i (y i) = ∏ i : ι, Real.pi / d i := by
    rw [integral_fintype_prod_volume_eq_prod g]
    exact Finset.prod_congr rfl fun i _ ↦ integral_cexp_neg_star_mul (hd i) _
  have h_det : (Pᴴ * diagonal d * P).det = ‖P.det‖ ^ 2 * ∏ i : ι, d i := by
    simp [← mul_conj', mul_comm, mul_left_comm]
  calc
    _ = ∫ y : ι → ℂ, ∏ i : ι, g i (y i) ∂volume.map (fun x : ι → ℂ ↦ P *ᵥ x) := by
      rw [integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop)), funext h_form]
    _ = ((‖P.det‖ ^ 2 : ℝ) : ℂ)⁻¹ * ∏ i : ι, (Real.pi : ℂ) / d i := by
      rw [map_mulVec_addHaar_eq_smul p.det_ne_zero]
      simp [P, h_prod, ENNReal.toReal_inv, Complex.real_smul]
    _ = (Real.pi : ℂ) ^ Fintype.card ι * (Pᴴ * diagonal d * P).det⁻¹ := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, h_det]
      push_cast
      ring

end TauCeti
