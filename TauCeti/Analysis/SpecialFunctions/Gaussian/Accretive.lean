/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Matrix.Accretive
import TauCeti.Analysis.SpecialFunctions.Gaussian.Reproducing
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Complex Gaussian integral for strictly accretive matrices

For a strictly accretive matrix `A`, we compute the complex Gaussian integral with linear
shift `a` against Lebesgue measure:
`∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) = π ^ Fintype.card ι * A.det⁻¹`
(`TauCeti.integral_cexp_neg_star_dotProduct_mulVec`). Congruence to diagonal form and the
Haar change of variables reduce it to `TauCeti.integral_cexp_neg_sum_mul_norm_sq_add`.

## Provenance

This result adapts `New.Fock.integral_gauss` from
`src/Lib/General/Analysis/GaussianIntegral.lean` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
The proof uses Lebesgue measure and Tau Ceti's diagonal Gaussian formula. The underlying
matrix results adapt `Matrix.IsAccretive`, `Matrix.PosDef.isAccretive`,
`Matrix.IsAccretive.det_ne_zero` and `New.Fock.exists_eq_conjTranspose_mul_diagonal_mul`.
The change of variables adapts `New.Fock.map_mulVec_addHaar_eq_smul` and
`New.lintegral_eq_norm_det_sq_mul_lintegral_mulVec` using Mathlib's Haar pushforward and
Tau Ceti's real determinant formula for complex-linear maps.
-/

public section

open MeasureTheory Matrix Complex Finset
open scoped ComplexConjugate

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Multivariate complex Gaussian integral for a strictly accretive matrix `A`:
`∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) = π ^ Fintype.card ι * A.det⁻¹`. -/
theorem integral_cexp_neg_star_dotProduct_mulVec [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsStrictlyAccretive) (a : ι → ℂ) :
    ∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) = (Real.pi : ℂ) ^ Fintype.card ι * A.det⁻¹ := by
  obtain ⟨p, d, rfl, hd⟩ := hA.exists_eq_conjTranspose_mul_diagonal_mul
  set P : Matrix ι ι ℂ := (p : Matrix ι ι ℂ)
  let g (y : ι → ℂ) : ℂ := exp (-∑ i, d i * (‖y i‖ : ℂ) ^ 2 + ∑ i, (0 : ι → ℂ) i * y i +
    ∑ i, (d i * (P *ᵥ a) i) * conj (y i))
  have h_form (x : ι → ℂ) :
      exp (-(star x ⬝ᵥ (Pᴴ * diagonal d * P) *ᵥ (x - a))) = g (P *ᵥ x) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star,
      mulVec_sub]
    simp only [g, dotProduct, mulVec_diagonal, Pi.star_apply, Pi.sub_apply, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, ← mul_conj']
    congr 1
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [RCLike.star_def]
    ring
  have h_prod : ∫ y : ι → ℂ, g y = ∏ i : ι, Real.pi / d i := by
    simp only [g]
    rw [integral_cexp_neg_sum_mul_norm_sq_add hd]
    simp
  have h_det : (Pᴴ * diagonal d * P).det = ‖P.det‖ ^ 2 * ∏ i : ι, d i := by
    simp [← mul_conj', mul_comm, mul_left_comm]
  calc
    _ = ∫ y : ι → ℂ, g y ∂volume.map (fun x : ι → ℂ ↦ P *ᵥ x) := by
      rw [integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop)), funext h_form]
    _ = ((‖P.det‖ ^ 2 : ℝ) : ℂ)⁻¹ * ∏ i : ι, (Real.pi : ℂ) / d i := by
      rw [map_mulVec_addHaar_eq_smul p.det_ne_zero]
      simp [P, h_prod, ENNReal.toReal_inv, Complex.real_smul]
    _ = (Real.pi : ℂ) ^ Fintype.card ι * (Pᴴ * diagonal d * P).det⁻¹ := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, h_det]
      push_cast
      ring

end TauCeti
