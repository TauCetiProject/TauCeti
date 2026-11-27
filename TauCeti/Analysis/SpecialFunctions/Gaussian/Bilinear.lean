/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Analysis.Matrix.DotProduct
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Complex Gaussian integrals of real-bilinear forms

Let `E` be a finite-dimensional real normed space equipped with an additive Haar measure `μ`, and
let `B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ` be a real-bilinear form whose real part is strictly positive on
nonzero vectors (`∀ v ≠ 0, 0 < (B v v).re`). Then:

* the Gaussian integral `∫ v, Complex.exp (-B v v) ∂μ` does not vanish
  (`TauCeti.integral_cexp_neg_bilinear_ne_zero`);
* `v ↦ Complex.exp (-B v v)` is `μ`-integrable (`TauCeti.integrable_cexp_neg_bilinear`).

Nonvanishing is proved by choosing a basis of `E`, simultaneously diagonalizing the symmetrized real
and imaginary matrices of `B` via `Matrix.PosDef.exists_simultaneous_diagonal_real`, transporting
`μ` to Lebesgue measure on `Fin n → ℝ` up to a positive Haar factor, and evaluating the factored
complex Gaussian integral using `GaussianFourier.integral_cexp_neg_sum_mul_add`; continuity of
`v ↦ B v v` (`LinearMap.continuous_apply_self`) supplies the measurability needed for this change
of variables. Integrability follows from nonvanishing via
`MeasureTheory.Integrable.of_integral_ne_zero`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.6–§7.7.
* Levent Alpöge's prior formalization
  (`ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero`).
-/

public section

open Complex MeasureTheory Module
open scoped ENNReal Matrix NNReal

namespace TauCeti

private theorem continuous_cexp_neg_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    Continuous fun v : E ↦ Complex.exp (-B v v) :=
  B.continuous_apply_self.neg.cexp

private noncomputable def symmMatrix {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (β : LinearMap.BilinForm ℝ E) (b : Basis (Fin n) ℝ E) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (LinearMap.BilinForm.toMatrix b β + (LinearMap.BilinForm.toMatrix b β)ᵀ)

private theorem symmMatrix_isHermitian {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (β : LinearMap.BilinForm ℝ E) (b : Basis (Fin n) ℝ E) :
    (symmMatrix β b).IsHermitian :=
  (Matrix.isHermitian_add_transpose_self _).smul (IsSelfAdjoint.all _)

private theorem dotProduct_symmMatrix_mulVec {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (β : LinearMap.BilinForm ℝ E) (b : Basis (Fin n) ℝ E) (x : Fin n → ℝ) :
    dotProduct x (symmMatrix β b *ᵥ x) = β (b.equivFun.symm x) (b.equivFun.symm x) := by
  rw [symmMatrix, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
    LinearMap.BilinForm.dotProduct_toMatrix_mulVec, Matrix.dotProduct_transpose_mulVec,
    LinearMap.BilinForm.dotProduct_toMatrix_mulVec, smul_eq_mul]
  ring

private theorem bilinear_basis_equivFun_symm {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) (x : Fin n → ℝ) :
    B (b.equivFun.symm x) (b.equivFun.symm x) =
      ((dotProduct x (symmMatrix (B.compr₂ Complex.reCLM.toLinearMap) b *ᵥ x) : ℝ) : ℂ) +
        ((dotProduct x (symmMatrix (B.compr₂ Complex.imCLM.toLinearMap) b *ᵥ x) : ℝ) : ℂ) *
          Complex.I := by
  rw [dotProduct_symmMatrix_mulVec, dotProduct_symmMatrix_mulVec]
  exact (Complex.re_add_im _).symm

private theorem symmMatrix_re_posDef {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v : E, v ≠ 0 → 0 < (B v v).re)
    (b : Basis (Fin n) ℝ E) :
    (symmMatrix (B.compr₂ Complex.reCLM.toLinearMap) b).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (symmMatrix_isHermitian _ b) fun x hx ↦ ?_
  have hv : b.equivFun.symm x ≠ 0 := fun h ↦ hx (b.equivFun.symm.injective (by simp [h]))
  rw [star_trivial, dotProduct_symmMatrix_mulVec]
  exact hB (b.equivFun.symm x) hv

private theorem diagonalized_bilinear_apply {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E)
    {P : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hPA : Pᵀ * symmMatrix (B.compr₂ Complex.reCLM.toLinearMap) b * P = 1)
    (hPC : Pᵀ * symmMatrix (B.compr₂ Complex.imCLM.toLinearMap) b * P = Matrix.diagonal lam)
    (y : Fin n → ℝ) :
    B (b.equivFun.symm (P *ᵥ y)) (b.equivFun.symm (P *ᵥ y)) =
      ∑ i, (1 + (lam i : ℂ) * Complex.I) * (y i : ℂ) ^ 2 := by
  have hre_dot :
      dotProduct (P *ᵥ y) (symmMatrix (B.compr₂ Complex.reCLM.toLinearMap) b *ᵥ (P *ᵥ y)) =
        ∑ i, y i ^ 2 := by
    conv_lhs => lhs; rw [← star_trivial (P *ᵥ y)]
    rw [← Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec,
      Matrix.conjTranspose_eq_transpose_of_trivial, hPA, ← Matrix.diagonal_one,
      Matrix.star_dotProduct_diagonal_mulVec]
    simp
  have him_dot :
      dotProduct (P *ᵥ y) (symmMatrix (B.compr₂ Complex.imCLM.toLinearMap) b *ᵥ (P *ᵥ y)) =
        ∑ i, lam i * y i ^ 2 := by
    conv_lhs => lhs; rw [← star_trivial (P *ᵥ y)]
    rw [← Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec,
      Matrix.conjTranspose_eq_transpose_of_trivial, hPC, Matrix.star_dotProduct_diagonal_mulVec]
    simp
  rw [bilinear_basis_equivFun_symm B b (P *ᵥ y), hre_dot, him_dot]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- For every real-bilinear form `B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ` with `∀ v ≠ 0, 0 < (B v v).re` on a
finite-dimensional real normed space `E` with additive Haar measure `μ`, the complex Gaussian
integral `∫ v, Complex.exp (-B v v) ∂μ` is nonzero. -/
theorem integral_cexp_neg_bilinear_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v : E, v ≠ 0 → 0 < (B v v).re) :
    ∫ v : E, Complex.exp (-B v v) ∂μ ≠ 0 := by
  set b := Module.finBasis ℝ E
  obtain ⟨P, lam, hPA, hPC⟩ :=
    (symmMatrix_re_posDef B hB b).exists_simultaneous_diagonal_real
      (symmMatrix_isHermitian (B.compr₂ Complex.imCLM.toLinearMap) b)
  let e : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (((P : Matrix _ _ ℝ).toLinearEquiv' P.invertible).trans b.equivFun.symm).toContinuousLinearEquiv
  have he_apply (y : Fin (finrank ℝ E) → ℝ) :
      e y = b.equivFun.symm ((P : Matrix _ _ ℝ) *ᵥ y) := by
    rw [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply, ← Matrix.toLin'_apply]
    exact congrArg b.equivFun.symm (LinearMap.congr_fun (Matrix.toLinearEquiv'_apply _ _) y)
  let ν : Measure E := (volume : Measure (Fin (finrank ℝ E) → ℝ)).map e
  have hν : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  set c : ℝ≥0 := Measure.addHaarScalarFactor μ ν
  have hc_pos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have hint_eq : ∫ v : E, Complex.exp (-B v v) ∂μ =
      (c : ℝ) • ∫ y : Fin (finrank ℝ E) → ℝ, Complex.exp (-B (e y) (e y)) := by
    have hμ : μ = (c : ℝ≥0∞) • ν := Measure.isAddLeftInvariant_eq_smul μ ν
    have hev : ∫ y : E, Complex.exp (-B y y) ∂ν =
        ∫ y : Fin (finrank ℝ E) → ℝ, Complex.exp (-B (e y) (e y)) :=
      integral_map e.continuous.aemeasurable
        (continuous_cexp_neg_bilinear B).aestronglyMeasurable
    conv_lhs => rw [hμ, integral_smul_measure, ENNReal.coe_toReal, hev]
  have hgauss : ∫ y : Fin (finrank ℝ E) → ℝ, Complex.exp (-B (e y) (e y)) =
      ∏ i : Fin (finrank ℝ E), ((Real.pi : ℂ) / (1 + (lam i : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) := by
    have heq : ∀ y, B (e y) (e y) = ∑ i, (1 + (lam i : ℂ) * Complex.I) * (y i : ℂ) ^ 2 :=
      fun y ↦ by rw [he_apply y, diagonalized_bilinear_apply B b hPA hPC y]
    simp_rw [heq]
    convert GaussianFourier.integral_cexp_neg_sum_mul_add
      (b := fun i ↦ 1 + (lam i : ℂ) * Complex.I) (fun _ ↦ by simp) 0 using 1
    · simp
    · refine (Finset.prod_congr rfl fun i _ ↦ ?_).symm
      simp
  rw [hint_eq, hgauss, Complex.real_smul, mul_ne_zero_iff]
  refine ⟨Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hc_pos.ne'),
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_⟩
  have hbi : 1 + (lam i : ℂ) * Complex.I ≠ 0 := fun h ↦ by
    have hre := congrArg Complex.re h
    simp at hre
  exact mt (fun h ↦ (Complex.cpow_eq_zero_iff _ _).mp h |>.1)
    (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hbi)

/-- If a real-bilinear form `B` on a finite-dimensional real normed space has strictly positive
real part on the diagonal away from zero, then `v ↦ Complex.exp (-B v v)` is `μ`-integrable. -/
theorem integrable_cexp_neg_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v : E, v ≠ 0 → 0 < (B v v).re) :
    Integrable (fun v : E ↦ Complex.exp (-B v v)) μ :=
  Integrable.of_integral_ne_zero (integral_cexp_neg_bilinear_ne_zero μ B hB)

end TauCeti
