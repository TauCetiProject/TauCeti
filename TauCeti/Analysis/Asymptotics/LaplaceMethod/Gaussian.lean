/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Complex Gaussian integrals of real-bilinear forms

Let `E` be a finite-dimensional real normed space equipped with an additive Haar measure `μ`, and
let `B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ` be a real-bilinear form whose real part is strictly positive on
nonzero vectors (`∀ v ≠ 0, 0 < (B v v).re`). Then:

* `(B · ·).re` is bounded below by a positive multiple of `‖·‖ ^ 2`
  (`TauCeti.exists_pos_mul_norm_sq_le_re_bilinear`);
* `v ↦ Complex.exp (-B v v)` is `μ`-integrable (`TauCeti.integrable_cexp_neg_bilinear`);
* the Gaussian integral `∫ v, Complex.exp (-B v v) ∂μ` does not vanish
  (`TauCeti.integral_cexp_neg_bilinear_ne_zero`).

The integrability and the Laplace-method majorant both rely on
`TauCeti.integrable_one_add_mul_norm_sq_rpow`, the rescaled version of Mathlib's
`integrable_rpow_neg_one_add_norm_sq`. Nonvanishing is proved by choosing a basis of `E`,
simultaneously diagonalizing the symmetric real and imaginary matrices of `B` via the spectral
theorem, transporting `μ` to Lebesgue measure on `Fin n → ℝ` up to a positive Haar factor, and
evaluating the factored complex Gaussian integral using
`GaussianFourier.integral_cexp_neg_sum_mul_add`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.6–§7.7.
-/

public section

open Complex MeasureTheory Module
open scoped ENNReal Matrix NNReal

namespace TauCeti

/-- Rescaled Japanese-bracket integrability on a finite-dimensional real normed space: for
`0 < c` and `Module.finrank ℝ E < r`, `v ↦ (1 + c * ‖v‖ ^ 2) ^ (-r / 2)` is `μ`-integrable. -/
theorem integrable_one_add_mul_norm_sq_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {c r : ℝ} (hc : 0 < c) (hr : (Module.finrank ℝ E : ℝ) < r) :
    Integrable (fun v : E ↦ (1 + c * ‖v‖ ^ 2) ^ (-r / 2)) μ := by
  have hbase := integrable_rpow_neg_one_add_norm_sq (μ := μ) hr
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hcomp := hbase.comp_smul hsqrt
  refine hcomp.congr (.of_forall fun v ↦ ?_)
  simp [norm_smul, mul_pow, Real.sq_sqrt hc.le]

/-- A real-bilinear complex form whose real part is positive at every nonzero vector on a
finite-dimensional real normed space satisfies a uniform coercivity bound `m * ‖v‖ ^ 2 ≤ (B v v).re`
for some `m > 0`. -/
theorem exists_pos_mul_norm_sq_le_re_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v : E, v ≠ 0 → 0 < (B v v).re) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : E, m * ‖v‖ ^ 2 ≤ (B v v).re := by
  let bRe : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    { toFun v := Complex.reCLM.toLinearMap.comp (B v)
      map_add' u v := by ext w; simp
      map_smul' r v := by ext w; simp }
  obtain ⟨m, hm, hle⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ bRe.toContinuousBilinearMap) continuousOn_const
    fun _ _ v hv ↦ hB v hv
  exact ⟨m, hm, fun v ↦ by simpa [bRe] using hle () rfl v⟩

private theorem continuous_cexp_neg_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    Continuous fun v : E ↦ Complex.exp (-B v v) :=
  ((B.toContinuousBilinearMap.continuous₂).comp (continuous_id.prodMk continuous_id)).neg.cexp

/-- If a real-bilinear form `B` on a finite-dimensional real normed space has strictly positive
real part on nonzero vectors, then `v ↦ Complex.exp (-B v v)` is `μ`-integrable. -/
theorem integrable_cexp_neg_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v : E, v ≠ 0 → 0 < (B v v).re) :
    Integrable (fun v : E ↦ Complex.exp (-B v v)) μ := by
  obtain ⟨m, hm, hle⟩ := exists_pos_mul_norm_sq_le_re_bilinear B hB
  set p : ℝ := (Module.finrank ℝ E : ℝ) / 2 + 1
  have hp : 0 < p := by positivity
  have hmaj : Integrable (fun v : E ↦ (1 + (m / p) * ‖v‖ ^ 2) ^ (-(2 * p) / 2)) μ :=
    integrable_one_add_mul_norm_sq_rpow μ (div_pos hm hp) (by simp only [p]; linarith)
  refine hmaj.mono' (continuous_cexp_neg_bilinear B).aestronglyMeasurable (.of_forall fun v ↦ ?_)
  have hexp : 1 + (m / p) * ‖v‖ ^ 2 ≤ Real.exp ((m / p) * ‖v‖ ^ 2) := by
    linarith [Real.add_one_le_exp ((m / p) * ‖v‖ ^ 2)]
  have hrpow : (Real.exp ((m / p) * ‖v‖ ^ 2)) ^ (-p) ≤ (1 + (m / p) * ‖v‖ ^ 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hexp (neg_nonpos.mpr hp.le)
  have hscale : Real.exp (-m * ‖v‖ ^ 2) = (Real.exp ((m / p) * ‖v‖ ^ 2)) ^ (-p) := by
    rw [← Real.exp_mul]; congr 1; field_simp [hp.ne']
  rw [Complex.norm_exp, Complex.neg_re]
  calc Real.exp (-(B v v).re) ≤ Real.exp (-m * ‖v‖ ^ 2) :=
        Real.exp_le_exp.mpr (by linarith [hle v])
    _ = (Real.exp ((m / p) * ‖v‖ ^ 2)) ^ (-p) := hscale
    _ ≤ (1 + (m / p) * ‖v‖ ^ 2) ^ (-p) := hrpow
    _ = (1 + (m / p) * ‖v‖ ^ 2) ^ (-(2 * p) / 2) := by ring_nf

private noncomputable def symmRealMatrix {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ ((B (b i) (b j) + B (b j) (b i)) / 2).re

private noncomputable def symmImagMatrix {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ ((B (b i) (b j) + B (b j) (b i)) / 2).im

private theorem symmRealMatrix_isHermitian {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) :
    (symmRealMatrix B b).IsHermitian := by
  ext i j
  simp [symmRealMatrix, add_comm]

private theorem symmImagMatrix_isHermitian {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) :
    (symmImagMatrix B b).IsHermitian := by
  ext i j
  simp [symmImagMatrix, add_comm]

private theorem bilinear_equivFun_symm_eq_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) (x : Fin n → ℝ) :
    B (b.equivFun.symm x) (b.equivFun.symm x) =
      ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (b i) (b j) := by
  rw [b.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Complex.real_smul,
    Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

private theorem dotProduct_mulVec_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : dotProduct x (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem bilinear_basis_equivFun_symm {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E) (x : Fin n → ℝ) :
    B (b.equivFun.symm x) (b.equivFun.symm x) =
      ((dotProduct x (symmRealMatrix B b *ᵥ x) : ℝ) : ℂ) +
        ((dotProduct x (symmImagMatrix B b *ᵥ x) : ℝ) : ℂ) * Complex.I := by
  have hsum := bilinear_equivFun_symm_eq_sum B b x
  have hswap : ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (b j) (b i) =
      B (b.equivFun.symm x) (b.equivFun.symm x) := by
    rw [hsum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      simp [mul_comm (x j) (x i)]
  have hsymm : B (b.equivFun.symm x) (b.equivFun.symm x) =
      ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * ((B (b i) (b j) + B (b j) (b i)) / 2) := by
    calc B (b.equivFun.symm x) (b.equivFun.symm x)
        = (B (b.equivFun.symm x) (b.equivFun.symm x) +
            B (b.equivFun.symm x) (b.equivFun.symm x)) / 2 := by ring
      _ = ((∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (b i) (b j)) +
            (∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (b j) (b i))) / 2 :=
          congrArg (· / 2) (congrArg₂ (· + ·) hsum hswap.symm)
      _ = ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * ((B (b i) (b j) + B (b j) (b i)) / 2) := by
          simp_rw [← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  apply Complex.ext
  · rw [hsymm]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.re_sum,
      dotProduct_mulVec_eq_sum, symmRealMatrix, Matrix.of_apply, Complex.mul_im,
      Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  · rw [hsymm]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.im_sum,
      dotProduct_mulVec_eq_sum, symmImagMatrix, Matrix.of_apply, Complex.mul_re,
      Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

private theorem symmRealMatrix_posDef {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v : E, v ≠ 0 → 0 < (B v v).re)
    (b : Basis (Fin n) ℝ E) : (symmRealMatrix B b).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (symmRealMatrix_isHermitian B b) fun x hx ↦ ?_
  have hv : b.equivFun.symm x ≠ 0 := fun h ↦ hx (b.equivFun.symm.injective (by simp [h]))
  have hre : (B (b.equivFun.symm x) (b.equivFun.symm x)).re =
      dotProduct x (symmRealMatrix B b *ᵥ x) := by
    rw [bilinear_basis_equivFun_symm B b x]
    simp
  simpa [star_trivial, ← hre] using hB (b.equivFun.symm x) hv

private theorem exists_congruence_one_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ P₁ Q₁ : Matrix (Fin n) (Fin n) ℝ,
      P₁ * Q₁ = 1 ∧ Q₁ * P₁ = 1 ∧ P₁ᵀ * A * P₁ = 1 := by
  set α := hA.1.eigenvalues
  have hα : ∀ i, 0 < α i := hA.eigenvalues_pos
  set U₁ : Matrix (Fin n) (Fin n) ℝ := ↑hA.1.eigenvectorUnitary
  have hU₁L : U₁ᵀ * U₁ = 1 := by
    simpa [U₁, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hU₁R : U₁ * U₁ᵀ = 1 := by
    simpa [U₁, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  have hA₁ : U₁ᵀ * A * U₁ = Matrix.diagonal α := by
    simpa [U₁, α, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      hA.1.conjStarAlgAut_star_eigenvectorUnitary
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i ↦ (Real.sqrt (α i))⁻¹
  set Di : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i ↦ Real.sqrt (α i)
  have hDDi : D * Di = 1 := by
    ext i j
    simp only [D, Di, Matrix.diagonal_mul_diagonal, Matrix.one_apply]
    split_ifs with h
    · subst h; simp [(Real.sqrt_pos.mpr (hα _)).ne']
    · simp [h]
  have hDiD : Di * D = 1 := by
    ext i j
    simp only [D, Di, Matrix.diagonal_mul_diagonal, Matrix.one_apply]
    split_ifs with h
    · subst h; simp [(Real.sqrt_pos.mpr (hα _)).ne']
    · simp [h]
  have hDT : Dᵀ = D := Matrix.diagonal_transpose _
  refine ⟨U₁ * D, Di * U₁ᵀ, ?_, ?_, ?_⟩
  · calc (U₁ * D) * (Di * U₁ᵀ) = U₁ * (D * Di) * U₁ᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDDi, Matrix.mul_one, hU₁R]
  · calc (Di * U₁ᵀ) * (U₁ * D) = Di * ((U₁ᵀ * U₁) * D) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU₁L, Matrix.one_mul, hDiD]
  · calc (U₁ * D)ᵀ * A * (U₁ * D)
        = D * (U₁ᵀ * A * U₁) * D := by simp only [Matrix.transpose_mul, hDT, Matrix.mul_assoc]
      _ = D * Matrix.diagonal α * D := by rw [hA₁]
      _ = 1 := by
          ext i j
          simp only [D, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
          split_ifs with hij
          · subst hij; field_simp; rw [Real.sq_sqrt (hα _).le, div_self (hα _).ne']
          · rfl

private theorem exists_simultaneous_diagonal_real {n : ℕ} {A C : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hC : C.IsHermitian) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ),
      P * Q = 1 ∧ Q * P = 1 ∧ Pᵀ * A * P = 1 ∧ Pᵀ * C * P = Matrix.diagonal lam := by
  obtain ⟨P₁, Q₁, hP₁Q₁, hQ₁P₁, hP₁A⟩ := exists_congruence_one_of_posDef hA
  set M := P₁ᵀ * C * P₁
  have hM : M.IsHermitian := by
    ext i j
    have hCT : Cᵀ = C := hC
    calc Mᵀ i j = (P₁ᵀ * Cᵀ * P₁) i j := by
          simp only [M, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = M i j := by rw [hCT]
  set U₂ : Matrix (Fin n) (Fin n) ℝ := ↑hM.eigenvectorUnitary
  have hU₂L : U₂ᵀ * U₂ = 1 := by
    simpa [U₂, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hU₂R : U₂ * U₂ᵀ = 1 := by
    simpa [U₂, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hM₂ : U₂ᵀ * M * U₂ = Matrix.diagonal hM.eigenvalues := by
    simpa [U₂, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      hM.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨P₁ * U₂, U₂ᵀ * Q₁, hM.eigenvalues, ?_, ?_, ?_, ?_⟩
  · calc (P₁ * U₂) * (U₂ᵀ * Q₁) = P₁ * ((U₂ * U₂ᵀ) * Q₁) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU₂R, Matrix.one_mul, hP₁Q₁]
  · calc (U₂ᵀ * Q₁) * (P₁ * U₂) = U₂ᵀ * ((Q₁ * P₁) * U₂) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ₁P₁, Matrix.one_mul, hU₂L]
  · calc (P₁ * U₂)ᵀ * A * (P₁ * U₂)
        = U₂ᵀ * (P₁ᵀ * A * P₁) * U₂ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hP₁A, Matrix.mul_one, hU₂L]
  · calc (P₁ * U₂)ᵀ * C * (P₁ * U₂) = U₂ᵀ * M * U₂ := by
          simp only [M, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.diagonal hM.eigenvalues := hM₂

private theorem dotProduct_mulVec_conj {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    dotProduct (P *ᵥ y) (A *ᵥ (P *ᵥ y)) = dotProduct y ((Pᵀ * A * P) *ᵥ y) := by
  calc dotProduct (P *ᵥ y) (A *ᵥ (P *ᵥ y))
      = ((P *ᵥ y) ᵥ* A) ⬝ᵥ (P *ᵥ y) := Matrix.dotProduct_mulVec _ _ _
    _ = ((y ᵥ* Pᵀ) ᵥ* A) ⬝ᵥ (P *ᵥ y) := by rw [Matrix.vecMul_transpose]
    _ = (y ᵥ* (Pᵀ * A)) ⬝ᵥ (P *ᵥ y) := by rw [Matrix.vecMul_vecMul]
    _ = y ⬝ᵥ ((Pᵀ * A) *ᵥ (P *ᵥ y)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = y ⬝ᵥ ((Pᵀ * A * P) *ᵥ y) := by rw [Matrix.mulVec_mulVec]

private theorem diagonalized_bilinear_apply {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (b : Basis (Fin n) ℝ E)
    {P : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hPA : Pᵀ * symmRealMatrix B b * P = 1)
    (hPC : Pᵀ * symmImagMatrix B b * P = Matrix.diagonal lam) (y : Fin n → ℝ) :
    B (b.equivFun.symm (P *ᵥ y)) (b.equivFun.symm (P *ᵥ y)) =
      ∑ i, (1 + (lam i : ℂ) * Complex.I) * (y i : ℂ) ^ 2 := by
  have hre_dot : dotProduct (P *ᵥ y) (symmRealMatrix B b *ᵥ (P *ᵥ y)) = ∑ i, y i ^ 2 := by
    rw [dotProduct_mulVec_conj, hPA, Matrix.one_mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ (sq (y i)).symm
  have him_dot : dotProduct (P *ᵥ y) (symmImagMatrix B b *ᵥ (P *ᵥ y)) =
      ∑ i, lam i * y i ^ 2 := by
    rw [dotProduct_mulVec_conj, hPC, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [Matrix.mulVec_diagonal]; ring
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
  obtain ⟨P, Q, lam, hPQ, hQP, hPA, hPC⟩ := exists_simultaneous_diagonal_real
    (symmRealMatrix_posDef B hB b) (symmImagMatrix_isHermitian B b)
  let equivP : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    LinearEquiv.ofLinearMap P.mulVecLin Q.mulVecLin
      (LinearMap.ext fun y ↦ by simp [Matrix.mulVec_mulVec, hPQ])
      (LinearMap.ext fun y ↦ by simp [Matrix.mulVec_mulVec, hQP])
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (equivP.trans b.equivFun.symm).toContinuousLinearEquiv
  let ν : Measure E := (volume : Measure (Fin (Module.finrank ℝ E) → ℝ)).map e
  have hν : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  set c : ℝ≥0 := Measure.addHaarScalarFactor μ ν
  have hc_pos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have hint_eq : ∫ v : E, Complex.exp (-B v v) ∂μ =
      (c : ℝ) • ∫ y : Fin (Module.finrank ℝ E) → ℝ, Complex.exp (-B (e y) (e y)) := by
    have hμ : μ = (c : ℝ≥0∞) • ν := Measure.isAddLeftInvariant_eq_smul μ ν
    have hev : ∫ y : E, Complex.exp (-B y y) ∂ν =
        ∫ y : Fin (Module.finrank ℝ E) → ℝ, Complex.exp (-B (e y) (e y)) := by
      dsimp only [ν]
      exact integral_map e.continuous.aemeasurable
        (continuous_cexp_neg_bilinear B).aestronglyMeasurable
    conv_lhs => rw [hμ, integral_smul_measure, ENNReal.coe_toReal, hev]
  have hgauss : ∫ y : Fin (Module.finrank ℝ E) → ℝ, Complex.exp (-B (e y) (e y)) =
      ∏ i : Fin (Module.finrank ℝ E),
        ((Real.pi : ℂ) / (1 + (lam i : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) := by
    have heq : ∀ y, B (e y) (e y) = ∑ i, (1 + (lam i : ℂ) * Complex.I) * (y i : ℂ) ^ 2 :=
      fun y ↦ diagonalized_bilinear_apply B b hPA hPC y
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

end TauCeti
