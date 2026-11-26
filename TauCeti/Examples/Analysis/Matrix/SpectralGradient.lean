/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralGradient
public import TauCeti.Examples.Analysis.Matrix.SpectralFunction
import Mathlib.Analysis.Calculus.Deriv.Abs
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic

/-!
# The gradient of spectral functions on `2 × 2` matrices

The gradient of the spectral function `A ↦ f(λ(A))` at a Hermitian matrix `A` is
`∇F_f(A) = U diag(∂ᵢ f(λ(A))) U*` for an eigenbasis `U` of `A`
(`Matrix.IsHermitian.spectralGradient`). These examples compute it for the spectral functions
`det`, `tr(T²)` and `det^{1/2}` on explicit `2 × 2` matrices, and give the
non-differentiable control `λ₁`. The gradient of `tr` is the identity at every Hermitian matrix
(`Matrix.IsHermitian.spectralGradient_sum`).

* The gradient of `det` at `[[2, 1], [1, 2]]`, with eigenvalues `3, 1`, is `[[2, -1], [-1, 2]]`.
  The diagonal matrix `diag(∂ᵢ f(λ)) = diag(1, 3)`, which forgets the eigenbasis, is a different
  matrix.
* `max` is symmetric but not differentiable at `(1, 1)`, and
  `t ↦ λ₁(1 + t diag(1, 0)) = 1 + max(t, 0)` is not differentiable at `0`.
* The spectral function of `μ ↦ ∑ μₖ²` is `tr(T²)`, with gradient `2T`; at `[[0, 1], [1, 0]]` the
  eigenvalues are `1, -1`.
* For `f = σ₂^{1/2}` at `T = diag(1, 4)`, whose sorted eigenvalue vector is `(4, 1)`, the partial
  derivatives are `1/4` and `1`, so `∇F(T) = diag(1, 1/4)` in the standard basis,
  `det ∇F(T) = 1/4` and `tr(∇F(T) T) = 2 = F(T)` (Euler's identity in degree one).
* For `f = σ₂` at `T = diag(1, 4)`, `∇F(T) = det(T) T⁻¹ = diag(4, 1)` and
  `tr(∇F(T) T) = 8 = 2 F(T)`: the Euler identity carries the degree of homogeneity.
* The trace inequality `tr(AB) ≥ n (det A det B)^{1/n}` at `A = diag(1, 4)`: `5 ≥ 4` for `B = 1`,
  with equality `2 = 2` for `B = A⁻¹`.
-/

public section

open Matrix
open scoped ComplexOrder

namespace TauCeti.SpectralGradientExamples

open SpectralFunctionExamples

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The determinant at `[[2, 1], [1, 2]]` -/

/-- The sorted eigenvalues of `[[2, 1], [1, 2]]` are `3, 1`. -/
theorem eigenvalues₀_two_one (hT : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) 𝕜).IsHermitian) :
    hT.eigenvalues₀ = ![3, 1] := by
  refine hT.eigenvalues₀_eq_of_charpoly_eq_two (by norm_num) ?_
  norm_num [charpoly_fin_two, trace_fin_two_of, det_fin_two_of, map_ofNat]
  ring

/-- **The gradient of the determinant** at `[[2, 1], [1, 2]]` is `det(T) T⁻¹ = [[2, -1], [-1, 2]]`.
-/
theorem spectralGradient_prod_two_one
    (hT : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) 𝕜).IsHermitian) :
    hT.spectralGradient (fun μ ↦ ∏ k, μ k) = !![2, -1; -1, 2] := by
  have hdet : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) 𝕜).det = 3 := by
    rw [det_fin_two_of]
    norm_num
  refine hT.spectralGradient_prod_eq_of_mul_eq
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 three_ne_zero) ?_
  rw [hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- **Forgetting the eigenbasis gives the wrong matrix.** At `T = [[2, 1], [1, 2]]` the partial
derivatives of `f = σ₂` at `λ(T) = (3, 1)` are `1` and `3`; the diagonal matrix `diag(1, 3)` of
them differs from the gradient `[[2, -1], [-1, 2]]`. -/
theorem diagonal_fderiv_prod_two_one
    (hT : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) 𝕜).IsHermitian) :
    (diagonal fun k : Fin 2 ↦
      (fderiv ℝ (fun μ : Fin 2 → ℝ ↦ ∏ k, μ k) hT.eigenvalues₀ (Pi.single k 1) : 𝕜)) =
        diagonal ![1, 3] ∧
      diagonal ![(1 : 𝕜), 3] ≠ hT.spectralGradient (fun μ ↦ ∏ k, μ k) := by
  refine ⟨?_, ?_⟩
  · have h0 : fderiv ℝ (fun μ : Fin 2 → ℝ ↦ ∏ k, μ k) hT.eigenvalues₀ (Pi.single 0 1) = 1 := by
      rw [fderiv_prod_apply_single (ι := Fin 2) (y := hT.eigenvalues₀)]
      simp [eigenvalues₀_two_one, Fin.univ_succ]
    have h1 : fderiv ℝ (fun μ : Fin 2 → ℝ ↦ ∏ k, μ k) hT.eigenvalues₀ (Pi.single 1 1) = 3 := by
      rw [fderiv_prod_apply_single (ι := Fin 2) (y := hT.eigenvalues₀)]
      simp [eigenvalues₀_two_one, Fin.univ_succ, Finset.erase_insert_of_ne]
    congr 1
    funext k
    fin_cases k
    · exact (congrArg (fun x : ℝ ↦ (x : 𝕜)) h0).trans (by simp)
    · exact (congrArg (fun x : ℝ ↦ (x : 𝕜)) h1).trans (by simp [RCLike.ofReal_ofNat])
  · rw [spectralGradient_prod_two_one]
    intro h
    have h01 := congrFun₂ h 0 1
    simp at h01

/-! ### `λ₁` is not differentiable at a repeated eigenvalue -/

/-- `t ↦ 1 + max(t, 0)` is not differentiable at `0`. -/
theorem not_differentiableAt_one_add_max_zero :
    ¬ DifferentiableAt ℝ (fun t : ℝ ↦ 1 + max t 0) 0 := by
  intro h
  have habs : (fun t : ℝ ↦ 2 * (1 + max t 0) - 2 - t) = abs := by
    funext t
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right ht, abs_of_nonpos ht]
      ring
    · rw [max_eq_left ht, abs_of_nonneg ht]
      ring
  apply not_differentiableAt_abs_zero
  rw [← habs]
  exact (((differentiableAt_const _).mul h).sub (differentiableAt_const _)).sub differentiableAt_id

/-- **`max` is not differentiable at `(1, 1)`.** Along `t ↦ (1 + t, 1)` it is `1 + max(t, 0)`. -/
theorem not_differentiableAt_maxPair : ¬ DifferentiableAt ℝ maxPair ![1, 1] := by
  intro h
  have hfun : (fun t : ℝ ↦ ![1 + t, (1 : ℝ)]) = fun t : ℝ ↦ ![1, 1] + t • ![(1 : ℝ), 0] := by
    funext t
    ext i
    fin_cases i <;> simp [add_comm]
  have hline : DifferentiableAt ℝ (fun t : ℝ ↦ ![1 + t, (1 : ℝ)]) 0 := by
    rw [hfun]
    exact (differentiableAt_const _).add (differentiableAt_id.smul_const _)
  apply not_differentiableAt_one_add_max_zero
  have hcomp := (show DifferentiableAt ℝ maxPair ((fun t : ℝ ↦ ![1 + t, (1 : ℝ)]) 0) by
    simpa using h).comp (0 : ℝ) hline
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Function.comp_apply, maxPair_def, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← max_add_add_left, add_zero]

/-- `λ₁(1 + t diag(1, 0)) = 1 + max(t, 0)`. -/
theorem eigenvalues₀_zero_one_add_smul (t : ℝ)
    (h : ((1 : Matrix (Fin 2) (Fin 2) 𝕜) + (t : 𝕜) • diagonal ![1, 0]).IsHermitian) :
    h.eigenvalues₀ 0 = 1 + max t 0 := by
  have hD : (1 : Matrix (Fin 2) (Fin 2) 𝕜) + (t : 𝕜) • diagonal ![1, 0] =
      diagonal ![((1 + t : ℝ) : 𝕜), (1 : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm, Algebra.algebraMap_eq_smul_one, add_smul]
  have h' : (diagonal ![((1 + t : ℝ) : 𝕜), (1 : ℝ)]).IsHermitian := hD ▸ h
  rw [(h.eigenvalues₀_eq_eigenvalues₀_iff h').2 (by rw [hD])]
  rcases le_total t 0 with ht | ht
  · rw [h'.eigenvalues₀_diagonal_two_swap (by linarith), max_eq_right ht]
    simp
  · rw [h'.eigenvalues₀_diagonal_two (by linarith), max_eq_left ht]
    simp [add_comm]

/-- **The negative control for Lewis's theorem.** The largest eigenvalue
`t ↦ λ₁(1 + t diag(1, 0))` is not differentiable at `t = 0`, where the eigenvalue `1` of the
identity is repeated. -/
theorem not_differentiableAt_eigenvalues₀_zero_one_add_smul
    (h : ∀ t : ℝ, ((1 : Matrix (Fin 2) (Fin 2) 𝕜) + (t : 𝕜) • diagonal ![1, 0]).IsHermitian) :
    ¬ DifferentiableAt ℝ (fun t ↦ (h t).eigenvalues₀ 0) 0 := by
  simp only [eigenvalues₀_zero_one_add_smul]
  exact not_differentiableAt_one_add_max_zero

/-! ### `tr(T²)` -/

/-- At `T = [[0, 1], [1, 0]]`, with eigenvalues `1, -1`, the spectral function of `μ ↦ ∑ μₖ²` is
`tr(T²) = 2` and its gradient is `2T = [[0, 2], [2, 0]]`. -/
theorem spectralGradient_sum_sq_swap
    (hT : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝕜).IsHermitian) :
    hT.eigenvalues₀ = ![1, -1] ∧ ∑ k, hT.eigenvalues₀ k ^ 2 = 2 ∧
      hT.spectralGradient (fun μ ↦ ∑ k, μ k ^ 2) = !![0, 2; 2, 0] := by
  have he : hT.eigenvalues₀ = ![1, -1] := by
    refine hT.eigenvalues₀_eq_of_charpoly_eq_two (by norm_num) ?_
    simp [charpoly_fin_two, trace_fin_two_of, det_fin_two_of]
    ring
  refine ⟨he, ?_, ?_⟩
  · -- The spectral function of `μ ↦ ∑ μₖ²` is `tr(T²)`.
    rw [hT.sum_eigenvalues₀_pow_eq_re_trace_pow, sq, trace_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  · rw [hT.spectralGradient_sum_sq]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num

/-! ### `det^{1/2}` and `det` at `diag(1, 4)` -/

/-- The derivative of the geometric mean at `(4, 1)`: `∂₁ σ₂^{1/2}(4, 1) = 1/4` and
`∂₂ σ₂^{1/2}(4, 1) = 1`. -/
theorem fderiv_geomMean_four_one :
    fderiv ℝ geomMean ![4, 1] (Pi.single 0 1) = 1 / 4 ∧
      fderiv ℝ geomMean ![4, 1] (Pi.single 1 1) = 1 := by
  have hmul := HasFDerivAt.mul (hasFDerivAt_apply (𝕜 := ℝ) 0 (![4, 1] : Fin 2 → ℝ))
    (hasFDerivAt_apply 1 _)
  have h := hmul.rpow_const (p := 2⁻¹) (Or.inl (by norm_num))
  have hpow : (4 : ℝ) ^ ((2⁻¹ : ℝ) - 1) = 1 / 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hg : geomMean = fun μ : Fin 2 → ℝ ↦
      (((fun ν : Fin 2 → ℝ ↦ ν 0) * fun ν : Fin 2 → ℝ ↦ ν 1) μ) ^ (2⁻¹ : ℝ) := by
    funext μ
    simp [geomMean_def]
  rw [hg, h.fderiv]
  simp [hpow]
  norm_num

/-- **The gradient of `det^{1/2}` at `diag(1, 4)`.** For `f = σ₂^{1/2}` and `T = diag(1, 4)`,
whose sorted eigenvalue vector is `(4, 1)`, the gradient is `∇F(T) = diag(1, 1/4)` in the standard
basis, its determinant is `1/4`, and `tr(∇F(T) T) = 2 = F(T)`. -/
theorem spectralGradient_geomMean_one_four
    (hT : (diagonal ![((1 : ℝ) : 𝕜), (4 : ℝ)]).IsHermitian) :
    hT.spectralGradient geomMean = diagonal ![1, 1 / 4] ∧
      (hT.spectralGradient geomMean).det = 1 / 4 ∧
      (hT.spectralGradient geomMean * diagonal ![((1 : ℝ) : 𝕜), (4 : ℝ)]).trace = 2 ∧
      geomMean hT.eigenvalues₀ = 2 := by
  have he : hT.eigenvalues₀ = ![4, 1] := hT.eigenvalues₀_diagonal_two_swap (by norm_num)
  have hG : hT.spectralGradient geomMean = diagonal ![1, 1 / 4] := by
    rw [hT.spectralGradient_eq_mul_diagonal_mul_star geomMean_comp_perm (one_mem _) ![1, 0] (by
      rw [he, star_one, Matrix.one_mul, Matrix.mul_one]
      congr 1
      ext i
      fin_cases i <;> simp), he, star_one, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext i
    fin_cases i
    · exact (congrArg (fun x : ℝ ↦ (x : 𝕜)) fderiv_geomMean_four_one.2).trans (by simp)
    · exact (congrArg (fun x : ℝ ↦ (x : 𝕜)) fderiv_geomMean_four_one.1).trans
        (by norm_num [RCLike.ofReal_ofNat])
  refine ⟨hG, ?_, ?_, ?_⟩
  · rw [hG, det_diagonal, Fin.prod_univ_two]
    simp
  · rw [hG, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
    norm_num [RCLike.ofReal_ofNat]
  · rw [he, geomMean_def]
    simpa using four_rpow_inv_two

/-- **The Euler identity carries the degree.** For `f = σ₂`, homogeneous of degree two, at
`T = diag(1, 4)`: `∇F(T) = det(T) T⁻¹ = diag(4, 1)` and `tr(∇F(T) T) = 8 = 2 F(T)`. -/
theorem spectralGradient_prod_one_four
    (hT : (diagonal ![((1 : ℝ) : 𝕜), (4 : ℝ)]).IsHermitian) :
    hT.spectralGradient (fun μ ↦ ∏ k, μ k) = diagonal ![4, 1] ∧
      (hT.spectralGradient (fun μ ↦ ∏ k, μ k) * diagonal ![((1 : ℝ) : 𝕜), (4 : ℝ)]).trace = 8 ∧
      ∏ k, hT.eigenvalues₀ k = 4 := by
  have hdet : (diagonal ![((1 : ℝ) : 𝕜), (4 : ℝ)]).det = 4 := by
    rw [det_diagonal, Fin.prod_univ_two]
    simp [RCLike.ofReal_ofNat]
  have hG : hT.spectralGradient (fun μ ↦ ∏ k, μ k) = diagonal ![4, 1] := by
    refine hT.spectralGradient_prod_eq_of_mul_eq
      (by rw [hdet]; exact isUnit_iff_ne_zero.2 four_ne_zero) ?_
    rw [hdet]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [RCLike.ofReal_ofNat]
  refine ⟨hG, ?_, ?_⟩
  · rw [hG, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
    norm_num [RCLike.ofReal_ofNat]
  · -- The product of the sorted eigenvalues is the determinant.
    have h := hT.det_eq_prod_eigenvalues₀
    rw [hdet] at h
    exact_mod_cast h.symm

/-! ### The trace inequality at `diag(1, 4)` -/

/-- **The trace inequality `tr(AB) ≥ n (det A det B)^{1/n}`** at `A = diag(1, 4)`: for `B = 1`,
`tr(AB) = 5 ≥ 4 = 2 (det A det B)^{1/2}`, and for `B = A⁻¹ = diag(1, 1/4)` both sides are `2`.
The `n`-th power form `det A det B ≤ (tr(AB)/n)ⁿ` of the library
(`Matrix.PosSemidef.det_mul_det_le_trace_mul_div_card_pow`) reads `4 ≤ (5/2)²` and `1 ≤ 1²`. -/
theorem trace_mul_diagonal_one_four :
    (diagonal ![(1 : ℝ), 4] * 1).trace = 5 ∧
      2 * ((diagonal ![(1 : ℝ), 4]).det * (1 : Matrix (Fin 2) (Fin 2) ℝ).det) ^ (2⁻¹ : ℝ) = 4 ∧
      (diagonal ![(1 : ℝ), 4] * diagonal ![1, 1 / 4]).trace = 2 ∧
      2 * ((diagonal ![(1 : ℝ), 4]).det * (diagonal ![(1 : ℝ), 1 / 4]).det) ^ (2⁻¹ : ℝ) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_one, trace_diagonal, Fin.sum_univ_two]
    norm_num
  · rw [det_one, det_diagonal, Fin.prod_univ_two]
    norm_num [four_rpow_inv_two]
  · rw [diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
    norm_num
  · rw [det_diagonal, det_diagonal, Fin.prod_univ_two, Fin.prod_univ_two]
    norm_num

end TauCeti.SpectralGradientExamples
