/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.Propagator
import TauCeti.Analysis.Normed.Algebra.NilpotentExponential
import Mathlib.Tactic.FinCases

/-!
# The propagator is time-ordered

On `ℝ²`, with matrices acting through `Matrix.toEuclideanCLM`, take the nilpotent matrices
`A = [[0, 1], [0, 0]]` and `B = [[0, 0], [1, 0]]` and the coefficient `P` equal to `A` on `(-∞, 1)`
and to `B` on `[1, ∞)`. The propagator from `0` to `2` is the time-ordered product
`N_P(2, 0) = exp B ∘ exp A = [[1, 1], [1, 2]]`: by the cocycle identity it is
`N_P(2, 1) ∘ N_P(1, 0)`, and each factor is the exponential of a constant coefficient, since `P` is
`A` almost everywhere on `[0, 1]` and `B` on `(1, 2]`. As `A² = B² = 0`, `exp A = 1 + A` and
`exp B = 1 + B`.

The reversed product `exp A ∘ exp B = [[2, 1], [1, 1]]` differs, and so does the exponential of
the integral `∫₀² P = A + B`: `exp (A + B)` commutes with `A + B`, while `[[1, 1], [1, 2]]` does
not.

## Continuous dependence on the coefficient

For the scalar constant coefficients `p = 0` and `p′ = 1` on `[0, 1]`, the propagators from `0` to
`1` are `1` and `e`, and the bound
`‖N_{p′}(1, 0) − N_p(1, 0)‖ ≤ ‖p′ − p‖_{L¹} exp(‖p′‖_{L¹} + ‖p‖_{L¹})` of
`TauCeti.norm_propagator_sub_propagator_le` reads `e − 1 ≤ e`
(`TauCeti.Examples.Propagator.norm_propagator_one_sub_propagator_zero`). For `P′ = P` the
right-hand side of that bound is `0`
(`TauCeti.Examples.Propagator.integral_norm_sub_self_mul_exp_eq_zero`), and the propagator only
depends on the coefficient almost everywhere (`TauCeti.propagator_congr_ae`).
-/

public section

open MeasureTheory Set NormedSpace

namespace TauCeti.Examples.Propagator

/-- The matrix `[[0, 1], [0, 0]]` as an operator on `ℝ²`. -/
noncomputable abbrev opA : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, 1; 0, 0]

/-- The matrix `[[0, 0], [1, 0]]` as an operator on `ℝ²`. -/
noncomputable abbrev opB : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, 0; 1, 0]

/-- The coefficient equal to `A` on `(-∞, 1)` and to `B` on `[1, ∞)`. -/
noncomputable abbrev coeff (r : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  opB + (Iio 1).indicator (fun _ ↦ opA - opB) r

/-- A square-zero matrix acts with exponential `1 + M`. -/
private theorem exp_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M * M = 0) :
    exp (Matrix.toEuclideanCLM (𝕜 := ℝ) M) = Matrix.toEuclideanCLM (𝕜 := ℝ) (1 + M) := by
  rw [exp_eq_one_add_of_sq_eq_zero ℝ (by rw [← map_pow, sq, hM, map_zero]), map_add, map_one]

/-- Composition of matrix operators is the operator of the matrix product. -/
private theorem toEuclideanCLM_comp {n : Type*} [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℝ) : Matrix.toEuclideanCLM (𝕜 := ℝ) M ∘L Matrix.toEuclideanCLM (𝕜 := ℝ) N =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (M * N) := by
  rw [map_mul, ContinuousLinearMap.mul_def]

private theorem exp_opA : exp opA = Matrix.toEuclideanCLM (𝕜 := ℝ) !![1, 1; 0, 1] := by
  rw [opA, exp_toEuclideanCLM (by ext i j; fin_cases i <;> fin_cases j <;> simp)]
  simp [Matrix.one_fin_two]

private theorem exp_opB : exp opB = Matrix.toEuclideanCLM (𝕜 := ℝ) !![1, 0; 1, 1] := by
  rw [opB, exp_toEuclideanCLM (by ext i j; fin_cases i <;> fin_cases j <;> simp)]
  simp [Matrix.one_fin_two]

private theorem integrableOn_coeff : IntegrableOn coeff (Icc 0 2) :=
  (integrableOn_const (C := opB) measure_Icc_lt_top.ne).add
    ((integrableOn_const (C := opA - opB) measure_Icc_lt_top.ne).indicator measurableSet_Iio)

/-- **The propagator is time-ordered**: `N_P(2, 0) = exp B ∘ exp A = [[1, 1], [1, 2]]`. -/
theorem propagator_coeff_two_zero :
    propagator coeff 2 0 = Matrix.toEuclideanCLM (𝕜 := ℝ) !![1, 1; 1, 2] := by
  have h₁ : propagator coeff 1 0 = exp opA := by
    rw [propagator_congr_ae (Q := fun _ ↦ opA), propagator_const]
    · simp
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with u hu hmem
      rw [uIoc_of_le zero_le_one] at hmem
      simp only [coeff, indicator_of_mem (show u ∈ Iio 1 from lt_of_le_of_ne hmem.2 hu),
        add_sub_cancel]
  have h₂ : propagator coeff 2 1 = exp opB := by
    rw [propagator_congr_ae (Q := fun _ ↦ opB), propagator_const]
    · norm_num
    · refine Filter.Eventually.of_forall fun u hmem ↦ ?_
      rw [uIoc_of_le one_le_two] at hmem
      simp only [coeff, indicator_of_notMem (show u ∉ Iio 1 from not_lt.mpr hmem.1.le), add_zero]
  rw [← propagator_comp_propagator integrableOn_coeff (r := 1) ⟨zero_le_one, one_le_two⟩
    ⟨le_rfl, zero_le_two⟩ ⟨zero_le_two, le_rfl⟩, h₁, h₂, exp_opA, exp_opB, toEuclideanCLM_comp]
  norm_num [Matrix.mul_fin_two]

/-- The reversed product is `exp A ∘ exp B = [[2, 1], [1, 1]]`. -/
theorem exp_opA_comp_exp_opB :
    exp opA ∘L exp opB = Matrix.toEuclideanCLM (𝕜 := ℝ) !![2, 1; 1, 1] := by
  rw [exp_opA, exp_opB, toEuclideanCLM_comp]
  norm_num [Matrix.mul_fin_two]

/-- The propagator differs from the reversed product `exp A ∘ exp B`. -/
theorem exp_opA_comp_exp_opB_ne_propagator : exp opA ∘L exp opB ≠ propagator coeff 2 0 := by
  rw [exp_opA_comp_exp_opB, propagator_coeff_two_zero, Ne, EmbeddingLike.apply_eq_iff_eq]
  intro h
  simpa using congrFun (congrFun h 0) 0

/-- The propagator `N_P(2, 0)` differs from the exponential `exp (A + B)` of the integral
`∫₀² P = A + B` of the coefficient. -/
theorem exp_opA_add_opB_ne_propagator : exp (opA + opB) ≠ propagator coeff 2 0 := by
  intro h
  have hc := ((Commute.refl (opA + opB)).exp_right).eq
  rw [h, propagator_coeff_two_zero, opA, opB, ← map_add] at hc
  simp only [← map_mul, EmbeddingLike.apply_eq_iff_eq] at hc
  simpa [Matrix.mul_fin_two] using congrFun (congrFun hc 0) 1

/-- For the scalar coefficients `0` and `1` on `ℝ`, the propagators from `0` to `1` differ by
`e − 1`, and the right-hand side of `TauCeti.norm_propagator_sub_propagator_le` is `e`. -/
theorem norm_propagator_one_sub_propagator_zero :
    ‖propagator (fun _ ↦ (1 : ℝ →L[ℝ] ℝ)) 1 0 - propagator (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) 1 0‖ =
        Real.exp 1 - 1 ∧
      |∫ _ in (0 : ℝ)..1, ‖(1 : ℝ →L[ℝ] ℝ) - 0‖| *
        Real.exp (|∫ _ in (0 : ℝ)..1, ‖(1 : ℝ →L[ℝ] ℝ)‖| +
          |∫ _ in (0 : ℝ)..1, ‖(0 : ℝ →L[ℝ] ℝ)‖|) = Real.exp 1 := by
  have h1 : propagator (fun _ ↦ (1 : ℝ →L[ℝ] ℝ)) 1 0 = Real.exp 1 • (1 : ℝ →L[ℝ] ℝ) := by
    simp [Real.exp_eq_exp_ℝ, ← Algebra.algebraMap_eq_smul_one, NormedSpace.algebraMap_exp_comm]
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨?_, by simp⟩
  simpa [h1, norm_smul, abs_of_nonneg he] using
    congrArg norm (sub_smul (Real.exp 1) 1 (1 : ℝ →L[ℝ] ℝ)).symm

/-- For `P′ = P` the right-hand side of `TauCeti.norm_propagator_sub_propagator_le` is `0`. -/
theorem integral_norm_sub_self_mul_exp_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : ℝ → E →L[ℝ] E) (t s : ℝ) :
    |∫ u in s..t, ‖P u - P u‖| * Real.exp (|∫ u in s..t, ‖P u‖| + |∫ u in s..t, ‖P u‖|) = 0 := by
  simp

end TauCeti.Examples.Propagator
