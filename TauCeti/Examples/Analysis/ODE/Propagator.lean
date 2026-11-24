/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.Propagator
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

/-- An element of square zero has exponential `1 + x`. -/
private theorem exp_eq_one_add_of_sq_eq_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {x : 𝔸} (hx : x ^ 2 = 0) : exp x = 1 + x := by
  have hpow (n : ℕ) (hn : 2 ≤ n) : x ^ n = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, hx, zero_mul]
  rw [exp_eq_tsum ℝ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 2) fun n hn ↦ by
    rw [hpow n (by simp at hn; omega), smul_zero]]
  simp [Finset.sum_range_succ]

private theorem exp_opA : exp opA = Matrix.toEuclideanCLM (𝕜 := ℝ) !![1, 1; 0, 1] := by
  have hsq : opA ^ 2 = 0 := by
    rw [opA, ← map_pow, ← map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2))]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_one_add_of_sq_eq_zero hsq,
    opA, ← map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)), ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem exp_opB : exp opB = Matrix.toEuclideanCLM (𝕜 := ℝ) !![1, 0; 1, 1] := by
  have hsq : opB ^ 2 = 0 := by
    rw [opB, ← map_pow, ← map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2))]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_one_add_of_sq_eq_zero hsq,
    opB, ← map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)), ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

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
    ⟨le_rfl, zero_le_two⟩ ⟨zero_le_two, le_rfl⟩, h₁, h₂, exp_opA, exp_opB,
    ← ContinuousLinearMap.mul_def, ← map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The propagator differs from the reversed product `exp A ∘ exp B = [[2, 1], [1, 1]]`. -/
theorem exp_opA_comp_exp_opB :
    exp opA ∘L exp opB = Matrix.toEuclideanCLM (𝕜 := ℝ) !![2, 1; 1, 1] ∧
      exp opA ∘L exp opB ≠ propagator coeff 2 0 := by
  have h : exp opA ∘L exp opB = Matrix.toEuclideanCLM (𝕜 := ℝ) !![2, 1; 1, 1] := by
    rw [exp_opA, exp_opB, ← ContinuousLinearMap.mul_def, ← map_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  refine ⟨h, ?_⟩
  rw [h, propagator_coeff_two_zero, Ne, EmbeddingLike.apply_eq_iff_eq]
  intro h'
  simpa using congrFun (congrFun h' 0) 0

/-- The propagator differs from the exponential `exp (A + B)` of the integral of the coefficient:
`exp (A + B)` commutes with `A + B`, and `[[1, 1], [1, 2]]` does not. -/
theorem exp_opA_add_opB_ne : exp (opA + opB) ≠ propagator coeff 2 0 := by
  intro h
  have hc : Commute (opA + opB) (exp (opA + opB)) := (Commute.refl _).exp_right
  rw [h, propagator_coeff_two_zero, opA, opB, ← map_add, Commute, SemiconjBy, ← map_mul,
    ← map_mul, EmbeddingLike.apply_eq_iff_eq] at hc
  simpa [Matrix.mul_fin_two] using congrFun (congrFun hc 0) 1

end TauCeti.Examples.Propagator
