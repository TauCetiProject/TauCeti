/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Matrix

/-!
# Checks for the matrix amplification of a trace

For `x = [[a, b], [0, 0]]` over a C⋆-algebra `B` with a trace `τ`, `x⋆x` has diagonal entries
`a⋆a` and `b⋆b`, so `x ∈ 𝔫_{τ₂}` iff `a, b ∈ 𝔫_τ`
(`TauCeti.TraceExamples.mem_sqIntegrable_matrixTrace_topRow_iff`), while `xx⋆` has the single
nonzero entry `aa⋆ + bb⋆` (`TauCeti.TraceExamples.topRow_mul_star_topRow`).

For `B = ℂ` and `τ = id` (`TauCeti.TraceExamples.complexTrace`, `z ↦ Re z` on `ℂ₊`), `τ_n` is the
matrix trace on `M_n(ℂ)`:

* the projection `[[1/2, 1/2], [1/2, 1/2]]` (`TauCeti.TraceExamples.halfProjection`) has
  `τ₂ = 1` although neither diagonal entry is `1`
  (`TauCeti.TraceExamples.matrixTrace_halfProjection`);
* `x = [[1, 1], [1, 1]] ≥ 0` has `τ₂(x) = 2`, while the sum of all its entries is `4`; the unitary
  `U = 2^{-1/2} [[1, 1], [-1, 1]]` carries `x` to `diag(2, 0)`, whose entries sum to `2`, so the sum
  of all entries is not unitarily invariant (`TauCeti.TraceExamples.unitaryConj_allOnes`).
-/

public section

open scoped ENNReal

namespace TauCeti.TraceExamples

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

/-- The matrix `[[a, b], [0, 0]]` of `M₂(B)`. -/
def topRow (a b : B) : CStarMatrix (Fin 2) (Fin 2) B :=
  CStarMatrix.ofMatrix !![a, b; 0, 0]

omit [PartialOrder B] [StarOrderedRing B] in
/-- `[[a, b], [0, 0]] [[a, b], [0, 0]]⋆ = [[aa⋆ + bb⋆, 0], [0, 0]]`. -/
theorem topRow_mul_star_topRow (a b : B) :
    topRow a b * star (topRow a b) =
      CStarMatrix.ofMatrix !![a * star a + b * star b, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topRow, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]

/-- `[[a, b], [0, 0]] ∈ 𝔫_{τ₂}` iff `a, b ∈ 𝔫_τ`. -/
theorem mem_sqIntegrable_matrixTrace_topRow_iff (hτ : IsTrace τ) (a b : B) :
    topRow a b ∈ sqIntegrable (matrixTrace τ (Fin 2)) ↔
      a ∈ sqIntegrable τ ∧ b ∈ sqIntegrable τ := by
  rw [hτ.mem_sqIntegrable_matrixTrace_iff]
  simp [topRow, Fin.forall_fin_two, hτ.map_zero]

/-! ### The amplification of the identity trace of `ℂ` -/

section Complex

open scoped ComplexOrder

/-- The identity trace of `ℂ`, `z ↦ Re z` on `ℂ₊ = [0, ∞)`. -/
noncomputable def complexTrace (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal z.re

theorem isTrace_complexTrace : IsTrace complexTrace where
  map_add_of_nonneg x y hx hy := by
    simp only [complexTrace, Complex.add_re]
    exact ENNReal.ofReal_add (Complex.nonneg_iff.1 hx).1 (Complex.nonneg_iff.1 hy).1
  map_nnreal_smul_of_nonneg c x _ := by
    simp only [complexTrace, Complex.real_smul, Complex.re_ofReal_mul]
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  map_star_mul_self x := by rw [mul_comm]

/-- The projection `[[1/2, 1/2], [1/2, 1/2]]` of `M₂(ℂ)`. -/
noncomputable def halfProjection : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- `[[1/2, 1/2], [1/2, 1/2]]` is a projection. -/
theorem isStarProjection_halfProjection : IsStarProjection halfProjection := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfProjection, CStarMatrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [halfProjection, CStarMatrix.star_apply]

/-- The amplified trace of `[[1/2, 1/2], [1/2, 1/2]]` is `1`, although neither diagonal entry
is `1`. -/
theorem matrixTrace_halfProjection : matrixTrace complexTrace (Fin 2) halfProjection = 1 := by
  rw [matrixTrace_apply, Fin.sum_univ_two]
  simp only [halfProjection, complexTrace]
  simp only [CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- The matrix `[[1, 1], [1, 1]]` of `M₂(ℂ)`. -/
def allOnes : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![1, 1; 1, 1]

/-- The unitary `2^{-1/2} [[1, 1], [-1, 1]]` of `M₂(ℂ)`. -/
noncomputable def rotation : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![(√2 : ℂ)⁻¹, (√2 : ℂ)⁻¹; -(√2 : ℂ)⁻¹, (√2 : ℂ)⁻¹]

theorem inv_sqrt_two_mul_self : (√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem rotation_mem_unitary : rotation ∈ unitary (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff]
  have h := inv_sqrt_two_mul_self
  have hc : (starRingEnd ℂ) (√2 : ℂ)⁻¹ = (√2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two, hc, h] <;>
      ring

/-- `x = [[1, 1], [1, 1]]` has `τ₂(x) = 2` and entry sum `4`, and the unitary `U` carries it to
`diag(2, 0)`, which has `τ₂ = 2` but entry sum `2`. -/
theorem unitaryConj_allOnes :
    rotation * allOnes * star rotation = CStarMatrix.ofMatrix !![2, 0; 0, 0] ∧
      matrixTrace complexTrace (Fin 2) allOnes = 2 ∧
      matrixTrace complexTrace (Fin 2) (CStarMatrix.ofMatrix !![(2 : ℂ), 0; 0, 0]) = 2 ∧
      ∑ i, ∑ j, allOnes i j = 4 ∧
      ∑ i, ∑ j, (CStarMatrix.ofMatrix !![(2 : ℂ), 0; 0, 0] :
        CStarMatrix (Fin 2) (Fin 2) ℂ) i j = 2 := by
  have h := inv_sqrt_two_mul_self
  have hc : (starRingEnd ℂ) (√2 : ℂ)⁻¹ = (√2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, allOnes, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two,
        hc]
    linear_combination (4 : ℂ) * h
  · simp [matrixTrace_apply, allOnes, complexTrace, Fin.sum_univ_two, one_add_one_eq_two]
  · simp [matrixTrace_apply, complexTrace, Fin.sum_univ_two]
  · simp [allOnes, Fin.sum_univ_two]
    norm_num
  · simp [Fin.sum_univ_two]

end Complex

end TauCeti.TraceExamples
