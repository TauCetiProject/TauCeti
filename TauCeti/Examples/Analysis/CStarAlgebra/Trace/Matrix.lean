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
matrix trace on `M_n(ℂ)₊` (`TauCeti.TraceExamples.matrixTrace_complexTrace_of_nonneg`):

* the projection `[[1/2, 1/2], [1/2, 1/2]]` (`TauCeti.TraceExamples.halfProjection`) has
  `τ₂ = 1` although neither diagonal entry is `1`
  (`TauCeti.TraceExamples.matrixTrace_halfProjection`);
* `x = [[1, 1], [1, 1]] ≥ 0` (`TauCeti.TraceExamples.allOnes_nonneg`) has `τ₂(x) = 2`
  (`TauCeti.TraceExamples.matrixTrace_allOnes`), while the sum of all its entries is `4`
  (`TauCeti.TraceExamples.sum_sum_allOnes`); the unitary `U = 2^{-1/2} [[1, 1], [-1, 1]]`
  (`TauCeti.TraceExamples.rotation_mem_unitary`) carries `x` to `diag(2, 0)`
  (`TauCeti.TraceExamples.rotation_mul_allOnes_mul_star_rotation`), which has `τ₂ = 2` but whose
  entries sum to `2` (`TauCeti.TraceExamples.sum_sum_diagTwoZero`), so the sum of all entries is
  not unitarily invariant.
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

/-- The identity trace of `ℂ`, `z ↦ Re z` on `ℂ₊ = [0, ∞)`: the trace of the identity of `ℂ` as a
positive tracial functional. -/
noncomputable def complexTrace : ℂ → ℝ≥0∞ :=
  (PositiveTracialFunctional.ofMapMulComm (PositiveContinuousLinearMap.id ℂ ℂ)
    fun a b ↦ by simp [mul_comm]).toTrace

/-- The value of the identity trace of `ℂ`. -/
theorem complexTrace_apply (z : ℂ) : complexTrace z = ENNReal.ofReal z.re := by
  simp [complexTrace, PositiveTracialFunctional.ofMapMulComm_apply]

/-- For `τ = id` on `ℂ`, `τ_n` is the matrix trace on `M_n(ℂ)₊`. -/
theorem matrixTrace_complexTrace_of_nonneg {n : Type*} [Fintype n] {x : CStarMatrix n n ℂ}
    (hx : 0 ≤ x) :
    matrixTrace complexTrace n x = ENNReal.ofReal (CStarMatrix.ofMatrix.symm x).trace.re := by
  simp only [matrixTrace_apply, complexTrace_apply, Matrix.trace, Matrix.diag, Complex.re_sum]
  exact (ENNReal.ofReal_sum_of_nonneg fun i _ ↦
    (Complex.nonneg_iff.1 (CStarMatrix.diag_nonneg_of_nonneg hx i)).1).symm

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
  rw [matrixTrace_complexTrace_of_nonneg isStarProjection_halfProjection.nonneg]
  norm_num [halfProjection, Matrix.trace_fin_two]

/-- The matrix `[[1, 1], [1, 1]]` of `M₂(ℂ)`. -/
def allOnes : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![1, 1; 1, 1]

/-- `[[1, 1], [1, 1]] = [[1, 1], [0, 0]]⋆ [[1, 1], [0, 0]]`. -/
theorem allOnes_eq_star_topRow_mul_topRow : allOnes = star (topRow 1 1) * topRow 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [allOnes, topRow, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]

/-- `[[1, 1], [1, 1]] ≥ 0`. -/
theorem allOnes_nonneg : 0 ≤ allOnes := by
  rw [allOnes_eq_star_topRow_mul_topRow]
  exact star_mul_self_nonneg _

/-- The matrix `diag(2, 0)` of `M₂(ℂ)`. -/
def diagTwoZero : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![2, 0; 0, 0]

/-- `diag(2, 0) = [[1, 1], [0, 0]] [[1, 1], [0, 0]]⋆`. -/
theorem diagTwoZero_eq_topRow_mul_star_topRow : diagTwoZero = topRow 1 1 * star (topRow 1 1) := by
  rw [topRow_mul_star_topRow, diagTwoZero]
  norm_num

/-- `diag(2, 0) ≥ 0`. -/
theorem diagTwoZero_nonneg : 0 ≤ diagTwoZero := by
  rw [diagTwoZero_eq_topRow_mul_star_topRow]
  exact mul_star_self_nonneg _

/-- The unitary `2^{-1/2} [[1, 1], [-1, 1]]` of `M₂(ℂ)`. -/
noncomputable def rotation : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![(√2 : ℂ)⁻¹, (√2 : ℂ)⁻¹; -(√2 : ℂ)⁻¹, (√2 : ℂ)⁻¹]

/-- `(√2)⁻¹ (√2)⁻¹ = 1/2` in `ℂ`. -/
private theorem inv_sqrt_two_mul_self : (√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `2^{-1/2} [[1, 1], [-1, 1]]` is unitary. -/
theorem rotation_mem_unitary : rotation ∈ unitary (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two,
        inv_sqrt_two_mul_self] <;>
      ring

/-- The unitary `U = 2^{-1/2} [[1, 1], [-1, 1]]` carries `[[1, 1], [1, 1]]` to `diag(2, 0)`. -/
theorem rotation_mul_allOnes_mul_star_rotation :
    rotation * allOnes * star rotation = diagTwoZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, allOnes, diagTwoZero, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two, add_mul, inv_sqrt_two_mul_self]

/-- The amplified trace of `[[1, 1], [1, 1]]` is `2`. -/
theorem matrixTrace_allOnes : matrixTrace complexTrace (Fin 2) allOnes = 2 := by
  rw [matrixTrace_complexTrace_of_nonneg allOnes_nonneg]
  norm_num [allOnes, Matrix.trace_fin_two]

/-- The amplified trace of `diag(2, 0)` is `2`. -/
theorem matrixTrace_diagTwoZero : matrixTrace complexTrace (Fin 2) diagTwoZero = 2 := by
  rw [matrixTrace_complexTrace_of_nonneg diagTwoZero_nonneg]
  norm_num [diagTwoZero, Matrix.trace_fin_two]

/-- The entries of `[[1, 1], [1, 1]]` sum to `4`. -/
theorem sum_sum_allOnes : ∑ i, ∑ j, allOnes i j = 4 := by
  norm_num [allOnes, Fin.sum_univ_two]

/-- The entries of `diag(2, 0)` sum to `2`, so the sum of all entries is not unitarily
invariant. -/
theorem sum_sum_diagTwoZero : ∑ i, ∑ j, diagTwoZero i j = 2 := by
  simp [diagTwoZero, Fin.sum_univ_two]

end Complex

end TauCeti.TraceExamples
