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

end TauCeti.TraceExamples
