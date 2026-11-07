/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
public import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Uniform quadratic bounds for compact positive-definite matrix families

For a continuous family `A : X → Matrix ι ι ℝ` of positive-definite matrices, with compact
parameter space `X` and finite index type `ι`, there are constants `a, b > 0` such that
`a * ‖ξ‖² ≤ (A x).toQuadraticForm' ξ ≤ b * ‖ξ‖²` for every parameter `x` and vector `ξ`.
The same constants work across all parameters and vectors, including in dimension zero.
These uniform ellipticity bounds are used for segment-averaged inverse matrices.

The statement is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

open Set Metric
open scoped Matrix

namespace TauCeti

/-- A compact continuous positive-definite matrix family has common positive lower and upper
quadratic bounds, with constants independent of both the family parameter and the vector. -/
theorem exists_uniform_quadratic_bounds {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [TopologicalSpace X] [CompactSpace X]
    (A : X → Matrix ι ι ℝ) (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x (ξ : EuclideanSpace ℝ ι),
      a * ‖ξ‖ ^ 2 ≤ (A x).toQuadraticForm' ξ ∧
        (A x).toQuadraticForm' ξ ≤ b * ‖ξ‖ ^ 2 := by
  -- Supply the bounded-convergence instances used by the general bilinear coercivity API.
  let : ContinuousAdd (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup
      (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)).toContinuousAdd
  let : ContinuousSMul ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
    ContinuousLinearMap.continuousSMul
  let B : X → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ := fun x =>
    PDE.matrixBilinearForm (A x)
  have hB : Continuous B := PDE.continuous_matrixBilinearForm.comp hA
  have hpositive (x : X) (_ : x ∈ (univ : Set X)) (ξ : EuclideanSpace ℝ ι) (hξ : ξ ≠ 0) :
      0 < B x ξ ξ := by
    change 0 < PDE.matrixBilinearForm (A x) ξ ξ
    rw [PDE.matrixBilinearForm_self, Matrix.toQuadraticForm'_apply]
    apply (hpos x).dotProduct_mulVec_pos
    intro hz
    apply hξ
    ext i
    exact congrFun hz i
  obtain ⟨a, ha, hlo⟩ := isCompact_univ.exists_pos_forall_mul_norm_sq_le
    hB.continuousOn hpositive
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (f := B) hB.continuousOn
  let b : ℝ := max M 0 + 1
  have hMb : M ≤ b := (le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨a, b, ha, by positivity, fun x ξ => ⟨?_, ?_⟩⟩
  · exact (hlo x (mem_univ x) ξ).trans_eq (PDE.matrixBilinearForm_self (A x) ξ)
  · calc
      (A x).toQuadraticForm' ξ ≤ ‖B x‖ * ‖ξ‖ ^ 2 :=
        PDE.toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq (A x) ξ
      _ ≤ b * ‖ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right ((hM x (mem_univ x)).trans hMb) (sq_nonneg _)

end TauCeti
