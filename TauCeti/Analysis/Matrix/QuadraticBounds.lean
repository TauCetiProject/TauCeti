/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
public import TauCeti.Topology.Algebra.Module.BilinearForm
import Mathlib.Analysis.Normed.Module.Normalize

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
    ∑ i, ∑ j, A x i j • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)
  have hB : Continuous B := by
    dsimp only [B]
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (hA.matrix_elem i j).smul continuous_const
  have hdiag (x : X) (ξ : EuclideanSpace ℝ ι) : B x ξ ξ = (A x).toQuadraticForm' ξ := by
    simp only [B, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj, PiLp.proj_apply,
      smul_eq_mul, Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpositive (x : X) (_ : x ∈ (univ : Set X)) (ξ : EuclideanSpace ℝ ι) (hξ : ξ ≠ 0) :
      0 < B x ξ ξ := by
    rw [hdiag, Matrix.toQuadraticForm'_apply]
    apply (hpos x).dotProduct_mulVec_pos
    intro hz
    apply hξ
    ext i
    exact congrFun hz i
  obtain ⟨a, ha, hlo⟩ := isCompact_univ.exists_pos_forall_mul_norm_sq_le
    hB.continuousOn hpositive
  let S : Set (X × EuclideanSpace ℝ ι) := univ ×ˢ Metric.sphere 0 1
  let Q : X × EuclideanSpace ℝ ι → ℝ := fun z => (A z.1).toQuadraticForm' z.2
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere 0 1)
  have hQ : Continuous Q := by
    simp only [Q, Matrix.toQuadraticForm'_apply]
    fun_prop
  obtain ⟨R, hR⟩ := (hS.image hQ).isBounded.exists_norm_le
  let b : ℝ := |R| + 1
  refine ⟨a, b, ha, by positivity, fun x ξ => ⟨?_, ?_⟩⟩
  · rw [← hdiag]
    exact hlo x (mem_univ x) ξ
  · by_cases hξ : ξ = 0
    · simp [hξ]
    have hn : ‖NormedSpace.normalize ξ‖ = 1 := NormedSpace.norm_normalize hξ
    have hm : (x, NormedSpace.normalize ξ) ∈ S :=
      ⟨mem_univ _, by simpa only [mem_sphere_iff_norm, sub_zero] using hn⟩
    have hupper : Q (x, NormedSpace.normalize ξ) ≤ b := by
      have h := hR _ ⟨(x, NormedSpace.normalize ξ), hm, rfl⟩
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans (h.trans
        ((le_abs_self R).trans (le_add_of_nonneg_right zero_le_one)))
    have hscale := (A x).toQuadraticForm'.map_smul ‖ξ‖ (NormedSpace.normalize ξ).ofLp
    rw [← WithLp.ofLp_smul, NormedSpace.norm_smul_normalize, smul_eq_mul, ← pow_two] at hscale
    calc
      (A x).toQuadraticForm' ξ = ‖ξ‖ ^ 2 * Q (x, NormedSpace.normalize ξ) := hscale
      _ ≤ ‖ξ‖ ^ 2 * b := mul_le_mul_of_nonneg_left hupper (sq_nonneg _)
      _ = b * ‖ξ‖ ^ 2 := mul_comm _ _

end TauCeti
