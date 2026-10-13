/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# The norm of a multilinear map on an orthonormal basis

A continuous multilinear map `M` on a finite-dimensional inner product space is determined by its
values on tuples of vectors of an orthonormal basis `b`, and its operator norm is controlled by
them: `‖M‖ ≤ ∑_r ‖M (b ∘ r)‖`, the sum running over all tuples `r` of basis indices
(`ContinuousMultilinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`). For a second derivative,
this bounds the norm of the Hessian by the sum of the absolute values of its matrix entries.
-/

public section

namespace ContinuousMultilinearMap

variable {𝕜 E G ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The operator norm of a continuous multilinear map on an inner product space is at most the sum
of the norms of its values on tuples of vectors of an orthonormal basis. -/
theorem opNorm_le_sum_norm_apply_orthonormalBasis
    (M : ContinuousMultilinearMap 𝕜 (fun _ : κ => E) G) (b : OrthonormalBasis ι 𝕜 E) :
    ‖M‖ ≤ ∑ r : κ → ι, ‖M fun j => b (r j)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m => ?_
  -- Expand each argument in the basis and use multilinearity.
  have hM : M m = ∑ r : κ → ι, (∏ j, b.repr (m j) (r j)) • M fun j => b (r j) := by
    conv_lhs => rw [show m = fun j => ∑ i, b.repr (m j) i • b i from
      funext fun j => (b.sum_repr (m j)).symm]
    rw [M.map_sum]
    exact Finset.sum_congr rfl fun r _ => M.map_smul_univ _ _
  rw [hM, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, norm_prod, mul_comm]
  gcongr with j
  rw [b.repr_apply_apply]
  simpa [b.orthonormal.1 (r j)] using norm_inner_le_norm (𝕜 := 𝕜) (b (r j)) (m j)

end ContinuousMultilinearMap
