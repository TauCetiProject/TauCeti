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

A continuous multilinear map `M` on finite-dimensional inner product spaces is determined by its
values on tuples of vectors of orthonormal bases `b j`, and its operator norm is controlled by
them: `‖M‖ ≤ ∑_r ‖M (fun j => b j (r j))‖`, the sum running over all tuples `r` of basis indices
(`ContinuousMultilinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`). For a second derivative,
this bounds the norm of the Hessian by the sum of the absolute values of its matrix entries.
The linear case, `‖L‖ ≤ ∑ i, ‖L (b i)‖`, is
`ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`; for a first derivative it bounds
the norm of the gradient by the sum of the absolute values of the partial derivatives.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E G ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

/-- The operator norm of a continuous linear map on an inner product space is at most the sum of
the norms of its values on the vectors of an orthonormal basis. -/
theorem opNorm_le_sum_norm_apply_orthonormalBasis (L : E →L[𝕜] G) (b : OrthonormalBasis ι 𝕜 E) :
    ‖L‖ ≤ ∑ i, ‖L (b i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  -- Expand the argument in the basis and use linearity.
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  gcongr
  exact (PiLp.norm_apply_le (b.repr x) i).trans_eq (b.repr.norm_map x)

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {𝕜 G κ : Type*} {E ι : κ → Type*} [RCLike 𝕜]
  [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace 𝕜 (E j)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [∀ j, Fintype (ι j)] [Fintype κ]

open scoped Classical in
/-- The operator norm of a continuous multilinear map on inner product spaces is at most the sum
of the norms of its values on tuples of vectors of orthonormal bases, one for each argument. -/
theorem opNorm_le_sum_norm_apply_orthonormalBasis
    (M : ContinuousMultilinearMap 𝕜 E G) (b : ∀ j, OrthonormalBasis (ι j) 𝕜 (E j)) :
    ‖M‖ ≤ ∑ r : ∀ j, ι j, ‖M fun j => b j (r j)‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun m => ?_
  -- Expand each argument in the basis and use multilinearity.
  have hM : M m = ∑ r : ∀ j, ι j, (∏ j, (b j).repr (m j) (r j)) •
      M fun j => b j (r j) := by
    conv_lhs => rw [← funext fun j => (b j).sum_repr (m j)]
    rw [M.map_sum]
    exact Finset.sum_congr rfl fun r _ => M.map_smul_univ _ _
  rw [hM, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, norm_prod, mul_comm]
  gcongr with j
  exact (PiLp.norm_apply_le ((b j).repr (m j)) (r j)).trans_eq ((b j).repr.norm_map (m j))

end ContinuousMultilinearMap
