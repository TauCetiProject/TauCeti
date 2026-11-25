/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Pointwise and norm convergence of operators on a finite-dimensional space

On a finite-dimensional normed space `E` the operator norm of `T : E →L[𝕜] F` is controlled by
the norms of the values of `T` on a basis (`Module.Basis.exists_opNorm_le`). So a family of
operators on `E` that tends to zero at every point tends to zero in operator norm
(`ContinuousLinearMap.tendsto_opNorm_zero_of_forall_tendsto_zero`): pointwise smallness at the
finitely many basis vectors is uniform smallness on the unit ball. This is how a quantity that
tends to zero for each element of a finite-dimensional space, such as the tail of a section, is
made uniformly small on the whole space.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a finite-dimensional space, operators that tend to zero at every point tend to zero in
operator norm. -/
theorem tendsto_opNorm_zero_of_forall_tendsto_zero {ι : Type*} {l : Filter ι}
    {T : ι → E →L[𝕜] F} (h : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 0)) :
    Tendsto (fun i ↦ ‖T i‖) l (𝓝 0) := by
  set v := Module.finBasis 𝕜 E
  obtain ⟨C, -, hC⟩ := v.exists_opNorm_le (F := F)
  have hsum : Tendsto (fun i ↦ C * ∑ j, ‖T i (v j)‖) l (𝓝 0) := by
    simpa using (tendsto_finsetSum _ fun j _ ↦ (h (v j)).norm).const_mul C
  refine squeeze_zero (fun i ↦ norm_nonneg _)
    (fun i ↦ hC (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) fun j ↦ ?_) hsum
  exact Finset.single_le_sum (f := fun j ↦ ‖T i (v j)‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_univ j)

end ContinuousLinearMap
