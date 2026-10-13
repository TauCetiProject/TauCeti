/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Approximation numbers of orthogonal projections

An orthogonal projection onto a subspace of dimension `r` has approximation numbers equal to
`1` at indices below `r`, and `0` thereafter. This gives an exact finite-rank model for the
zero-based indexing of approximation numbers. For an infinite-dimensional subspace all the
approximation numbers are `1`.

The formula uses cardinal dimension and only assumes that the subspace admits an orthogonal
projection. Neither the ambient space nor the subspace is required to be finite-dimensional,
and the ambient space need not be complete.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The approximation numbers of an orthogonal projection are `1` below the dimension of
its range and `0` at every other index. This also applies to infinite-dimensional ranges. -/
@[simp]
theorem singularValue_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (n : ℕ) :
    U.starProjection.singularValue n = if (n : Cardinal) < Module.rank 𝕜 U then 1 else 0 := by
  split_ifs with hn
  · apply le_antisymm
    · exact (U.starProjection.singularValue_le_nnnorm n).trans
        (by exact_mod_cast U.starProjection_norm_le)
    · exact_mod_cast U.starProjection.le_singularValue_of_lt_rank hn
        (c := 1) (fun x hx ↦ by simp [U.norm_starProjection_apply hx])
  · apply ContinuousLinearMap.singularValue_eq_zero_of_rank_le
    rw [LinearMap.rank, range_starProjection]
    exact le_of_not_gt hn

end Submodule
