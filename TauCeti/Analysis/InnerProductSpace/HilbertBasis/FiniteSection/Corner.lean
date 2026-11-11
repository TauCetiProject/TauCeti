/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Basic

/-!
# Finite operators and their orthogonal corners

A finite operator `A` on the first `n + 1` coordinates extends to the ambient Hilbert space
as `J A J†`, where `J = b.finiteInclusion n`. The isometric map `J.cornerEmbedding` preserves
composition and adjoints and takes the finite identity to `b.finiteProjection n`.

Compression by `ContinuousLinearMap.finiteSection` and this extension are mutually inverse
on the corner `P T P = T`. In particular, the operator norm of a finite matrix agrees exactly
with that of its zero extension. This lets finite-section formulas be read as equalities of
operators on one fixed Hilbert space, without losing their finite-dimensional identity.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for zero extension and corner compression in the finite-section method.
-/

public section

open ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

namespace HilbertBasis

/-- Compressing the zero extension of any finite operator recovers that operator. -/
@[simp]
theorem finiteSection_cornerEmbedding (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) :
    ((b.finiteInclusion n).cornerEmbedding A).finiteSection b n = A := by
  rw [finiteSection_def, LinearIsometry.compression_cornerEmbedding]

/-- Every operator supported on the finite-coordinate corner has a unique finite matrix
representative. -/
theorem existsUnique_cornerEmbedding_eq_iff (b : HilbertBasis ℕ 𝕜 H) (n : ℕ)
    (T : H →L[𝕜] H) :
    (∃! A, (b.finiteInclusion n).cornerEmbedding A = T) ↔
      b.finiteProjection n ∘L T ∘L b.finiteProjection n = T := by
  rw [(b.finiteInclusion n).cornerEmbedding.injective.existsUnique_iff_exists]
  simpa only [Set.mem_range, adjoint_finiteInclusion, finiteInclusion_comp_coordinateCutoff,
    compression_def, adjoint_finiteProjection] using
    (b.finiteInclusion n).mem_range_cornerEmbedding_iff T

end HilbertBasis
