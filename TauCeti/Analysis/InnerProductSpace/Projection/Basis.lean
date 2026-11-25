/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Projecting the second block of a basis to an orthogonal complement

Let `b` be a basis of an inner product space `E` indexed by `ι ⊕ κ` whose first block
`b ∘ Sum.inl` spans a subspace `W` admitting an orthogonal projection. The orthogonal projection
to `Wᗮ` kills the first block, and its kernel `W` meets the span of the second block trivially, so
the projections to `Wᗮ` of the second block form a basis of `Wᗮ`
(`Module.Basis.orthogonalProjectionInr`).

For a lattice basis whose first block is a basis of the intersection of the lattice with `W`, this
basis spans the projection of the lattice to `Wᗮ`, and it computes the covolume of that projection.

## Main definitions

* `Module.Basis.orthogonalProjectionInr`: the basis `j ↦ Wᗮ.orthogonalProjectionOnto (b (inr j))`
  of `Wᗮ`, for a basis `b` of `E` indexed by `ι ⊕ κ` whose first block spans `W`.

## References

* T. Horesh and Y. Karasik, *Equidistribution of primitive lattices in ℝⁿ*, Q. J. Math. 74
  (2023), 1253–1294, Proposition B.4, p. 1290.
-/

public section

open Submodule

namespace Module.Basis

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]

/-- If the first block of a basis spans `W`, the projections to `Wᗮ` of the second block are
linearly independent. -/
theorem linearIndependent_orthogonalProjectionOnto_inr (b : Basis (ι ⊕ κ) 𝕜 E)
    (hW : span 𝕜 (Set.range (b ∘ Sum.inl)) = W) :
    LinearIndependent 𝕜 fun j ↦ Wᗮ.orthogonalProjectionOnto (b (.inr j)) := by
  obtain ⟨-, hinr, hdisj⟩ := linearIndependent_sum.1 b.linearIndependent
  refine hinr.map (f := (Wᗮ.orthogonalProjectionOnto : E →ₗ[𝕜] Wᗮ)) ?_
  have hker : LinearMap.ker (Wᗮ.orthogonalProjectionOnto : E →ₗ[𝕜] Wᗮ) = W := by
    simp [orthogonal_orthogonal]
  rw [hker, ← hW]
  exact hdisj.symm

/-- If the first block of a basis spans `W`, the projections to `Wᗮ` of the second block span
`Wᗮ`. -/
theorem span_orthogonalProjectionOnto_inr (b : Basis (ι ⊕ κ) 𝕜 E)
    (hW : span 𝕜 (Set.range (b ∘ Sum.inl)) = W) :
    span 𝕜 (Set.range fun j ↦ Wᗮ.orthogonalProjectionOnto (b (.inr j))) = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  rw [← orthogonalProjectionOnto_mem_subspace_eq_self y]
  have hy : (y : E) ∈ span 𝕜 (Set.range b) := by
    rw [b.span_eq]
    exact mem_top
  -- Every basis vector projects into the span: the first block projects to `0`.
  refine (span_le.2 ?_ : span 𝕜 (Set.range b) ≤
    (span 𝕜 _).comap (Wᗮ.orthogonalProjectionOnto : E →ₗ[𝕜] Wᗮ)) hy
  rintro _ ⟨i | j, rfl⟩
  · rw [SetLike.mem_coe, mem_comap, ContinuousLinearMap.coe_coe,
      orthogonalProjectionOnto_orthogonal_apply_eq_zero (hW ▸ subset_span ⟨i, rfl⟩)]
    exact zero_mem _
  · exact subset_span ⟨j, rfl⟩

/-- The basis of `Wᗮ` formed by the orthogonal projections of the second block of a basis `b` of
`E` indexed by `ι ⊕ κ`, when the first block of `b` spans `W`. -/
noncomputable def orthogonalProjectionInr (b : Basis (ι ⊕ κ) 𝕜 E)
    (hW : span 𝕜 (Set.range (b ∘ Sum.inl)) = W) : Basis κ 𝕜 Wᗮ :=
  .mk (b.linearIndependent_orthogonalProjectionOnto_inr hW)
    (b.span_orthogonalProjectionOnto_inr hW).ge

@[simp]
theorem orthogonalProjectionInr_apply (b : Basis (ι ⊕ κ) 𝕜 E)
    (hW : span 𝕜 (Set.range (b ∘ Sum.inl)) = W) (j : κ) :
    b.orthogonalProjectionInr hW j = Wᗮ.orthogonalProjectionOnto (b (.inr j)) :=
  Basis.mk_apply _ _ j

end Module.Basis
