/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

/-!
# Orthogonal projections onto sums of orthogonal subspaces

If `U` and `V` are mutually orthogonal submodules of an inner product space, each admitting an
orthogonal projection, then their sum `U ⊔ V` admits an orthogonal projection as well, namely the
sum `U.starProjection + V.starProjection` of the individual projections. In particular, `U ⊔ V` is
closed and equals its own topological closure, with no completeness assumption on the ambient space.

## Main results

* `Submodule.IsOrtho.hasOrthogonalProjection_sup`: the sum of two orthogonal projected subspaces
  admits an orthogonal projection.
* `Submodule.IsOrtho.starProjection_sup`: the orthogonal projection onto `U ⊔ V` is the sum of
  the projections onto `U` and `V`.
* `Submodule.IsOrtho.isClosed_sup`: the sum of two orthogonal projected subspaces is closed.
* `Submodule.IsOrtho.topologicalClosure_sup`: the topological closure of `U ⊔ V` is `U ⊔ V`.
* `ClosedSubmodule.toSubmodule_sup_of_isOrtho`,
  `ClosedSubmodule.starProjection_sup_of_isOrtho`: the join of two orthogonal closed projected
  submodules has underlying submodule `U.toSubmodule ⊔ V.toSubmodule` and projection
  `U.toSubmodule.starProjection + V.toSubmodule.starProjection`.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {U V : Submodule 𝕜 E}

private theorem sub_starProjection_add_mem_orthogonal_sup
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) (x : E) :
    x - (U.starProjection x + V.starProjection x) ∈ (U ⊔ V)ᗮ := by
  rw [← inf_orthogonal, mem_inf]
  refine ⟨?_, ?_⟩
  · rw [sub_add_eq_sub_sub]
    exact Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x) (h.ge (V.starProjection_apply_mem x))
  · rw [add_comm, sub_add_eq_sub_sub]
    exact Vᗮ.sub_mem (V.sub_starProjection_mem_orthogonal x) (h.le (U.starProjection_apply_mem x))

/-- The sum of two mutually orthogonal subspaces that admit orthogonal projections also admits an
orthogonal projection. No completeness of the ambient space is assumed. -/
theorem IsOrtho.hasOrthogonalProjection_sup
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⟂ V) :
    (U ⊔ V).HasOrthogonalProjection :=
  ⟨fun x ↦ ⟨U.starProjection x + V.starProjection x,
    add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x),
    sub_starProjection_add_mem_orthogonal_sup h x⟩⟩

/-- The orthogonal projection onto the sum of two mutually orthogonal subspaces is the sum of their
orthogonal projections. -/
theorem IsOrtho.starProjection_sup [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⟂ V) [(U ⊔ V).HasOrthogonalProjection] :
    (U ⊔ V).starProjection = U.starProjection + V.starProjection := by
  ext x
  exact eq_starProjection_of_mem_orthogonal
    (add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x))
    (sub_starProjection_add_mem_orthogonal_sup h x)

/-- The sum of two mutually orthogonal subspaces admitting orthogonal projections is closed. -/
theorem IsOrtho.isClosed_sup [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⟂ V) : IsClosed ((U ⊔ V : Submodule 𝕜 E) : Set E) := by
  have := h.hasOrthogonalProjection_sup
  exact (U ⊔ V).isClosed_of_hasOrthogonalProjection

/-- The sum of two mutually orthogonal subspaces admitting orthogonal projections equals its own
topological closure. -/
theorem IsOrtho.topologicalClosure_sup [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⟂ V) : (U ⊔ V).topologicalClosure = U ⊔ V :=
  h.isClosed_sup.submodule_topologicalClosure_eq

end Submodule

namespace ClosedSubmodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If two closed submodules admitting orthogonal projections are mutually orthogonal, their join in
`ClosedSubmodule` requires no closure: its underlying submodule is the algebraic sum
`U.toSubmodule ⊔ V.toSubmodule`. -/
theorem toSubmodule_sup_of_isOrtho {U V : ClosedSubmodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U.toSubmodule ⟂ V.toSubmodule) :
    (U ⊔ V).toSubmodule = U.toSubmodule ⊔ V.toSubmodule :=
  h.topologicalClosure_sup

/-- If two closed submodules admitting orthogonal projections are mutually orthogonal and their
join admits an orthogonal projection, the orthogonal projection onto their join is the sum of the
two orthogonal projections. -/
theorem starProjection_sup_of_isOrtho {U V : ClosedSubmodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [(U ⊔ V).HasOrthogonalProjection]
    (h : U.toSubmodule ⟂ V.toSubmodule) :
    (U ⊔ V).toSubmodule.starProjection =
      U.toSubmodule.starProjection + V.toSubmodule.starProjection := by
  have hsub := toSubmodule_sup_of_isOrtho h
  have aux : ∀ {K : Submodule 𝕜 E} [K.HasOrthogonalProjection],
      K = U.toSubmodule ⊔ V.toSubmodule →
      K.starProjection = U.toSubmodule.starProjection + V.toSubmodule.starProjection := by
    rintro _ _ rfl
    exact h.starProjection_sup
  exact aux hsub

end ClosedSubmodule
