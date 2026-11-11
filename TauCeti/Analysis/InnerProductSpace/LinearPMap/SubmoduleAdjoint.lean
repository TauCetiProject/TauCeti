/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Double adjoints of submodules and densely defined operators

The double adjoint of a submodule is its topological closure, so the double
adjoint of a closed submodule is the original submodule.
As a consequence, the adjoint of a closable densely defined partial linear map
has dense domain.

## Main results

* `Submodule.le_adjoint_adjoint`: double adjoints contain the original submodule.
* `Submodule.adjoint_adjoint_eq_topologicalClosure`: the double adjoint is the
  topological closure.
* `Submodule.adjoint_adjoint`: equality for closed submodules.
* `LinearPMap.dense_adjoint_domain`: a closable densely defined operator has a
  densely defined adjoint.

## Provenance

Adapted from the Kitware DKPS formalization, originally authored in `ForTauCeti`
(copyright (c) 2026 Kitware, Inc.; authors Jon Crall and Claude Opus 5; Apache-2.0).

-/

public section

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Every submodule is contained in its double adjoint, without closedness or
completeness assumptions. -/
theorem le_adjoint_adjoint (g : Submodule 𝕜 (E × F)) : g ≤ g.adjoint.adjoint := by
  intro x hx
  rw [Submodule.mem_adjoint_iff]
  intro a b hab
  rw [Submodule.mem_adjoint_iff] at hab
  have h := hab x.1 x.2 (by simpa using hx)
  have h2 := congrArg (starRingEnd 𝕜) h
  simp only [map_sub, inner_conj_symm, map_zero] at h2
  exact sub_eq_zero.mpr (sub_eq_zero.mp h2).symm

/-- The double adjoint of a submodule is its topological closure when the ambient
inner product spaces are complete. -/
theorem adjoint_adjoint_eq_topologicalClosure [CompleteSpace E] [CompleteSpace F]
    (g : Submodule 𝕜 (E × F)) : g.adjoint.adjoint = g.topologicalClosure := by
  refine le_antisymm ?_ (g.topologicalClosure_minimal g.le_adjoint_adjoint ?_)
  · set L := WithLp.prodContinuousLinearEquiv 2 𝕜 E F with hL
    set G : Submodule 𝕜 (WithLp 2 (E × F)) :=
      g.comap (L : WithLp 2 (E × F) →L[𝕜] E × F).toLinearMap with hG
    intro x hx
    have hmem : (L.symm x) ∈ Gᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      rw [Submodule.mem_orthogonal] at hy
      have hab : ((-(WithLp.ofLp y).2 : F), ((WithLp.ofLp y).1 : E)) ∈ g.adjoint := by
        rw [Submodule.mem_adjoint_iff]
        intro c d hcd
        have hu : (L.symm (c, d)) ∈ G := by simpa [hG, hL] using hcd
        have := hy _ hu
        rw [WithLp.prod_inner_apply] at this
        simp only [hL, WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp] at this ⊢
        simp only [inner_neg_right]
        linear_combination -this
      have hxy := (Submodule.mem_adjoint_iff _ x).mp hx _ _ hab
      rw [WithLp.prod_inner_apply]
      simp only [hL, WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp]
      simp only [inner_neg_left] at hxy
      linear_combination hxy
    rw [G.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe, topologicalClosure_coe] at hmem
    rw [← SetLike.mem_coe, topologicalClosure_coe]
    simpa [hG, ← L.preimage_closure] using hmem
  · -- A submodule adjoint is closed: it is the preimage of an orthogonal complement.
    rw [Submodule.adjoint, map_coe, LinearEquiv.coe_coe, LinearEquiv.image_eq_preimage_symm]
    exact (isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

/-- **Involutivity of the submodule adjoint on closed submodules.**

This is the graph-level statement that makes the unbounded-operator adjoint
theory close on itself: with `LinearPMap.adjoint_graph_eq_graph_adjoint` it says
`Γ(T††) = Γ(T)` for closed densely defined `T`. -/
theorem adjoint_adjoint [CompleteSpace E] [CompleteSpace F] (g : Submodule 𝕜 (E × F))
    (hg : IsClosed (g : Set (E × F))) : g.adjoint.adjoint = g :=
  (adjoint_adjoint_eq_topologicalClosure g).trans hg.submodule_topologicalClosure_eq

end Submodule

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **von Neumann's theorem.** The adjoint of a closable densely defined partial
linear map between complete inner product spaces has dense domain. -/
theorem dense_adjoint_domain {T : E →ₗ.[𝕜] F}
    (hT : Dense (T.domain : Set E)) (hTc : T.IsClosable) :
    Dense (T.adjoint.domain : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have hmem : ((0 : E), y) ∈ T.graph.adjoint.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hT] at hab
    simpa using hy a (LinearPMap.mem_domain_of_mem_graph hab)
  rw [Submodule.adjoint_adjoint_eq_topologicalClosure,
    hTc.graph_closure_eq_closure_graph] at hmem
  exact T.closure.graph_fst_eq_zero_snd hmem rfl

end LinearPMap
