/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Double adjoints of submodules and densely defined operators

The double adjoint of a submodule of a product of complete spaces is its topological closure,
and the double adjoint of a complete submodule is the original submodule.
As a consequence, the adjoint of a closable partial linear map has dense domain.

## Main results

* `Submodule.le_adjoint_adjoint`: double adjoints contain the original submodule.
* `Submodule.adjoint_adjoint_eq_topologicalClosure`: the double adjoint is the
  topological closure.
* `Submodule.adjoint_adjoint`: equality for complete submodules.
* `LinearPMap.dense_adjoint_domain`: a closable operator has a densely defined
  adjoint.
* `LinearPMap.tendsto_inner_apply_of_isClosable`: for closable `A`, a sequence `uₙ → 0` of
  `dom A` with `‖A uₙ‖ ≤ 1` has `A uₙ → 0` weakly.
* `LinearPMap.adjoint_adjoint_eq_closure`: `T†† = closure T` for a closable densely defined
  operator.
* `LinearPMap.adjoint_adjoint`, `LinearPMap.adjoint_adjoint_apply`: `T†† = T` for a closed
  densely defined operator.

## Provenance

Adapted from the Kitware DKPS formalization, originally authored in `ForTauCeti`
(copyright (c) 2026 Kitware, Inc.; authors Jon Crall and Claude Opus 5; Apache-2.0).

-/

public section

open Filter Topology
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

/-- Transport of the double adjoint to the `L²` product: a point of `g.adjoint.adjoint` lies in
the double orthogonal complement of the copy of `g` in `WithLp 2 (E × F)`. -/
private theorem toLp_mem_orthogonal_orthogonal_of_mem_adjoint_adjoint {g : Submodule 𝕜 (E × F)}
    {x : E × F} (hx : x ∈ g.adjoint.adjoint) :
    WithLp.toLp 2 x ∈ (g.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap)ᗮᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have hab : ((-(WithLp.ofLp y).2 : F), ((WithLp.ofLp y).1 : E)) ∈ g.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro c d hcd
    have := hy (WithLp.toLp 2 (c, d)) (by simpa using hcd)
    rw [WithLp.prod_inner_apply] at this
    simp only [inner_neg_right]
    linear_combination -this
  have hxy := (Submodule.mem_adjoint_iff _ x).mp hx _ _ hab
  rw [WithLp.prod_inner_apply]
  simp only [inner_neg_left] at hxy
  linear_combination hxy

/-- The double adjoint of a submodule is its topological closure when the ambient
inner product spaces are complete. -/
theorem adjoint_adjoint_eq_topologicalClosure [CompleteSpace E] [CompleteSpace F]
    (g : Submodule 𝕜 (E × F)) : g.adjoint.adjoint = g.topologicalClosure := by
  refine le_antisymm (fun x hx => ?_) (g.topologicalClosure_minimal g.le_adjoint_adjoint ?_)
  · have hmem := toLp_mem_orthogonal_orthogonal_of_mem_adjoint_adjoint hx
    rw [orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe, topologicalClosure_coe, comap_coe,
      LinearEquiv.coe_toLinearMap, WithLp.coe_linearEquiv] at hmem
    rw [← SetLike.mem_coe, topologicalClosure_coe]
    simpa using (WithLp.prod_continuous_ofLp 2 E F).closure_preimage_subset _ hmem
  · -- A submodule adjoint is closed: it is the preimage of an orthogonal complement.
    rw [Submodule.adjoint, map_coe, LinearEquiv.coe_coe, LinearEquiv.image_eq_preimage_symm]
    exact (isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

/-- **Involutivity of the submodule adjoint on complete submodules.**

This is the graph-level statement that makes the unbounded-operator adjoint
theory close on itself: with `LinearPMap.adjoint_graph_eq_graph_adjoint` it says
`Γ(T††) = Γ(T)` for closed densely defined `T`. Only the submodule needs to be complete, not
the ambient spaces: the proof applies `Submodule.orthogonal_orthogonal`, whose
`HasOrthogonalProjection` hypothesis a complete submodule satisfies through
`Submodule.HasOrthogonalProjection.ofCompleteSpace`. In complete ambient spaces, apply it to a
closed submodule through `IsClosed.isComplete`. -/
@[simp]
theorem adjoint_adjoint (g : Submodule 𝕜 (E × F)) (hg : IsComplete (g : Set (E × F))) :
    g.adjoint.adjoint = g := by
  refine le_antisymm (fun x hx => ?_) g.le_adjoint_adjoint
  set G := g.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  -- `G` is the image of `g` under the uniform equivalence `WithLp.toLp`, hence complete.
  have : CompleteSpace G := by
    refine completeSpace_coe_iff_isComplete.mpr ?_
    rwa [comap_coe, LinearEquiv.coe_toLinearMap, ← LinearEquiv.image_symm_eq_preimage,
      WithLp.coe_symm_linearEquiv, (WithLp.isUniformInducing_toLp 2 E F).isComplete_iff]
  have hmem := toLp_mem_orthogonal_orthogonal_of_mem_adjoint_adjoint hx
  rw [orthogonal_orthogonal] at hmem
  simpa [G] using hmem

end Submodule

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **von Neumann's theorem.** The adjoint of a closable partial linear map between
complete inner product spaces has dense domain.

No density of `T.domain` is needed: the domain of `T.adjoint` is
`{y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}` whether or not `T` is densely defined
(only the values of `T.adjoint` are junk off the densely defined case). -/
theorem dense_adjoint_domain {T : E →ₗ.[𝕜] F} (hTc : T.IsClosable) :
    Dense (T.adjoint.domain : Set F) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have hmem : ((0 : E), y) ∈ T.graph.adjoint.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    -- `(a, b)` in the graph adjoint means `⟪b, x⟫ = ⟪a, T x⟫` on `T.domain`, so
    -- `x ↦ ⟪a, T x⟫` is continuous and `a` lies in the domain of `T.adjoint`.
    have ha : a ∈ T.adjoint.domain := by
      refine LinearPMap.mem_adjoint_domain_of_exists a ⟨b, fun x => ?_⟩
      have h := sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hab _ _ (T.mem_graph x))
      rw [← inner_conj_symm, ← h, inner_conj_symm]
    simpa using hy a ha
  rw [Submodule.adjoint_adjoint_eq_topologicalClosure,
    hTc.graph_closure_eq_closure_graph] at hmem
  exact T.closure.graph_fst_eq_zero_snd hmem rfl

/-- **The double adjoint is the closure.** For a closable densely defined partial linear map `T`
between Hilbert spaces, `T†† = closure T`. -/
theorem adjoint_adjoint_eq_closure {T : E →ₗ.[𝕜] F} (hT : T.IsClosable)
    (hd : Dense (T.domain : Set E)) : T.adjoint.adjoint = T.closure := by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint (dense_adjoint_domain hT), adjoint_graph_eq_graph_adjoint hd,
    Submodule.adjoint_adjoint_eq_topologicalClosure, hT.graph_closure_eq_closure_graph]

/-- **The adjoint of a closed operator is involutive.** For a closed densely defined partial linear
map `T` between Hilbert spaces, `T†† = T`. -/
theorem adjoint_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    T.adjoint.adjoint = T :=
  (adjoint_adjoint_eq_closure hT.isClosable hd).trans hT.closure_eq

/-- For a closed densely defined `T`, the double adjoint `T††` evaluates as `T` on `dom T`. -/
theorem adjoint_adjoint_apply {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    (x : T.domain) : T.adjoint.adjoint ⟨x, (adjoint_adjoint hT hd).symm ▸ x.property⟩ = T x :=
  (adjoint_adjoint hT hd).le.2 rfl

/-- For a closable `A` and a sequence `uₙ → 0` of `dom A` with `‖A uₙ‖ ≤ 1`, the vectors `A uₙ`
tend to zero weakly: they do so against the dense domain of the adjoint
(`LinearPMap.dense_adjoint_domain`), and they are bounded. -/
theorem tendsto_inner_apply_of_isClosable {A : E →ₗ.[𝕜] F} (hA : A.IsClosable)
    {u : ℕ → A.domain} (hu : Tendsto (fun n ↦ (u n : E)) atTop (𝓝 0))
    (hAu : ∀ n, ‖A (u n)‖ ≤ 1) (k : F) : Tendsto (fun n ↦ ⟪A (u n), k⟫_𝕜) atTop (𝓝 0) := by
  have hD (b : F) (hb : b ∈ A.adjoint.domain) :
      Tendsto (fun n ↦ ⟪A (u n), b⟫_𝕜) atTop (𝓝 0) := by
    -- On `dom A†`, `x ↦ ⟪b, A x⟫` is continuous, so it tends to `0` along `uₙ → 0`.
    have hc : Continuous ((innerₛₗ 𝕜 b).comp A.toFun) := (A.mem_adjoint_domain_iff b).mp hb
    have h₁ : Tendsto (fun n ↦ ⟪b, A (u n)⟫_𝕜) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (hc.tendsto 0).comp (tendsto_subtype_rng.mpr (by simpa using hu))
    simpa [Function.comp_def, inner_conj_symm] using
      ((RCLike.continuous_conj (K := 𝕜)).tendsto 0).comp h₁
  have := ContinuousLinearMap.tendsto_apply_of_dense (dense_adjoint_domain hA) (l := atTop)
    (f := fun n ↦ innerSL 𝕜 (A (u n))) (g := 0) (C := 1)
    (.of_forall fun n ↦ (innerSL_apply_norm 𝕜 _).trans_le (hAu n))
    (fun b hb ↦ by simpa using hD b hb) k
  simpa using this

end LinearPMap
