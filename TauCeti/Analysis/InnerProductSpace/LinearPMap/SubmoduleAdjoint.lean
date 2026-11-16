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
As a consequence, the adjoint of a closable partial linear map has dense domain.

## Main results

* `Submodule.le_adjoint_adjoint`: double adjoints contain the original submodule.
* `Submodule.topologicalClosure_adjoint`: the adjoint of the topological closure of a
  submodule is the adjoint of the submodule.
* `Submodule.adjoint_adjoint_eq_topologicalClosure`: the double adjoint is the
  topological closure.
* `Submodule.adjoint_adjoint`: equality for closed submodules.
* `LinearPMap.dense_adjoint_domain`: a closable operator has a densely defined
  adjoint.
* `LinearPMap.closure_adjoint`: taking the closure of a partial linear map does not
  change its adjoint.
* `LinearPMap.orthogonal_range_eq_ker_adjoint` and
  `LinearPMap.adjoint_apply_mem_orthogonal_ker`: `(range T)ᗮ = ker T†` when `T` is
  densely defined, and `T† y ∈ (ker T)ᗮ` unconditionally.
* `LinearPMap.adjoint_adjoint_eq_closure` and `LinearPMap.IsClosed.adjoint_adjoint`:
  for a closable densely defined operator `T`, `T†† = T.closure`, so `T†† = T` when
  `T` is closed.
* `ContinuousLinearMap.compPMap_adjoint`: the adjoint of `W ∘ M` for a bounded
  operator `W` and an arbitrary partial linear map `M` is `M† ∘ W†` on its maximal
  domain.

## Provenance

Adapted from the Kitware DKPS formalization, originally authored in `ForTauCeti`
(copyright (c) 2026 Kitware, Inc.; authors Jon Crall and Claude Opus 5; Apache-2.0).

## References

* J. Weidmann, *Linear Operators in Hilbert Spaces*, Graduate Texts in Mathematics 68,
  Springer (1980), Theorem 5.3.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §V.3.3.

-/

public section

open scoped InnerProductSpace LinearPMap

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

/-- Taking the topological closure of a submodule does not change its adjoint, without
completeness assumptions. -/
@[simp]
theorem topologicalClosure_adjoint (g : Submodule 𝕜 (E × F)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  ext x
  simp only [Submodule.mem_adjoint_iff]
  refine ⟨fun h a b hab ↦ h a b (g.le_topologicalClosure hab), fun h a b hab ↦ ?_⟩
  have hcl : IsClosed {p : E × F | inner 𝕜 p.2 x.1 - inner 𝕜 p.1 x.2 = 0} :=
    isClosed_eq ((continuous_snd.inner continuous_const).sub
      (continuous_fst.inner continuous_const)) continuous_const
  exact closure_minimal (fun p hp ↦ h p.1 p.2 hp) hcl (by rwa [← topologicalClosure_coe])

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

section CompleteSource

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem closure_adjoint_domain {T : E →ₗ.[𝕜] F} (hTc : T.IsClosable) :
    T.closure†.domain = T†.domain := by
  refine le_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · rw [mem_adjoint_domain_iff] at hy ⊢
    have hfun : ⇑((innerₛₗ 𝕜 y).comp T.toFun) =
        fun x : T.domain ↦ ((innerₛₗ 𝕜 y).comp T.closure.toFun) ⟨x, T.le_closure.1 x.2⟩ := by
      funext x; simp [T.le_closure.2 (y := ⟨x, T.le_closure.1 x.2⟩) rfl]
    rw [hfun]
    exact hy.comp (continuous_subtype_val.subtype_mk _)
  · rw [mem_adjoint_domain_iff] at hy ⊢
    let φ : StrongDual 𝕜 T.domain := ⟨(innerₛₗ 𝕜 y).comp T.toFun, hy⟩
    have hcl : _root_.IsClosed {p : E × F | ‖inner 𝕜 y p.2‖ ≤ ‖φ‖ * ‖p.1‖} :=
      isClosed_le (continuous_const.inner continuous_snd).norm
        (continuous_const.mul continuous_fst.norm)
    have hsub : (T.closure.graph : Set (E × F)) ⊆
        {p : E × F | ‖inner 𝕜 y p.2‖ ≤ ‖φ‖ * ‖p.1‖} := by
      rw [← hTc.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]
      refine closure_minimal (fun p hp ↦ ?_) hcl
      obtain ⟨u, rfl⟩ := (mem_graph_iff' T).mp hp
      exact φ.le_opNorm u
    exact (((innerₛₗ 𝕜 y).comp T.closure.toFun).mkContinuous ‖φ‖
      fun x ↦ hsub (T.closure.mem_graph x)).continuous

/-- Taking the closure of a partial linear map does not change its adjoint. No closability or
density hypothesis is required: if `T` is not closable then `T.closure = T`, and if `T` is not
densely defined then neither is `T.closure`, so both adjoints share the same domain and take the
junk value `0`. -/
@[simp]
theorem closure_adjoint (T : E →ₗ.[𝕜] F) : T.closure† = T† := by
  by_cases hTc : T.IsClosable
  · by_cases hd : Dense (T.domain : Set E)
    · refine eq_of_eq_graph ?_
      rw [adjoint_graph_eq_graph_adjoint (hd.mono T.le_closure.1),
        adjoint_graph_eq_graph_adjoint hd, ← hTc.graph_closure_eq_closure_graph,
        Submodule.topologicalClosure_adjoint]
    · have hd' : ¬Dense (T.closure.domain : Set E) := fun h ↦ hd <| by
        refine dense_iff_closure_eq.mpr (Set.Subset.antisymm (Set.subset_univ _) ?_)
        refine (dense_iff_closure_eq.mp h).symm.trans_subset (closure_minimal (fun x hx ↦ ?_)
          isClosed_closure)
        have hmem : ((x : E), T.closure ⟨x, hx⟩) ∈ _root_.closure (T.graph : Set (E × F)) := by
          rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe,
            hTc.graph_closure_eq_closure_graph]
          exact T.closure.mem_graph ⟨x, hx⟩
        have hfst := image_closure_subset_closure_image continuous_fst ⟨_, hmem, rfl⟩
        exact closure_mono (by rintro _ ⟨_, hp, rfl⟩; exact mem_domain_of_mem_graph hp) hfst
      refine LinearPMap.ext (closure_adjoint_domain hTc) fun y hy hy' ↦ ?_
      rw [adjoint_apply_of_not_dense hd' ⟨y, hy⟩, adjoint_apply_of_not_dense hd ⟨y, hy'⟩]
  · rw [closure_def' hTc]

/-- For a densely defined partial linear map `T`, the orthogonal complement of its range is the
kernel of its adjoint `T†`. -/
theorem orthogonal_range_eq_ker_adjoint {T : E →ₗ.[𝕜] F} (hd : Dense (T.domain : Set E)) :
    (LinearMap.range T.toFun)ᗮ = T†.ker := by
  refine le_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · have hpair : ∀ x : T.domain, inner 𝕜 (0 : E) (x : E) = inner 𝕜 y (T x) := fun x ↦ by
      rw [inner_zero_left]
      exact (Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self T.toFun x) hy).symm
    have hy' : y ∈ T†.domain := mem_adjoint_domain_of_exists y ⟨0, hpair⟩
    exact mem_ker_iff.2 ⟨⟨y, hy'⟩, rfl, adjoint_apply_eq hd ⟨y, hy'⟩ hpair⟩
  · obtain ⟨z, rfl, hz⟩ := mem_ker_iff.1 hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    rw [toFun_eq_coe, ← inner_conj_symm, ← adjoint_isFormalAdjoint hd z x, hz, inner_zero_left,
      _root_.map_zero]

/-- Every value `T† y` of the adjoint of a partial linear map lies in `(ker T)ᗮ`. No density or
closedness assumption is required: when `T.domain` is not dense, `T†` takes the value `0`. -/
theorem adjoint_apply_mem_orthogonal_ker (T : E →ₗ.[𝕜] F) (y : T†.domain) : T† y ∈ T.kerᗮ := by
  by_cases hd : Dense (T.domain : Set E)
  · rw [Submodule.mem_orthogonal]
    intro x hx
    obtain ⟨u, rfl, hu⟩ := mem_ker_iff.mp hx
    rw [← inner_conj_symm, adjoint_isFormalAdjoint hd y u, hu, inner_zero_right, _root_.map_zero]
  · rw [adjoint_apply_of_not_dense hd]
    exact zero_mem _

end CompleteSource

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

/-- **von Neumann's double-adjoint theorem.** The double adjoint of a closable densely defined
partial linear map between Hilbert spaces is its closure. -/
theorem adjoint_adjoint_eq_closure {T : E →ₗ.[𝕜] F} (hTc : T.IsClosable)
    (hd : Dense (T.domain : Set E)) : T†† = T.closure := by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint (dense_adjoint_domain hTc),
    adjoint_graph_eq_graph_adjoint hd, Submodule.adjoint_adjoint_eq_topologicalClosure,
    hTc.graph_closure_eq_closure_graph]

/-- For a closed densely defined partial linear map between Hilbert spaces, the double adjoint
recovers the map itself: `T†† = T`. -/
theorem IsClosed.adjoint_adjoint {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T†† = T :=
  (adjoint_adjoint_eq_closure hT.isClosable hd).trans <|
    eq_of_eq_graph (hT.isClosable.graph_closure_eq_closure_graph.symm.trans
      hT.submodule_topologicalClosure_eq)

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 G E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The adjoint of a bounded operator composed on the left with an arbitrary partial linear map
`M` is `M† ∘ W†` on its maximal domain `{y | W† y ∈ M†.domain}`. No closedness or density
assumption on `M` is needed. -/
theorem compPMap_adjoint (W : E →L[𝕜] F) (M : G →ₗ.[𝕜] E) :
    ((W : E →ₗ[𝕜] F).compPMap M)† =
      M†.comp ((W.adjoint : F →ₗ[𝕜] E).toPMap (M†.domain.comap (W.adjoint : F →ₗ[𝕜] E)))
        fun y ↦ y.2 := by
  have hdom : ((W : E →ₗ[𝕜] F).compPMap M)†.domain =
      (M†.comp ((W.adjoint : F →ₗ[𝕜] E).toPMap (M†.domain.comap (W.adjoint : F →ₗ[𝕜] E)))
        fun y ↦ y.2).domain := by
    ext y
    -- `LinearPMap.comp` has no simp lemma for `.domain`; unfold it and `compPMap.domain`.
    change y ∈ ((W : E →ₗ[𝕜] F).compPMap M)†.domain ↔ W.adjoint y ∈ M†.domain
    rw [LinearPMap.mem_adjoint_domain_iff, LinearPMap.mem_adjoint_domain_iff]
    have hfun : ⇑((innerₛₗ 𝕜 y).comp ((W : E →ₗ[𝕜] F).compPMap M).toFun) =
        ⇑((innerₛₗ 𝕜 (W.adjoint y)).comp M.toFun) := by
      funext x
      exact (W.adjoint_inner_left (M x) y).symm
    exact Iff.of_eq congr(Continuous $hfun)
  refine LinearPMap.ext hdom fun y hy hy' ↦ ?_
  -- `LinearPMap.comp` has no `@[simp]` evaluation lemma in Mathlib; unfold the RHS application.
  change (((W : E →ₗ[𝕜] F).compPMap M)†) ⟨y, hy⟩ = M† ⟨W.adjoint y, hy'⟩
  by_cases hd : Dense (M.domain : Set G)
  · have hd' : Dense (((W : E →ₗ[𝕜] F).compPMap M).domain : Set G) := hd
    refine LinearPMap.adjoint_apply_eq hd' ⟨y, hy⟩ fun x ↦ ?_
    rw [LinearMap.compPMap_apply, coe_coe,
      LinearPMap.adjoint_isFormalAdjoint hd ⟨W.adjoint y, hy'⟩ x, W.adjoint_inner_left]
  · have hd' : ¬Dense (((W : E →ₗ[𝕜] F).compPMap M).domain : Set G) := hd
    rw [LinearPMap.adjoint_apply_of_not_dense hd' ⟨y, hy⟩,
      LinearPMap.adjoint_apply_of_not_dense hd ⟨W.adjoint y, hy'⟩]

end ContinuousLinearMap

