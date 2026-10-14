/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Coordinate changes for partial operators

`TauCeti.pullbackLinearPMap A e` transports a partial endomorphism `A` along a continuous
linear equivalence `e : E ≃L[R] F`. Its domain is `e ⁻¹' A.domain` and its action is `e⁻¹ A e`.
The graph is the inverse image of the graph of `A` under the product equivalence `e × e`.
Consequently density of the domain and closedness of the operator are invariant under
coordinate changes. No inner product, completeness, or continuity of the partial operator
is required.

The identity, composition, and inverse laws allow successive coordinate changes without
unfolding the construction. For a total linear operator, pullback agrees with ordinary
conjugation of linear maps.

Apply the API by its qualified names, such as `TauCeti.pullbackLinearPMap A e` and
`TauCeti.mem_pullbackLinearPMap_domain A e`. Domain membership and successive inverse
coordinate changes simplify with `simp`.

## References

J. Weidmann, *Linear Operators in Hilbert Spaces*, Chapter 5 (§5.1), closed operators and their
graphs.
-/

public section

namespace TauCeti

section Ring

variable {R E F G : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [AddCommGroup G] [Module R G] [TopologicalSpace G]

/-- Pull a partial operator back along a continuous linear equivalence, transporting both
its domain and its action. -/
def pullbackLinearPMap (A : F →ₗ.[R] F) (e : E ≃L[R] F) : E →ₗ.[R] E where
  domain := A.domain.comap e.toLinearMap
  toFun := e.symm.toLinearMap.comp (A.toFun.comp
    ((e.toLinearMap.domRestrict (A.domain.comap e.toLinearMap)).codRestrict A.domain
      fun x ↦ x.property))

/-- The domain of a pulled-back partial operator is the inverse image of its domain. -/
theorem pullbackLinearPMap_domain (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    (pullbackLinearPMap A e).domain = A.domain.comap e.toLinearMap := (rfl)

/-- Domain membership under a coordinate change. -/
@[simp] theorem mem_pullbackLinearPMap_domain (A : F →ₗ.[R] F) (e : E ≃L[R] F)
    {x : E} : x ∈ (pullbackLinearPMap A e).domain ↔ e x ∈ A.domain := Iff.rfl

/-- The pulled-back action is `e⁻¹ A e` on its pulled-back domain. -/
@[simp] theorem pullbackLinearPMap_apply (A : F →ₗ.[R] F) (e : E ≃L[R] F)
    (x : (pullbackLinearPMap A e).domain) :
    pullbackLinearPMap A e x =
      e.symm (A ⟨e x, (mem_pullbackLinearPMap_domain A e).mp x.property⟩) := (rfl)

/-- A coordinate change transports both coordinates of the graph. -/
theorem mem_graph_pullbackLinearPMap (A : F →ₗ.[R] F) (e : E ≃L[R] F)
    {p : E × E} : p ∈ (pullbackLinearPMap A e).graph ↔ (e p.1, e p.2) ∈ A.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hAx⟩
    refine ⟨⟨e x, (mem_pullbackLinearPMap_domain A e).mp x.property⟩, congrArg e hx, ?_⟩
    simpa only [pullbackLinearPMap_apply, e.apply_symm_apply] using congrArg e hAx
  · rintro ⟨x, hx, hAx⟩
    simp only at hx hAx
    have hxmem : e p.1 ∈ A.domain := by
      rw [← hx]
      exact x.property
    refine ⟨⟨p.1, (mem_pullbackLinearPMap_domain A e).mpr hxmem⟩, rfl, ?_⟩
    apply e.injective
    simp only [pullbackLinearPMap_apply, e.apply_symm_apply]
    exact (congrArg A (Subtype.ext hx)).symm.trans hAx

/-- The graph of a pullback is the inverse image under the product coordinate change. -/
theorem graph_pullbackLinearPMap (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    (pullbackLinearPMap A e).graph = A.graph.comap (e.prodCongr e).toLinearMap := by
  ext p
  simp only [mem_graph_pullbackLinearPMap, Submodule.mem_comap,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.prodCongr_apply]

/-- Pullback along the identity leaves a partial operator unchanged. -/
@[simp] theorem pullbackLinearPMap_refl (A : E →ₗ.[R] E) :
    pullbackLinearPMap A (ContinuousLinearEquiv.refl R E) = A := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  simp only [mem_graph_pullbackLinearPMap, ContinuousLinearEquiv.refl_apply]

/-- Successive pullbacks compose their coordinate changes in the same order. -/
@[simp] theorem pullbackLinearPMap_pullbackLinearPMap (A : G →ₗ.[R] G)
    (f : F ≃L[R] G) (e : E ≃L[R] F) :
    pullbackLinearPMap (pullbackLinearPMap A f) e = pullbackLinearPMap A (e.trans f) := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  simp only [mem_graph_pullbackLinearPMap, ContinuousLinearEquiv.trans_apply]

/-- Pulling back by an equivalence and its inverse recovers the original operator. -/
theorem pullbackLinearPMap_pullbackLinearPMap_symm (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    pullbackLinearPMap (pullbackLinearPMap A e) e.symm = A := by
  rw [pullbackLinearPMap_pullbackLinearPMap]
  simp

/-- Density of the domain is invariant under continuous linear coordinate changes. -/
@[simp] theorem dense_pullbackLinearPMap_domain_iff
    (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    Dense ((pullbackLinearPMap A e).domain : Set E) ↔ Dense (A.domain : Set F) := by
  rw [pullbackLinearPMap_domain, Submodule.comap_coe]
  exact e.toHomeomorph.isOpenQuotientMap.dense_preimage_iff

/-- Pullback of an everywhere-defined linear operator is ordinary conjugation. -/
@[simp] theorem pullbackLinearPMap_toPMap_top
    (T : F →ₗ[R] F) (e : E ≃L[R] F) :
    pullbackLinearPMap (T.toPMap ⊤) e =
      (e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap).toPMap ⊤ := by
  apply LinearPMap.ext
  · simp [pullbackLinearPMap_domain]
  · intros
    simp [pullbackLinearPMap_apply, LinearMap.toPMap_apply]

end Ring

section Closed

variable {R E F : Type*} [CommRing R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

/-- Closedness of a partial operator is invariant under continuous linear coordinate changes. -/
@[simp] theorem isClosed_pullbackLinearPMap_iff
    (A : F →ₗ.[R] F) (e : E ≃L[R] F) : (pullbackLinearPMap A e).IsClosed ↔ A.IsClosed := by
  rw [LinearPMap.IsClosed, LinearPMap.IsClosed, graph_pullbackLinearPMap, Submodule.comap_coe]
  exact (e.prodCongr e).toHomeomorph.isClosed_preimage

end Closed

end TauCeti
