/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Coordinate changes for partial operators

`TauCeti.LinearPMap.pullback A e` transports a partial endomorphism `A` along a continuous linear
equivalence `e : E ≃L[R] F`. Its domain is `e ⁻¹' A.domain` and its action is `e⁻¹ A e`.
The graph is the inverse image of the graph of `A` under the product equivalence `e × e`.
Consequently density of the domain and closedness of the operator are invariant under
coordinate changes. No inner product, completeness, or continuity of the partial operator
is required.

The identity, composition, and inverse laws allow successive coordinate changes without
unfolding the construction. For a total continuous operator, pullback agrees with ordinary
conjugation of continuous linear maps.

## References

J. Weidmann, *Linear Operators in Hilbert Spaces*, Chapter 1, closed operators and their graphs.
-/

public section

namespace TauCeti

namespace LinearPMap

section Ring

variable {R E F G : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [AddCommGroup G] [Module R G] [TopologicalSpace G]

/-- Pull a partial operator back along a continuous linear equivalence, transporting both
its domain and its action. -/
def pullback (A : F →ₗ.[R] F) (e : E ≃L[R] F) : E →ₗ.[R] E where
  domain := A.domain.comap e.toLinearMap
  toFun := e.symm.toLinearMap.comp (A.toFun.comp
    ((e.toLinearMap.domRestrict (A.domain.comap e.toLinearMap)).codRestrict A.domain
      fun x ↦ x.property))

/-- The domain of a pulled-back partial operator is the inverse image of its domain. -/
theorem pullback_domain (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    (pullback A e).domain = A.domain.comap e.toLinearMap := (rfl)

/-- Domain membership under a coordinate change. -/
@[simp] theorem mem_pullback_domain (A : F →ₗ.[R] F) (e : E ≃L[R] F)
    {x : E} : x ∈ (pullback A e).domain ↔ e x ∈ A.domain := Iff.rfl

/-- The pulled-back action is `e⁻¹ A e` on its pulled-back domain. -/
@[simp] theorem pullback_apply (A : F →ₗ.[R] F) (e : E ≃L[R] F)
    (x : (pullback A e).domain) :
    pullback A e x = e.symm (A ⟨e x, (mem_pullback_domain A e).mp x.property⟩) := (rfl)

/-- A coordinate change transports both coordinates of the graph. -/
theorem mem_graph_pullback (A : F →ₗ.[R] F) (e : E ≃L[R] F)
    {p : E × E} : p ∈ (pullback A e).graph ↔ (e p.1, e p.2) ∈ A.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hAx⟩
    refine ⟨⟨e x, (mem_pullback_domain A e).mp x.property⟩, congrArg e hx, ?_⟩
    simpa only [pullback_apply, e.apply_symm_apply] using congrArg e hAx
  · rintro ⟨x, hx, hAx⟩
    simp only at hx hAx
    have hxmem : e p.1 ∈ A.domain := by
      rw [← hx]
      exact x.property
    refine ⟨⟨p.1, (mem_pullback_domain A e).mpr hxmem⟩, rfl, ?_⟩
    apply e.injective
    simp only [pullback_apply, e.apply_symm_apply]
    exact (congrArg A (Subtype.ext hx)).symm.trans hAx

/-- The graph of a pullback is the inverse image under the product coordinate change. -/
theorem graph_pullback (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    (pullback A e).graph = A.graph.comap (e.prodCongr e).toLinearMap := by
  ext p
  simp only [mem_graph_pullback, Submodule.mem_comap,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.prodCongr_apply]

/-- Pullback along the identity leaves a partial operator unchanged. -/
@[simp] theorem pullback_refl (A : E →ₗ.[R] E) :
    pullback A (ContinuousLinearEquiv.refl R E) = A := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  simp only [mem_graph_pullback, ContinuousLinearEquiv.refl_apply]

/-- Successive pullbacks compose their coordinate changes in the same order. -/
theorem pullback_pullback (A : G →ₗ.[R] G)
    (f : F ≃L[R] G) (e : E ≃L[R] F) : pullback (pullback A f) e = pullback A (e.trans f) := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  simp only [mem_graph_pullback, ContinuousLinearEquiv.trans_apply]

/-- Pulling back by an equivalence and its inverse recovers the original operator. -/
@[simp] theorem pullback_symm (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    pullback (pullback A e) e.symm = A := by
  rw [pullback_pullback]
  simp

/-- Density of the domain is invariant under continuous linear coordinate changes. -/
@[simp] theorem dense_pullback_domain_iff
    (A : F →ₗ.[R] F) (e : E ≃L[R] F) :
    Dense ((pullback A e).domain : Set E) ↔ Dense (A.domain : Set F) := by
  rw [pullback_domain, Submodule.comap_coe]
  exact e.toHomeomorph.isOpenQuotientMap.dense_preimage_iff

/-- Pullback of an everywhere-defined continuous operator is ordinary conjugation. -/
@[simp] theorem pullback_toPMap_top
    (T : F →L[R] F) (e : E ≃L[R] F) :
    pullback ((T : F →ₗ[R] F).toPMap ⊤) e =
      ((e.symm.toContinuousLinearMap ∘L T ∘L e.toContinuousLinearMap : E →L[R] E) :
        E →ₗ[R] E).toPMap ⊤ := by
  apply LinearPMap.ext
  · simp [pullback_domain]
  · intros
    simp [pullback_apply, LinearMap.toPMap_apply]

end Ring

section Closed

variable {R E F : Type*} [CommRing R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

/-- Closedness of a partial operator is invariant under continuous linear coordinate changes. -/
@[simp] theorem isClosed_pullback_iff
    (A : F →ₗ.[R] F) (e : E ≃L[R] F) : (pullback A e).IsClosed ↔ A.IsClosed := by
  rw [LinearPMap.IsClosed, LinearPMap.IsClosed, graph_pullback, Submodule.comap_coe]
  exact (e.prodCongr e).toHomeomorph.isClosed_preimage

end Closed

end LinearPMap

end TauCeti
