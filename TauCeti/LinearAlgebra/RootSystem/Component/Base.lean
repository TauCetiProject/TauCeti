/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

/-!
# Irreducible components from a base

For a base of a finite reduced crystallographic root pairing over a characteristic-zero domain, the
connected components of the Dynkin diagram are the irreducible components of the pairing, and the
span of the simple roots in a diagram component is the corresponding component space. Since the
irreducible components are defined without a base, this shows that the partition of the roots
obtained from the diagram does not depend on the base.

A diagram edge is a non-orthogonal pair of simple roots, so a diagram component lies in a single
irreducible component. The converse is the substance of the file: every root and its coroot lie in
the spans attached to a single diagram component, because this property is stable under the simple
reflections and every root is reached from a simple root by them. Different diagram components have
orthogonal spans, so non-orthogonal roots stay attached to one diagram component.

## Main definitions

* `RootPairing.Base.componentEquiv`: the bijection from diagram components to irreducible
  components.

## Main results

* `RootPairing.Base.diagramGraph_cartanMatrix_eq_comap`: the diagram is the non-orthogonality graph
  on the simple roots.
* `RootPairing.Base.reachable_nonorthogonalGraph_iff`: two simple roots are in the same irreducible
  component exactly when they are in the same diagram component.
* `RootPairing.Base.span_root_image_supp_eq_componentSpace`,
  `RootPairing.Base.span_coroot_image_supp_eq_corootComponentSpace`: the span of the simple roots of
  a diagram component is a component space, and likewise for coroots.
* `RootPairing.Base.span_root_image_supp_eq_span_root_image_supp`: the component spaces obtained
  from two bases agree.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C.23 and C.55.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
-/

public section

open Submodule (span span_le subset_span)
open TauCeti (diagramGraph diagramGraph_adj)

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] (b : P.Base)

/-- The span of the simple roots in a diagram component. -/
private noncomputable abbrev rootSpanOf (C : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    Submodule R M :=
  span R (P.root '' ((↑) '' C.supp))

/-- The span of the simple coroots in a diagram component. -/
private noncomputable abbrev corootSpanOf (C : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    Submodule R N :=
  span R (P.coroot '' ((↑) '' C.supp))

/-- The roots attached to a diagram component: root in the span of its simple roots and coroot in
the span of its simple coroots. -/
private abbrev AttachedTo (C : (diagramGraph b.cartanMatrix).ConnectedComponent) (k : ι) : Prop :=
  P.root k ∈ b.rootSpanOf C ∧ P.coroot k ∈ b.corootSpanOf C

private theorem root_mem_rootSpanOf (i : b.support) :
    P.root i ∈ b.rootSpanOf ((diagramGraph b.cartanMatrix).connectedComponentMk i) :=
  subset_span ⟨i, ⟨i, rfl, rfl⟩, rfl⟩

private theorem coroot_mem_corootSpanOf (i : b.support) :
    P.coroot i ∈ b.corootSpanOf ((diagramGraph b.cartanMatrix).connectedComponentMk i) :=
  subset_span ⟨i, ⟨i, rfl, rfl⟩, rfl⟩

variable [IsDomain R] [CharZero R]

/-- **The Dynkin diagram of a base is the non-orthogonality graph on its simple roots.** -/
theorem diagramGraph_cartanMatrix_eq_comap :
    diagramGraph b.cartanMatrix = P.nonorthogonalGraph.comap (↑) := by
  ext i j
  have hzero := P.pairing_eq_zero_iff' (i := i) (j := j)
  simp only [diagramGraph_adj, SimpleGraph.comap_adj, nonorthogonalGraph_adj, ne_eq, IsOrthogonal,
    b.cartanMatrix_apply_eq_zero_iff_pairing, Subtype.ext_iff]
  tauto

variable {b} in
private theorem isOrthogonal_of_connectedComponentMk_ne {i j : b.support}
    (h : (diagramGraph b.cartanMatrix).connectedComponentMk i ≠
      (diagramGraph b.cartanMatrix).connectedComponentMk j) :
    P.IsOrthogonal i j := by
  rw [diagramGraph_cartanMatrix_eq_comap] at h
  exact isOrthogonal_of_connectedComponentMk_comap_ne Subtype.val_injective h

/-- Different diagram components have orthogonal spans. -/
private theorem apply_eq_zero_of_mem_of_mem {C D : (diagramGraph b.cartanMatrix).ConnectedComponent}
    (h : C ≠ D) {x : M} {y : N} (hx : x ∈ b.rootSpanOf C) (hy : y ∈ b.corootSpanOf D) :
    P.toLinearMap x y = 0 := by
  have hle : Submodule.map₂ P.toLinearMap (b.rootSpanOf C) (b.corootSpanOf D) ≤ ⊥ := by
    rw [Submodule.map₂_span_span, span_le, Set.image2_subset_iff]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩ _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine (isOrthogonal_of_connectedComponentMk_ne ?_).1
    rwa [(C.mem_supp_iff i).mp hi, (D.mem_supp_iff j).mp hj]
  exact (Submodule.mem_bot R).mp (hle (Submodule.apply_mem_map₂ _ hx hy))

/-- A root is attached to at most one diagram component. -/
private theorem eq_of_attachedTo {C D : (diagramGraph b.cartanMatrix).ConnectedComponent}
    {k : ι} (hC : b.AttachedTo C k) (hD : b.AttachedTo D k) : C = D := by
  by_contra h
  have := b.apply_eq_zero_of_mem_of_mem h hC.1 hD.2
  rw [P.root_coroot_two] at this
  exact two_ne_zero this

variable [Finite ι] [P.IsReduced]

/-- Every root is attached to a diagram component. -/
private theorem exists_attachedTo (k : ι) : ∃ C, b.AttachedTo C k := by
  refine b.induction_reflect k (p := fun k ↦ ∃ C, b.AttachedTo C k) ?_ (fun i hi ↦ ?_) ?_
  · rintro i ⟨C, hr, hc⟩
    refine ⟨C, ?_, ?_⟩
    · rw [root_reflectionPerm, reflection_apply_self]
      exact neg_mem hr
    · rw [coroot_reflectionPerm, coreflection_apply_self]
      exact neg_mem hc
  · exact ⟨_, b.root_mem_rootSpanOf ⟨i, hi⟩, b.coroot_mem_corootSpanOf ⟨i, hi⟩⟩
  · rintro i j ⟨C, hr, hc⟩ hj
    by_cases hC : (diagramGraph b.cartanMatrix).connectedComponentMk ⟨j, hj⟩ = C
    · refine ⟨C, ?_, ?_⟩
      · rw [root_reflectionPerm, reflection_apply]
        exact sub_mem hr (Submodule.smul_mem _ _ (hC ▸ b.root_mem_rootSpanOf ⟨j, hj⟩))
      · rw [coroot_reflectionPerm, coreflection_apply]
        exact sub_mem hc (Submodule.smul_mem _ _ (hC ▸ b.coroot_mem_corootSpanOf ⟨j, hj⟩))
    · rw [P.reflectionPerm_eq_of_pairing_eq_zero
        (b.apply_eq_zero_of_mem_of_mem (Ne.symm hC) hr (b.coroot_mem_corootSpanOf ⟨j, hj⟩))]
      exact ⟨C, hr, hc⟩

/-- Being attached to a diagram component propagates along the non-orthogonality graph. -/
private theorem attachedTo_of_reachable
    {C : (diagramGraph b.cartanMatrix).ConnectedComponent} {k l : ι}
    (hkl : P.nonorthogonalGraph.Reachable k l) (hk : b.AttachedTo C k) : b.AttachedTo C l := by
  obtain ⟨w⟩ := hkl
  induction w with
  | nil => exact hk
  | @cons k m _ hadj _ ih =>
    refine ih ?_
    obtain ⟨D, hD⟩ := b.exists_attachedTo m
    obtain rfl | hCD := eq_or_ne C D
    · exact hD
    · have hzero := b.apply_eq_zero_of_mem_of_mem hCD hk.1 hD.2
      exact absurd ⟨hzero, P.pairing_eq_zero_iff'.mp hzero⟩ (P.nonorthogonalGraph_adj.mp hadj).2

/-- **Every irreducible component contains a simple root.** -/
theorem exists_mem_support_componentOf_eq (k : ι) :
    ∃ j ∈ b.support, P.componentOf j = P.componentOf k := by
  refine b.induction_reflect k (p := fun k ↦ ∃ j ∈ b.support, P.componentOf j = P.componentOf k)
    (fun i ⟨s, hs, h⟩ ↦ ⟨s, hs, h.trans (componentOf_reflectionPerm i i).symm⟩)
    (fun i hi ↦ ⟨i, hi, rfl⟩)
    fun i j ⟨s, hs, h⟩ _ ↦ ⟨s, hs, h.trans (componentOf_reflectionPerm j i).symm⟩

/-- **Two simple roots are in the same irreducible component exactly when they are in the same
component of the Dynkin diagram.** -/
theorem reachable_nonorthogonalGraph_iff {i j : b.support} :
    P.nonorthogonalGraph.Reachable i j ↔ (diagramGraph b.cartanMatrix).Reachable i j := by
  constructor
  · intro h
    refine SimpleGraph.ConnectedComponent.exact (b.eq_of_attachedTo ?_ ?_ (k := j))
    · exact b.attachedTo_of_reachable h ⟨b.root_mem_rootSpanOf i, b.coroot_mem_corootSpanOf i⟩
    · exact ⟨b.root_mem_rootSpanOf j, b.coroot_mem_corootSpanOf j⟩
  · refine fun h ↦ h.map (G' := P.nonorthogonalGraph) ⟨Subtype.val, fun {i j} hij ↦ ?_⟩
    rwa [diagramGraph_cartanMatrix_eq_comap, SimpleGraph.comap_adj] at hij

/-- **The components of the Dynkin diagram of a base are the irreducible components**, by sending
a diagram component to the irreducible component of its simple roots. -/
noncomputable def componentEquiv :
    (diagramGraph b.cartanMatrix).ConnectedComponent ≃ P.Component :=
  Equiv.ofBijective
    (SimpleGraph.ConnectedComponent.lift (fun i : b.support ↦ P.componentOf i) fun i j w _ ↦
      SimpleGraph.ConnectedComponent.sound (b.reachable_nonorthogonalGraph_iff.mpr ⟨w⟩))
    ⟨fun C D ↦ by
      induction C using SimpleGraph.ConnectedComponent.ind
      induction D using SimpleGraph.ConnectedComponent.ind
      intro h
      exact SimpleGraph.ConnectedComponent.sound (b.reachable_nonorthogonalGraph_iff.mp
        (SimpleGraph.ConnectedComponent.exact h)),
    fun C ↦ by
      induction C using SimpleGraph.ConnectedComponent.ind with | _ k => ?_
      obtain ⟨j, hj, hjk⟩ := b.exists_mem_support_componentOf_eq k
      exact ⟨(diagramGraph b.cartanMatrix).connectedComponentMk ⟨j, hj⟩, hjk⟩⟩

@[simp]
theorem componentEquiv_connectedComponentMk (i : b.support) :
    b.componentEquiv ((diagramGraph b.cartanMatrix).connectedComponentMk i) = P.componentOf i :=
  (rfl)

/-- A root is attached to a diagram component exactly when it lies in the corresponding irreducible
component. -/
private theorem attachedTo_iff {C : (diagramGraph b.cartanMatrix).ConnectedComponent}
    {k : ι} : b.AttachedTo C k ↔ P.componentOf k = b.componentEquiv C := by
  obtain ⟨j, hj, hjk⟩ := b.exists_mem_support_componentOf_eq k
  have hj' : b.AttachedTo ((diagramGraph b.cartanMatrix).connectedComponentMk ⟨j, hj⟩) j :=
    ⟨b.root_mem_rootSpanOf ⟨j, hj⟩, b.coroot_mem_corootSpanOf ⟨j, hj⟩⟩
  have hk := b.attachedTo_of_reachable (SimpleGraph.ConnectedComponent.exact hjk) hj'
  rw [← hjk, ← b.componentEquiv_connectedComponentMk ⟨j, hj⟩, b.componentEquiv.apply_eq_iff_eq]
  constructor
  · exact fun h ↦ b.eq_of_attachedTo hk h
  · rintro rfl
    exact hk

/-- **The span of the simple roots in a diagram component is the component space** of the
corresponding irreducible component. -/
theorem span_root_image_supp_eq_componentSpace
    (C : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    span R (P.root '' ((↑) '' C.supp)) = P.componentSpace (b.componentEquiv C) := by
  refine le_antisymm (span_le.mpr ?_) ?_
  · rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine root_mem_componentSpace_of_mem_supp ?_
    rw [← (C.mem_supp_iff i).mp hi]
    exact (b.componentEquiv_connectedComponentMk i).symm
  · rw [P.componentSpace_def]
    refine span_le.mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    exact (b.attachedTo_iff.mpr hk).1

/-- The span of the simple coroots in a diagram component is the coroot component space of the
corresponding irreducible component. -/
theorem span_coroot_image_supp_eq_corootComponentSpace
    (C : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    span R (P.coroot '' ((↑) '' C.supp)) = P.corootComponentSpace (b.componentEquiv C) := by
  refine le_antisymm (span_le.mpr ?_) ?_
  · rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine coroot_mem_corootComponentSpace_of_mem_supp ?_
    rw [← (C.mem_supp_iff i).mp hi]
    exact (b.componentEquiv_connectedComponentMk i).symm
  · rw [P.corootComponentSpace_def]
    refine span_le.mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    exact (b.attachedTo_iff.mpr hk).2

/-- **The decomposition is independent of the base.** A diagram component of a base and the
diagram component of another base with the same irreducible component have the same span of simple
roots. -/
theorem span_root_image_supp_eq_span_root_image_supp (b' : P.Base)
    (C : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    span R (P.root '' ((↑) '' C.supp)) =
      span R (P.root '' ((↑) '' (b'.componentEquiv.symm (b.componentEquiv C)).supp)) := by
  rw [span_root_image_supp_eq_componentSpace, span_root_image_supp_eq_componentSpace,
    Equiv.apply_symm_apply]

end RootPairing.Base
