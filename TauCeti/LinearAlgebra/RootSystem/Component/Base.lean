/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.Basic
public import TauCeti.LinearAlgebra.RootSystem.Component.Aut
public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.Algebra.Group.Submonoid.Closure

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

For a finite root system over a field, a base also restricts to each irreducible component: the
simple roots lying in a component form a base of its component pairing, because up to sign every
root of the component is a sum of simple roots in which only those of its own component can occur.
Heights and positivity of roots of the component are the same for both bases.

## Main definitions

* `RootPairing.Base.componentEquiv`: the bijection from diagram components to irreducible
  components.
* `RootPairing.Base.componentBase`: the base of the component pairing formed by the simple roots in
  the component.
* `RootPairing.Base.componentWeightBasis`: the simple roots of `b` in `C` as a basis of
  `P.componentSpace C`.
* `RootPairing.Equiv.diagramGraphIso`: the Dynkin-diagram isomorphism induced by a base-preserving
  equivalence.

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
* `RootPairing.Base.cartanMatrixIn_componentBase`: the Cartan matrix of the base of a component is
  the corresponding block of the Cartan matrix of the whole base.
* `RootPairing.Base.mem_closure_root_componentBase_iff`,
  `RootPairing.Base.height_componentBase`: the base of a component has the positive cone and the
  heights cut out by the whole base.
* `RootPairing.Equiv.componentEquiv_base_componentEquiv`: a base-preserving equivalence agrees
  between `componentEquiv` and `diagramGraphIso`.

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

/-- The simple roots of `b` in the diagram component corresponding to `C` are those in `C`. -/
theorem mem_supp_componentEquiv_symm (C : P.Component) {i : b.support} :
    i ∈ (b.componentEquiv.symm C).supp ↔ (i : ι) ∈ C.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, Equiv.eq_symm_apply,
    componentEquiv_connectedComponentMk, SimpleGraph.ConnectedComponent.mem_supp_iff]

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

/-! ### The base of a component pairing -/

section ComponentPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] (b : P.Base) (C : P.Component)

/-- The **base of the component pairing** of `C` cut out by a base `b`: its simple roots are the
simple roots of `b` lying in `C`. -/
noncomputable def componentBase : (P.componentPairing C).Base where
  support := b.support.preimage (↑) Subtype.val_injective.injOn
  linearIndepOn_root := by
    have h : (P.componentSpace C).subtype ∘ (P.componentPairing C).root = P.root ∘ (↑) :=
      funext (P.coe_componentPairing_root C)
    rw [Finset.coe_preimage]
    refine .of_comp (P.componentSpace C).subtype ?_
    rw [h]
    exact (b.linearIndepOn_root.mono (Set.image_preimage_subset _ _)).comp_of_image
      Subtype.val_injective.injOn
  linearIndepOn_coroot := by
    have h : (P.corootComponentSpace C).subtype ∘ (P.componentPairing C).coroot = P.coroot ∘ (↑) :=
      funext (P.coe_componentPairing_coroot C)
    rw [Finset.coe_preimage]
    refine .of_comp (P.corootComponentSpace C).subtype ?_
    rw [h]
    exact (b.linearIndepOn_coroot.mono (Set.image_preimage_subset _ _)).comp_of_image
      Subtype.val_injective.injOn
  root_mem_or_neg_mem i := by
    rw [Finset.coe_preimage]
    refine (b.root_mem_or_neg_mem i).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      exact (AddSubmonoid.mem_closure_image_preimage_val_iff (P.coe_componentPairing_root C)).mpr
        (mem_closure_root_inter_supp (by simpa using h) (Subtype.prop _))
  coroot_mem_or_neg_mem i := by
    rw [Finset.coe_preimage]
    refine (b.coroot_mem_or_neg_mem i).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      exact
        (AddSubmonoid.mem_closure_image_preimage_val_iff (P.coe_componentPairing_coroot C)).mpr
        (mem_closure_coroot_inter_supp (by simpa using h) (Subtype.prop _))

theorem support_componentBase :
    (b.componentBase C).support = b.support.preimage (↑) Subtype.val_injective.injOn := by
  simp [componentBase]

/-- The simple roots of the component base are the simple roots of `b` in `C`. -/
@[simp]
theorem mem_support_componentBase {i : C.supp} :
    i ∈ (b.componentBase C).support ↔ (i : ι) ∈ b.support := by
  simp [support_componentBase]

/-- **The positive cone of the component base**: a vector of the component space of `C` is a sum
of simple roots of the component base exactly when it is a sum of simple roots of `b`. -/
theorem mem_closure_root_componentBase_iff {x : P.componentSpace C} :
    x ∈ AddSubmonoid.closure ((P.componentPairing C).root '' (b.componentBase C).support) ↔
      (x : M) ∈ AddSubmonoid.closure (P.root '' b.support) := by
  rw [support_componentBase, Finset.coe_preimage,
    AddSubmonoid.mem_closure_image_preimage_val_iff (P.coe_componentPairing_root C)]
  exact ⟨fun h ↦ AddSubmonoid.closure_mono (Set.image_mono Set.inter_subset_left) h,
    fun h ↦ mem_closure_root_inter_supp h x.property⟩

/-- A vector of the coroot space of `C` is a sum of simple coroots of the component base exactly
when it is a sum of simple coroots of `b`. -/
theorem mem_closure_coroot_componentBase_iff {x : P.corootComponentSpace C} :
    x ∈ AddSubmonoid.closure ((P.componentPairing C).coroot '' (b.componentBase C).support) ↔
      (x : N) ∈ AddSubmonoid.closure (P.coroot '' b.support) := by
  rw [support_componentBase, Finset.coe_preimage,
    AddSubmonoid.mem_closure_image_preimage_val_iff (P.coe_componentPairing_coroot C)]
  exact ⟨fun h ↦ AddSubmonoid.closure_mono (Set.image_mono Set.inter_subset_left) h,
    fun h ↦ mem_closure_coroot_inter_supp h x.property⟩

/-- The heights of the roots of `C` relative to the component base are their heights relative to
`b`. -/
@[simp]
theorem height_componentBase [CharZero K] (i : C.supp) :
    (b.componentBase C).height i = b.height i := by
  classical
  obtain ⟨f, -, -, hf⟩ := (b.componentBase C).exists_root_eq_sum_int i
  let F : ι → ℤ := fun k ↦ if hk : k ∈ C.supp then f ⟨k, hk⟩ else 0
  have hF (k : ι) (hk : k ∉ Set.range ((↑) : C.supp → ι)) : F k = 0 :=
    dite_eq_right fun h ↦ hk ⟨⟨k, h⟩, rfl⟩
  have hFf (j : C.supp) : F j = f j := dite_eq_left j.property
  rw [height_eq_sum hf, b.height_eq_sum (f := F) ?_, support_componentBase]
  · rw [← Finset.sum_preimage _ _ Subtype.val_injective.injOn F fun k _ hk ↦ hF k hk]
    exact Finset.sum_congr rfl fun j _ ↦ (hFf j).symm
  · rw [← Finset.sum_preimage _ _ Subtype.val_injective.injOn (fun k ↦ F k • P.root k)
      fun k _ hk ↦ by rw [hF k hk, zero_smul]]
    simp_rw [hFf]
    simpa [support_componentBase] using congrArg Subtype.val hf

/-- A root of `C` is positive for the component base exactly when it is positive for `b`. -/
@[simp]
theorem isPos_componentBase_iff [CharZero K] (i : C.supp) :
    (b.componentBase C).IsPos i ↔ b.IsPos i := by
  rw [isPos_iff, isPos_iff, height_componentBase]

/-- The simple roots of the component base are the vertices of the corresponding component of the
Dynkin diagram of `b`. -/
noncomputable def supportComponentBaseEquiv [CharZero K] [P.IsCrystallographic] [P.IsReduced] :
    (b.componentBase C).support ≃ (b.componentEquiv.symm C).supp where
  toFun i := ⟨⟨i, (b.mem_support_componentBase C).mp i.property⟩,
    (b.mem_supp_componentEquiv_symm C).mpr i.val.property⟩
  invFun i := ⟨⟨i.val, (b.mem_supp_componentEquiv_symm C).mp i.property⟩,
    (b.mem_support_componentBase C).mpr i.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_supportComponentBaseEquiv_apply [CharZero K] [P.IsCrystallographic] [P.IsReduced]
    (i : (b.componentBase C).support) :
    (b.supportComponentBaseEquiv C i : b.support) =
      ⟨i, (b.mem_support_componentBase C).mp i.property⟩ := by
  simp [supportComponentBaseEquiv]

@[simp]
theorem coe_supportComponentBaseEquiv_symm_apply [CharZero K] [P.IsCrystallographic]
    [P.IsReduced] (i : (b.componentEquiv.symm C).supp) :
    ((b.supportComponentBaseEquiv C).symm i : C.supp) =
      ⟨(i : b.support), (b.mem_supp_componentEquiv_symm C).mp i.property⟩ := by
  simp [supportComponentBaseEquiv]

/-- The `S`-valued Cartan matrix of the component base is the block of the `S`-valued Cartan
matrix of `b` on the simple roots in `C`. -/
@[simp]
theorem cartanMatrixIn_componentBase (S : Type*) [CommRing S] [Algebra S K] [P.IsValuedIn S]
    (i j : (b.componentBase C).support) :
    (b.componentBase C).cartanMatrixIn S i j =
      b.cartanMatrixIn S ⟨i, (b.mem_support_componentBase C).mp i.property⟩
        ⟨j, (b.mem_support_componentBase C).mp j.property⟩ := by
  simp [cartanMatrixIn_def]

/-- The Cartan matrix of the component base is the block of the Cartan matrix of `b` on the simple
roots in `C`. -/
theorem cartanMatrix_componentBase [P.IsCrystallographic] (i j : (b.componentBase C).support) :
    (b.componentBase C).cartanMatrix i j =
      b.cartanMatrix ⟨i, (b.mem_support_componentBase C).mp i.property⟩
        ⟨j, (b.mem_support_componentBase C).mp j.property⟩ :=
  b.cartanMatrixIn_componentBase C ℤ i j

end ComponentPairing

end RootPairing.Base

namespace RootPairing

section ProjectionBase

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem]

private theorem toWeightBasis_repr_componentProj_aux (b : P.Base) (C : P.Component) (x : M)
    (i : b.support) :
    b.toWeightBasis.repr (P.componentProj C x : M) i =
      open Classical in if P.componentOf (i : ι) = C then b.toWeightBasis.repr x i else 0 := by
  classical
  conv_lhs => rw [← b.toWeightBasis.sum_repr x]
  simp only [b.toWeightBasis_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · by_cases hi : P.componentOf (i : ι) = C
    · rw [P.coe_componentProj_root_of_eq hi, ← b.toWeightBasis_apply]; simp [hi]
    · rw [P.componentProj_root_of_ne hi]; simp [hi]
  · intro j _ hji
    by_cases hj : P.componentOf (j : ι) = C
    · rw [P.coe_componentProj_root_of_eq hj, ← b.toWeightBasis_apply]
      simp [Finsupp.single_eq_of_ne (Ne.symm hji)]
    · rw [P.componentProj_root_of_ne hj]; simp
  · simp

/-- On a simple root in `C`, the simple-root coordinate of the `C`-projection equals the original
simple-root coordinate. -/
theorem toWeightBasis_repr_componentProj_of_eq (b : P.Base) {C : P.Component} {i : b.support}
    (hi : P.componentOf (i : ι) = C) (x : M) :
    b.toWeightBasis.repr (P.componentProj C x : M) i = b.toWeightBasis.repr x i := by
  rw [P.toWeightBasis_repr_componentProj_aux]; simp [hi]

/-- On a simple root outside `C`, the simple-root coordinate of the `C`-projection is zero. -/
theorem toWeightBasis_repr_componentProj_of_ne (b : P.Base) {C : P.Component} {i : b.support}
    (hi : P.componentOf (i : ι) ≠ C) (x : M) :
    b.toWeightBasis.repr (P.componentProj C x : M) i = 0 := by
  rw [P.toWeightBasis_repr_componentProj_aux]; simp [hi]

variable {P} in
/-- A vector in `P.componentSpace C` has zero coordinates along simple roots outside `C`. -/
theorem toWeightBasis_repr_eq_zero_of_mem_componentSpace (b : P.Base) {C : P.Component} {x : M}
    (hx : x ∈ P.componentSpace C) {i : b.support} (hi : P.componentOf (i : ι) ≠ C) :
    b.toWeightBasis.repr x i = 0 := by
  have hproj : (P.componentProj C x : M) = x :=
    congrArg Subtype.val (P.componentProj_apply_of_mem hx)
  rw [← hproj, P.toWeightBasis_repr_componentProj_of_ne b hi]

/-- Component projections preserve the positive root cone of any base. -/
theorem componentProj_mem_posRootCone (b : P.Base) (C : P.Component) {x : M}
    (hx : x ∈ TauCeti.posRootCone P b) : (P.componentProj C x : M) ∈ TauCeti.posRootCone P b := by
  obtain ⟨f, rfl⟩ := (TauCeti.mem_posRootCone P b).mp hx
  rw [map_sum, Submodule.coe_sum]
  refine AddSubmonoid.sum_mem _ fun j hj ↦ ?_
  rw [map_nsmul, Submodule.coe_smul_of_tower]
  by_cases hjC : P.componentOf j = C
  · rw [P.coe_componentProj_root_of_eq hjC]
    exact AddSubmonoid.nsmul_mem _ (TauCeti.root_mem_posRootCone_of_mem_support P b hj) _
  · simp [P.componentProj_root_of_ne hjC]

end ProjectionBase

namespace Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] (b : P.Base)

/-- The simple roots of `b` lying in `C` form an `R`-basis of `P.componentSpace C`. -/
noncomputable def componentWeightBasis (C : P.Component) :
    Module.Basis {i : b.support // P.componentOf (i : ι) = C} R (P.componentSpace C) :=
  b.toWeightBasis.restrict {i : b.support | P.componentOf (i : ι) = C} (P.componentSpace C)
    (fun i hi ↦ by
      rw [b.toWeightBasis_apply]
      exact P.root_mem_componentSpace_of_mem_supp ((C.mem_supp_iff _).mpr hi))
    (fun hx hi ↦ P.toWeightBasis_repr_eq_zero_of_mem_componentSpace b hx hi)

/-- The coordinates of a vector in `b.componentWeightBasis C` are its `b.toWeightBasis`
coordinates at the simple roots in `C`. -/
@[simp] theorem componentWeightBasis_repr_apply (C : P.Component) (x : P.componentSpace C)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentWeightBasis C).repr x i = b.toWeightBasis.repr (x : M) i.val := by
  rw [componentWeightBasis, Module.Basis.restrict_repr]

/-- The basis vectors of `b.componentWeightBasis C` are the simple roots of `b` in `C`. -/
@[simp] theorem coe_componentWeightBasis_apply (C : P.Component)
    (i : {i : b.support // P.componentOf (i : ι) = C}) :
    (b.componentWeightBasis C i : M) = P.root (i.val : ι) := by
  rw [componentWeightBasis, Module.Basis.coe_restrict, b.toWeightBasis_apply]

end Base

section CrystallographicBase

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  (e : P.Equiv Q) {b : P.Base} {b' : Q.Base}
  (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support)
  [CharZero R] [P.IsCrystallographic] [Q.IsCrystallographic]

/-- The Dynkin-diagram isomorphism induced by a base-preserving equivalence. -/
def Equiv.diagramGraphIso : diagramGraph b.cartanMatrix ≃g diagramGraph b'.cartanMatrix where
  toEquiv := e.supportEquiv hb
  map_rel_iff' {i j} := by
    simp only [diagramGraph_adj, ne_eq, (e.supportEquiv hb).apply_eq_iff_eq,
      e.cartanMatrix_supportEquiv hb]

/-- `Equiv.diagramGraphIso` evaluates via `Equiv.supportEquiv`. -/
@[simp] theorem Equiv.diagramGraphIso_apply (i : b.support) :
    e.diagramGraphIso hb i = e.supportEquiv hb i := (rfl)

/-- **For a base-preserving equivalence, `componentEquiv` agrees with `diagramGraphIso`.** -/
theorem Equiv.componentEquiv_base_componentEquiv [IsDomain R] [Finite ι] [Finite ι₂]
    [P.IsReduced] [Q.IsReduced] (K : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    e.componentEquiv (b.componentEquiv K) =
      b'.componentEquiv ((e.diagramGraphIso hb).connectedComponentEquiv K) :=
  K.ind fun _ ↦ by simp

end CrystallographicBase

section EquivComponentBase

variable {ι ι₂ K M N M₂ N₂ : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} {Q : RootPairing ι₂ K M₂ N₂}
  [Finite ι] [Finite ι₂] [P.IsRootSystem] [Q.IsRootSystem]

/-- A base-preserving equivalence carries the simple roots of `b.componentBase C` onto the simple
roots of `b'.componentBase (e.componentEquiv C)`. -/
theorem Equiv.mem_support_componentPairingEquiv_indexEquiv_iff (e : P.Equiv Q) {b : P.Base}
    {b' : Q.Base} (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support) (C : P.Component)
    (i : C.supp) :
    (e.componentPairingEquiv C).indexEquiv i ∈ (b'.componentBase (e.componentEquiv C)).support ↔
      i ∈ (b.componentBase C).support := by
  simp [hb]

/-- A base-preserving automorphism fixing `C` permutes the simple roots of `b.componentBase C`. -/
theorem Equiv.mem_support_restrictComponentAut_indexEquiv_iff {τ : P.Aut} {b : P.Base}
    (hb : ∀ i, i ∈ b.support ↔ τ.indexEquiv i ∈ b.support) {C : P.Component}
    (hC : τ.componentEquiv C = C) (i : C.supp) :
    (τ.restrictComponentAut C hC).indexEquiv i ∈ (b.componentBase C).support ↔
      i ∈ (b.componentBase C).support := by
  have htransport {D : P.Component} (h : D = C) (j : D.supp) (k : C.supp)
      (hjk : (k : ι) = (j : ι)) :
      k ∈ (b.componentBase C).support ↔ j ∈ (b.componentBase D).support := by
    subst h
    obtain rfl : k = j := Subtype.ext hjk
    rfl
  rw [htransport hC ((τ.componentPairingEquiv C).indexEquiv i)
    ((τ.restrictComponentAut C hC).indexEquiv i) (by simp)]
  exact τ.mem_support_componentPairingEquiv_indexEquiv_iff hb C i

end EquivComponentBase

end RootPairing
