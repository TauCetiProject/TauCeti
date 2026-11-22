/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Exhaustive, separated and complete filtrations

For a filtered object `F` of `C` indexed by a category `I` (Mathlib's
`CategoryTheory.FilteredObject C I`), this file records the steps of the filtration as subobjects
of the underlying object `X`, and the three conditions under which a filtration determines its
object from its steps:

* `CategoryTheory.FilteredObject.step F i`: the step `F_i`, as a subobject of `X`;
* `CategoryTheory.FilteredObject.IsExhaustive F`: `⊤` is the least upper bound of the steps;
* `CategoryTheory.FilteredObject.IsSeparated F`: `⊥` is the greatest lower bound of the steps;
* `CategoryTheory.FilteredObject.IsComplete F`: `X` is the limit of the quotients `X / F_i`,
  through the cone `CategoryTheory.FilteredObject.quotientCone F` of the projections.

For a decreasing filtration indexed by `ℤᵒᵖ` the quotients `X / F^p` form an inverse system as
`p → ∞`, and completeness is the usual completeness of the filtration topology. Completeness
implies separatedness (`CategoryTheory.FilteredObject.IsComplete.isSeparated`). A morphism of
filtered objects is an isomorphism exactly when it is one on the underlying objects and on every
step (`CategoryTheory.FilteredObject.isIso_iff`).

## References

* [Stacks, Homological algebra, Definition 19.1, Tag 0121][stacks-project]
* J. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, 2024, Definition 2.5
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.FilteredObject

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

/-- A morphism of filtered objects is an isomorphism if and only if it is an isomorphism on the
underlying objects and on every step of the filtrations. -/
lemma isIso_iff {F G : FilteredObject C I} (f : F ⟶ G) :
    IsIso f ↔ IsIso f.hom ∧ ∀ i, IsIso (f.natTrans.app i) := by
  refine ⟨fun _ ↦ ⟨inferInstanceAs (IsIso (forget.map f)),
    fun i ↦ ⟨(inv f).natTrans.app i, ?_, ?_⟩⟩, fun ⟨_, _⟩ ↦ ?_⟩
  · rw [← NatTrans.comp_app, ← comp_natTrans, IsIso.hom_inv_id, id_natTrans, NatTrans.id_app]
  · rw [← NatTrans.comp_app, ← comp_natTrans, IsIso.inv_hom_id, id_natTrans, NatTrans.id_app]
  · exact (isoMk (asIso f.hom) (fun i ↦ asIso (f.natTrans.app i))).isIso_hom

variable (F : FilteredObject C I)

/-- The inclusion `F_i ⟶ X` of the step `F_i` of a filtration into the underlying object. -/
noncomputable def stepι (i : I) : F.filtration.obj i ⟶ F.X :=
  F.filtration.ι.app i

/-- `CategoryTheory.FilteredObject.stepι` is Mathlib's inclusion `F.filtration.ι.app i`, with
codomain `F.X` rather than `((Functor.const I).obj F.X).obj i`. -/
lemma filtration_ι_app (i : I) : F.filtration.ι.app i = F.stepι i := (rfl)

instance (i : I) : Mono (F.stepι i) :=
  inferInstanceAs (Mono (F.filtration.ι.app i))

/-- The inclusion `F_i ⟶ F_j` of steps of a filtration given by a morphism `i ⟶ j` of the index
category. -/
noncomputable def stepMap {i j : I} (f : i ⟶ j) : F.filtration.obj i ⟶ F.filtration.obj j :=
  F.filtrationDiagram.map f

@[simp]
lemma stepMap_id (i : I) : F.stepMap (𝟙 i) = 𝟙 _ :=
  F.filtrationDiagram.map_id i

@[reassoc]
lemma stepMap_comp {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    F.stepMap (f ≫ g) = F.stepMap f ≫ F.stepMap g :=
  F.filtrationDiagram.map_comp f g

@[reassoc (attr := simp)]
lemma stepMap_stepι {i j : I} (f : i ⟶ j) : F.stepMap f ≫ F.stepι j = F.stepι i :=
  (F.filtration.ι.naturality f).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma Hom.natTrans_app_stepι {F G : FilteredObject C I} (f : F ⟶ G) (i : I) :
    f.natTrans.app i ≫ G.stepι i = F.stepι i ≫ f.hom :=
  f.comm i

@[reassoc]
lemma Hom.stepMap_natTrans_app {F G : FilteredObject C I} (φ : F ⟶ G) {i j : I} (f : i ⟶ j) :
    F.stepMap f ≫ φ.natTrans.app j = φ.natTrans.app i ≫ G.stepMap f :=
  φ.natTrans.naturality f

/-- The step `F_i` of a filtration, as a subobject of the underlying object. -/
noncomputable def step (i : I) : Subobject F.X :=
  Subobject.mk (F.stepι i)

/-- A morphism `i ⟶ j` of the index category includes the step `F_i` in the step `F_j`. -/
lemma step_le_step_of_hom {i j : I} (f : i ⟶ j) : F.step i ≤ F.step j :=
  Subobject.mk_le_mk_of_comm (F.stepMap f) (F.stepMap_stepι f)

/-- A step is everything exactly when its inclusion is an isomorphism. -/
lemma step_eq_top_iff (i : I) : F.step i = ⊤ ↔ IsIso (F.stepι i) :=
  (Subobject.isIso_iff_mk_eq_top _).symm

/-- A step is zero exactly when it is a zero object. -/
lemma step_eq_bot_iff [HasZeroMorphisms C] [HasZeroObject C] (i : I) :
    F.step i = ⊥ ↔ IsZero (F.filtration.obj i) := by
  rw [step, Subobject.mk_eq_bot_iff_zero, IsZero.iff_id_eq_zero, ← cancel_mono (F.stepι i)]
  simp

/-- A morphism of filtered objects is an isomorphism on a step that is zero on both sides. -/
lemma isIso_natTrans_app_of_step_eq_bot [HasZeroMorphisms C] [HasZeroObject C]
    {F G : FilteredObject C I} (φ : F ⟶ G) {i : I} (hF : F.step i = ⊥) (hG : G.step i = ⊥) :
    IsIso (φ.natTrans.app i) :=
  isIso_of_source_target_iso_zero _ ((F.step_eq_bot_iff i).1 hF).isoZero
    ((G.step_eq_bot_iff i).1 hG).isoZero

/-- A filtration is *exhaustive* when the whole object is the least upper bound of its steps. -/
def IsExhaustive : Prop :=
  IsLUB (Set.range F.step) ⊤

/-- A filtration is exhaustive exactly when every subobject containing all of its steps is
everything. -/
lemma isExhaustive_iff : F.IsExhaustive ↔ ∀ S : Subobject F.X, (∀ i, F.step i ≤ S) → S = ⊤ := by
  simp [IsExhaustive, IsLUB, IsLeast, upperBounds, lowerBounds, top_le_iff]

/-- A filtration is *separated* when the zero subobject is the greatest lower bound of its
steps. -/
def IsSeparated [HasZeroObject C] : Prop :=
  IsGLB (Set.range F.step) ⊥

/-- A filtration is separated exactly when every subobject contained in all of its steps is
zero. -/
lemma isSeparated_iff [HasZeroObject C] :
    F.IsSeparated ↔ ∀ S : Subobject F.X, (∀ i, S ≤ F.step i) → S = ⊥ := by
  simp [IsSeparated, IsGLB, IsGreatest, upperBounds, lowerBounds, le_bot_iff]

/-- A filtration with a step equal to the whole object is exhaustive. -/
lemma isExhaustive_of_step_eq_top {i : I} (hi : F.step i = ⊤) : F.IsExhaustive :=
  ⟨fun _ _ ↦ le_top, fun _ hS ↦ hi ▸ hS ⟨i, rfl⟩⟩

/-- A filtration with a zero step is separated. -/
lemma isSeparated_of_step_eq_bot [HasZeroObject C] {i : I}
    (hi : F.step i = ⊥) : F.IsSeparated :=
  ⟨fun _ _ ↦ bot_le, fun _ hS ↦ hi ▸ hS ⟨i, rfl⟩⟩

section Complete

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The system of quotients `X / F_i` of the underlying object `X` by the steps of the
filtration, with the maps induced by the inclusions of steps. -/
@[expose, simps]
noncomputable def quotientDiagram : I ⥤ C where
  obj i := cokernel (F.stepι i)
  map f := cokernel.map _ _ (F.stepMap f) (𝟙 F.X) (by simp)
  map_id i := by ext; simp
  map_comp f g := by ext; simp

@[reassoc]
lemma cokernel_π_quotientDiagram_map {i j : I} (f : i ⟶ j) :
    cokernel.π (F.stepι i) ≫ F.quotientDiagram.map f = cokernel.π (F.stepι j) := by
  simp [quotientDiagram]

/-- The cone of the projections `X ⟶ X / F_i` over the system of quotients. -/
@[expose, simps]
noncomputable def quotientCone : Cone F.quotientDiagram where
  pt := F.X
  π :=
    { app i := cokernel.π _
      naturality _ _ f := by simp [quotientDiagram] }

/-- A filtration is *complete* when the underlying object is the limit of its quotients by the
steps, through the projections. -/
def IsComplete : Prop :=
  Nonempty (IsLimit F.quotientCone)

/-- Morphisms into the underlying object of a complete filtration are determined by their
composites with the projections onto the quotients by the steps. -/
lemma IsComplete.hom_ext {F : FilteredObject C I} (hF : F.IsComplete) {W : C} {g g' : W ⟶ F.X}
    (h : ∀ i, g ≫ cokernel.π (F.stepι i) = g' ≫ cokernel.π (F.stepι i)) : g = g' :=
  hF.some.hom_ext h

/-- A morphism into the underlying object vanishes in the quotient by a step through which it
factors. -/
lemma arrow_comp_cokernel_π_eq_zero {S : Subobject F.X} {i : I} (h : S ≤ F.step i) :
    S.arrow ≫ cokernel.π (F.stepι i) = 0 := by
  rw [← Subobject.ofLEMk_comp (f := F.stepι i) h, Category.assoc, cokernel.condition, comp_zero]

/-- A complete filtration is separated: a subobject contained in every step maps to zero in
every quotient, hence is zero. -/
lemma IsComplete.isSeparated [HasZeroObject C] {F : FilteredObject C I} (hF : F.IsComplete) :
    F.IsSeparated := by
  refine (F.isSeparated_iff).2 fun S hS ↦ ?_
  rw [← Subobject.mk_arrow S, Subobject.mk_eq_bot_iff_zero]
  exact hF.hom_ext fun i ↦ by rw [F.arrow_comp_cokernel_π_eq_zero (hS i), zero_comp]

/-- The projection onto the quotient by a zero step is an isomorphism. -/
lemma isIso_cokernel_π_stepι_of_step_eq_bot [HasZeroObject C] {i : I} (hi : F.step i = ⊥) :
    IsIso (cokernel.π (F.stepι i)) := by
  rw [step, Subobject.mk_eq_bot_iff_zero] at hi
  rw [hi]
  infer_instance

/-- A filtration indexed by a cofiltered category with a zero step is complete: from that step
on, the system of quotients is constant with value the underlying object. -/
lemma isComplete_of_step_eq_bot [HasZeroObject C] [IsCofiltered I] {i₀ : I}
    (hi₀ : F.step i₀ = ⊥) : F.IsComplete := by
  have hiso : ∀ ⦃j : I⦄, (j ⟶ i₀) → IsIso (cokernel.π (F.stepι j)) := fun j f ↦
    F.isIso_cokernel_π_stepι_of_step_eq_bot (le_bot_iff.1 (hi₀ ▸ F.step_le_step_of_hom f))
  have h : F.quotientDiagram.IsEventuallyConstantTo i₀ := fun j f ↦ by
    have := hiso f
    have := hiso (𝟙 i₀)
    have : IsIso (cokernel.π (F.stepι j) ≫ F.quotientDiagram.map f) := by
      rw [cokernel_π_quotientDiagram_map]
      exact this
    exact IsIso.of_isIso_comp_left (cokernel.π (F.stepι j)) _
  have : IsIso (F.quotientCone.π.app i₀) := by
    rw [quotientCone_π_app]
    exact hiso (𝟙 i₀)
  exact ⟨h.isLimitOfIsIso _⟩

end Complete

end CategoryTheory.FilteredObject
