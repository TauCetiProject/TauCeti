/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Filtration.Quotients
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Completeness of filtrations

A filtration is exhaustive if its steps have join `⊤`, separated if they have meet `⊥`,
and complete if the underlying object is the limit of the quotients by its steps. These
conditions are stated without assuming arbitrary joins, meets, or limits exist. A complete
filtration is separated, and a finite decreasing filtration is exhaustive, separated and complete.

See [Stacks, Tag 0121](https://stacks.math.columbia.edu/tag/0121) for exhaustiveness and
separation. Completeness here refers to the limit of the quotients, not merely to vanishing
of a derived inverse limit of the steps.
-/

public section

noncomputable section

namespace CategoryTheory.FilteredObject

open Limits

variable {C I : Type*} [Category* C] [Category* I]

/-- A filtration step as a subobject of the underlying object. -/
def step (F : FilteredObject C I) (i : I) : Subobject F.X := Subobject.mk (F.filtration.ι.app i)

lemma step_eq_mk (F : FilteredObject C I) (i : I) :
    F.step i = Subobject.mk (F.filtration.ι.app i) := (rfl)

/-- A filtration transition exhibits its source step as a subobject of its target step. -/
lemma step_le_of_hom (F : FilteredObject C I) {i j : I} (f : i ⟶ j) : F.step i ≤ F.step j :=
  Subobject.mk_le_mk_of_comm (F.filtrationDiagram.map f) (by
    simpa using F.filtration.ι.naturality f)

/-- The subobjects of a filtration indexed by a preorder increase in that preorder. -/
lemma monotone_step {J : Type*} [Preorder J] (F : FilteredObject C J) : Monotone F.step :=
  fun _ _ h ↦ F.step_le_of_hom (homOfLE h)

/-- The inclusion of a step is an isomorphism exactly when the step is the whole object. -/
lemma isIso_ι_app_iff (F : FilteredObject C I) (i : I) :
    IsIso (F.filtration.ι.app i) ↔ F.step i = ⊤ := by
  rw [step_eq_mk, Subobject.isIso_iff_mk_eq_top]

/-- A step is the bottom subobject exactly when its inclusion is zero. -/
lemma step_eq_bot_iff [HasZeroObject C] [HasZeroMorphisms C] (F : FilteredObject C I) (i : I) :
    F.step i = ⊥ ↔ F.filtration.ι.app i = 0 := by
  rw [step_eq_mk, Subobject.mk_eq_bot_iff_zero]

section Complete

variable [HasZeroMorphisms C] [HasCokernels C]

/-- A filtration is complete if the canonical cone over the quotients by its steps is a limit. -/
def IsComplete (F : FilteredObject C I) : Prop := Nonempty (IsLimit F.quotientCone)

lemma isComplete_iff (F : FilteredObject C I) : F.IsComplete ↔ Nonempty (IsLimit F.quotientCone) :=
  Iff.rfl

/-- If a filtration reaches a zero step in a cofiltered diagram, it is complete: the quotient
projections at that index and all indices mapping to it are isomorphisms. -/
lemma isComplete_of_ι_eq_zero [IsCofilteredOrEmpty I] (F : FilteredObject C I) {i : I}
    (hi : F.filtration.ι.app i = 0) : F.IsComplete := by
  have : IsCofiltered I := { nonempty := ⟨i⟩ }
  have isoπ (j : I) (hj : F.filtration.ι.app j = 0) : IsIso (F.quotientπ.app j) := by
    let h := CokernelCofork.IsColimit.ofId (F.filtration.ι.app j) hj
    let e := h.coconePointUniqueUpToIso (F.quotientπIsCokernel j)
    have he : 𝟙 F.X ≫ e.hom = F.quotientπ.app j :=
      h.comp_coconePointUniqueUpToIso_hom (F.quotientπIsCokernel j) WalkingParallelPair.one
    rw [← he, Category.id_comp]
    infer_instance
  have : IsIso (F.quotientπ.app i) := isoπ i hi
  have h : F.quotientDiagram.IsEventuallyConstantTo i := by
    intro j f
    have := isoπ j (by simpa [hi] using (F.filtration.ι.naturality f).symm)
    exact IsIso.of_isIso_fac_left (F.π_quotientDiagram_map f)
  exact ⟨h.isLimitOfIsIso F.quotientCone⟩

end Complete

/-- A filtration is exhaustive if the top subobject is the join of its steps. -/
def IsExhaustive (F : FilteredObject C I) : Prop := IsLUB (Set.range F.step) ⊤

lemma isExhaustive_iff (F : FilteredObject C I) : F.IsExhaustive ↔ IsLUB (Set.range F.step) ⊤ :=
  Iff.rfl

/-- A filtration with a step equal to the entire object is exhaustive. -/
lemma isExhaustive_of_step_eq_top {F : FilteredObject C I} {i : I} (hi : F.step i = ⊤) :
    F.IsExhaustive := ⟨fun _ _ ↦ le_top, fun _ h ↦ hi ▸ h (Set.mem_range_self i)⟩

/-- A filtration is separated if the bottom subobject is the meet of its steps. -/
def IsSeparated [HasZeroObject C] (F : FilteredObject C I) : Prop := IsGLB (Set.range F.step) ⊥

lemma isSeparated_iff [HasZeroObject C] (F : FilteredObject C I) :
    F.IsSeparated ↔ IsGLB (Set.range F.step) ⊥ := Iff.rfl

/-- A filtration with a zero step is separated. -/
lemma isSeparated_of_step_eq_bot [HasZeroObject C] {F : FilteredObject C I} {i : I}
    (hi : F.step i = ⊥) : F.IsSeparated :=
  ⟨fun _ _ ↦ bot_le, fun _ h ↦ hi ▸ h (Set.mem_range_self i)⟩

/-- Completeness implies separation: a subobject contained in every step is annihilated by
every quotient projection, hence is zero by the limit property. -/
lemma IsComplete.isSeparated [HasZeroObject C] [HasZeroMorphisms C] [HasCokernels C]
    {F : FilteredObject C I} (h : F.IsComplete) :
    F.IsSeparated := by
  obtain ⟨hc⟩ := (F.isComplete_iff).1 h
  refine ⟨fun _ _ ↦ bot_le, fun S hS ↦ ?_⟩
  have hle (i : I) : S ≤ Subobject.mk (F.filtration.ι.app i) :=
    (hS (Set.mem_range_self i)).trans_eq (F.step_eq_mk i)
  have hzero : S.arrow = 0 := by
    apply hc.hom_ext
    intro i
    rw [← Subobject.ofLEMk_comp (hle i), Category.assoc]
    simp
  exact (Subobject.mk_arrow S).symm.trans (Subobject.mk_eq_bot_iff_zero.2 hzero) |>.le

section Finite

variable [HasZeroObject C]

/-- A decreasing filtration is finite if it reaches the whole object at some index `a`
and zero at some index `b ≥ a`. -/
def IsFinite (F : FilteredObject C ℤᵒᵖ) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ F.step (Opposite.op a) = ⊤ ∧ F.step (Opposite.op b) = ⊥

lemma isFinite_iff (F : FilteredObject C ℤᵒᵖ) : F.IsFinite ↔
    ∃ a b : ℤ, a ≤ b ∧ F.step (Opposite.op a) = ⊤ ∧ F.step (Opposite.op b) = ⊥ := Iff.rfl

/-- Finite decreasing filtrations are exhaustive. -/
lemma IsFinite.isExhaustive {F : FilteredObject C ℤᵒᵖ} (h : F.IsFinite) : F.IsExhaustive := by
  obtain ⟨_, _, _, ha, _⟩ := (F.isFinite_iff).1 h
  exact isExhaustive_of_step_eq_top ha

/-- Finite decreasing filtrations are separated. -/
lemma IsFinite.isSeparated {F : FilteredObject C ℤᵒᵖ} (h : F.IsFinite) : F.IsSeparated := by
  obtain ⟨_, _, _, _, hb⟩ := (F.isFinite_iff).1 h
  exact isSeparated_of_step_eq_bot hb

/-- Finite decreasing filtrations are complete. -/
lemma IsFinite.isComplete [HasZeroMorphisms C] [HasCokernels C] {F : FilteredObject C ℤᵒᵖ}
    (h : F.IsFinite) : F.IsComplete := by
  obtain ⟨_, b, _, _, hb⟩ := (F.isFinite_iff).1 h
  exact F.isComplete_of_ι_eq_zero ((F.step_eq_bot_iff (Opposite.op b)).1 hb)

end Finite

end CategoryTheory.FilteredObject
