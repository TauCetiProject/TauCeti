/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Filtration.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Graded pieces of decreasing filtrations

A decreasingly filtered object of `C` is a Mathlib `CategoryTheory.FilteredObject C ℤᵒᵖ`: its
steps `F^p` decrease, `F^{p+1} ⊆ F^p`. This file defines its graded pieces
`gr^p = F^p / F^{p+1}` and finite filtrations, and proves that the graded pieces detect
isomorphisms between finitely filtered objects.

## Main definitions

* `CategoryTheory.FilteredObject.grShortComplex p`: the functor sending a filtered object to the
  short complex `F^{p+1} ⟶ F^p ⟶ gr^p`, short exact in an abelian category
  (`CategoryTheory.FilteredObject.shortExact_grShortComplex`).
* `CategoryTheory.FilteredObject.gr p`: the graded piece `gr^p`, as a functor from decreasingly
  filtered objects to `C`.
* `CategoryTheory.FilteredObject.IsFinite`: the filtration is finite, `F^a = X` and `F^b = 0` for
  some integers `a` and `b`.

## Main results

* `CategoryTheory.FilteredObject.IsFinite.isExhaustive`, `IsFinite.isSeparated` and
  `IsFinite.isComplete`: a finite filtration is exhaustive, separated and complete.
* `CategoryTheory.FilteredObject.isIso_natTrans_app_of_isIso_gr`: a morphism of filtered objects
  that is an isomorphism on the graded pieces in degrees `p ≤ q < b`, between filtrations with
  zero step `F^b`, is an isomorphism on the step `F^p`.
* `CategoryTheory.FilteredObject.isIso_of_isIso_gr`: a morphism of finitely filtered objects that
  is an isomorphism on every graded piece is an isomorphism of filtered objects.

## References

* [Stacks, Homological algebra, Definition 19.1, Tag 0121][stacks-project]
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.FilteredObject

variable {C : Type*} [Category* C]

/-- The steps of a decreasing filtration decrease. -/
lemma step_antitone (F : FilteredObject C ℤᵒᵖ) : Antitone fun p : ℤ ↦ F.step (op p) :=
  fun _ _ h ↦ F.step_le_step_of_hom (homOfLE h).op

/-- In a decreasing filtration, every step after a zero step is zero. -/
lemma step_eq_bot_of_le [HasZeroObject C] (F : FilteredObject C ℤᵒᵖ) {p q : ℤ} (hpq : p ≤ q)
    (h : F.step (op p) = ⊥) : F.step (op q) = ⊥ :=
  F.step_eq_bot_of_hom (homOfLE hpq).op h

/-- In a decreasing filtration, every step before a step equal to the whole object is the whole
object. -/
lemma step_eq_top_of_le (F : FilteredObject C ℤᵒᵖ) {p q : ℤ} (hpq : p ≤ q)
    (h : F.step (op q) = ⊤) : F.step (op p) = ⊤ :=
  F.step_eq_top_of_hom (homOfLE hpq).op h

section GradedPiece

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The short complex `F^{p+1} ⟶ F^p ⟶ gr^p` of a decreasingly filtered object, whose first map
is the inclusion of steps and whose second map is the projection onto its cokernel, the graded
piece `gr^p`, as a functor of the filtered object. -/
@[expose, simps]
noncomputable def grShortComplex (p : ℤ) : FilteredObject C ℤᵒᵖ ⥤ ShortComplex C where
  obj F := ShortComplex.mk (F.stepMap (homOfLE (Int.le_add_one le_rfl)).op) (cokernel.π _)
    (cokernel.condition _)
  map φ :=
    { τ₁ := φ.natTrans.app (op (p + 1))
      τ₂ := φ.natTrans.app (op p)
      τ₃ := cokernel.map _ _ _ _ (Hom.stepMap_natTrans_app φ _).symm
      comm₁₂ := (Hom.stepMap_natTrans_app φ _).symm }

/-- The graded piece `gr^p = F^p / F^{p+1}` of a decreasingly filtered object, as a functor. -/
@[expose, simps!]
noncomputable def gr (p : ℤ) : FilteredObject C ℤᵒᵖ ⥤ C :=
  grShortComplex p ⋙ ShortComplex.π₃

end GradedPiece

section Finite

variable [HasZeroObject C] (F : FilteredObject C ℤᵒᵖ)

/-- A decreasing filtration is *finite* when some step `F^a` is the whole object and some step
`F^b` is zero. No order between `a` and `b` is imposed: if `b < a`, the object is zero, and then
any pair, in particular one with `a ≤ b`, witnesses finiteness. -/
def IsFinite : Prop :=
  ∃ a b : ℤ, F.step (op a) = ⊤ ∧ F.step (op b) = ⊥

/-- A filtration is finite exactly when some step is the whole object and some step is zero. -/
lemma isFinite_iff : F.IsFinite ↔ ∃ a b : ℤ, F.step (op a) = ⊤ ∧ F.step (op b) = ⊥ := Iff.rfl

variable {F}

/-- A filtration with a step equal to the whole object and a zero step is finite. -/
lemma IsFinite.mk {a b : ℤ} (ha : F.step (op a) = ⊤) (hb : F.step (op b) = ⊥) : F.IsFinite :=
  ⟨a, b, ha, hb⟩

/-- A finite filtration is exhaustive. -/
lemma IsFinite.isExhaustive (hF : F.IsFinite) : F.IsExhaustive :=
  have ⟨_, _, ha, _⟩ := hF
  F.isExhaustive_of_step_eq_top ha

/-- A finite filtration is separated. -/
lemma IsFinite.isSeparated (hF : F.IsFinite) : F.IsSeparated :=
  have ⟨_, _, _, hb⟩ := hF
  F.isSeparated_of_step_eq_bot hb

/-- A finite filtration is complete. -/
lemma IsFinite.isComplete [HasZeroMorphisms C] [HasCokernels C] (hF : F.IsFinite) : F.IsComplete :=
  have ⟨_, _, _, hb⟩ := hF
  F.isComplete_of_step_eq_bot hb

end Finite

section Abelian

variable [Abelian C]

/-- The short complex `0 ⟶ F^{p+1} ⟶ F^p ⟶ gr^p ⟶ 0` is short exact. -/
lemma shortExact_grShortComplex (F : FilteredObject C ℤᵒᵖ) (p : ℤ) :
    ((grShortComplex p).obj F).ShortExact :=
  -- the first map of `grShortComplex p`, the inclusion `F^{p+1} ⟶ F^p`, verbatim
  let f := F.stepMap (homOfLE (Int.le_add_one le_rfl)).op
  have : Mono f := mono_of_mono_fac (F.stepMap_stepι _)
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
    mono_f := this
    epi_g := inferInstanceAs (Epi (cokernel.π f)) }

variable {F G : FilteredObject C ℤᵒᵖ} (φ : F ⟶ G)

/-- **Five lemma for one step.** If a morphism of filtered objects is an isomorphism on the steps
`F^{p+1}` and on the graded pieces `gr^p`, it is an isomorphism on the steps `F^p`. -/
lemma isIso_natTrans_app_of_isIso_succ (p : ℤ) [IsIso (φ.natTrans.app (op (p + 1)))]
    [IsIso ((gr p).map φ)] : IsIso (φ.natTrans.app (op p)) :=
  ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' ((grShortComplex p).map φ)
    (F.shortExact_grShortComplex p) (G.shortExact_grShortComplex p) ‹_› ‹_›

/-- **Five-lemma induction.** Let `F^b` and `G^b` be zero. A morphism of filtered objects that is
an isomorphism on the graded pieces `gr^q` for `p ≤ q < b` is an isomorphism on the steps
`F^p`. -/
lemma isIso_natTrans_app_of_isIso_gr {b : ℤ} (hF : F.step (op b) = ⊥) (hG : G.step (op b) = ⊥)
    {p : ℤ} (h : ∀ q, p ≤ q → q < b → IsIso ((gr q).map φ)) : IsIso (φ.natTrans.app (op p)) := by
  obtain hbp | hpb := le_or_gt b p
  · exact isIso_natTrans_app_of_step_eq_bot φ (F.step_eq_bot_of_le hbp hF)
      (G.step_eq_bot_of_le hbp hG)
  -- descending induction on `p`, from `p = b` where both steps are zero
  replace hpb := hpb.le
  induction p, hpb using Int.leInductionDown with
  | base => exact isIso_natTrans_app_of_step_eq_bot φ hF hG
  | pred q hqb ih =>
    have : IsIso (φ.natTrans.app (op (q - 1 + 1))) := by
      rw [sub_add_cancel]
      exact ih fun r hr hrb ↦ h r (by lia) hrb
    have : IsIso ((gr (q - 1)).map φ) := h _ le_rfl (by lia)
    exact isIso_natTrans_app_of_isIso_succ φ (q - 1)

/-- **Graded pieces detect isomorphisms of finite filtrations.** A morphism of finitely filtered
objects that is an isomorphism on every graded piece is an isomorphism of filtered objects: on the
underlying objects and on every step. -/
lemma isIso_of_isIso_gr (hF : F.IsFinite) (hG : G.IsFinite) (h : ∀ p, IsIso ((gr p).map φ)) :
    IsIso φ := by
  obtain ⟨a₁, b₁, ha₁, hb₁⟩ := hF
  obtain ⟨a₂, b₂, ha₂, hb₂⟩ := hG
  have hstep (p : ℤ) : IsIso (φ.natTrans.app (op p)) :=
    isIso_natTrans_app_of_isIso_gr φ (b := max b₁ b₂)
      (F.step_eq_bot_of_le (le_max_left _ _) hb₁) (G.step_eq_bot_of_le (le_max_right _ _) hb₂)
      fun q _ _ ↦ h q
  refine (isIso_iff φ).2 ⟨?_, fun i ↦ hstep i.unop⟩
  -- on the underlying objects, compare through the steps `F^a = X` and `G^a = X`
  have : IsIso (F.stepι (op (min a₁ a₂))) :=
    (F.step_eq_top_iff _).1 (F.step_eq_top_of_le (min_le_left _ _) ha₁)
  have : IsIso (G.stepι (op (min a₁ a₂))) :=
    (G.step_eq_top_iff _).1 (G.step_eq_top_of_le (min_le_right _ _) ha₂)
  have : IsIso (F.stepι (op (min a₁ a₂)) ≫ φ.hom) := by
    rw [← Hom.natTrans_app_stepι]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.stepι (op (min a₁ a₂))) φ.hom

end Abelian

end CategoryTheory.FilteredObject
