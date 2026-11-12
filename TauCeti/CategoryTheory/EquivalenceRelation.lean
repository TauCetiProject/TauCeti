/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Internal equivalence relations through their points

A pair of parallel morphisms `p₁ p₂ : R ⟶ X` admitting a pullback of `p₂` and `p₁` is an internal
equivalence relation (`CategoryTheory.IsEquivalenceRelation`) exactly when it is jointly monic
and, for every object `T`, the relation on `T ⟶ X` relating `r ≫ p₁` to `r ≫ p₂` for `r : T ⟶ R`
is an equivalence relation (Stacks, Definition 39.3.1 (022P), for schemes).

## Main results

* `TauCeti.CategoryTheory.Rel.ofPairHom p₁ p₂ T`: the relation on `T ⟶ X` given by `p₁` and `p₂`,
  characterized by `TauCeti.CategoryTheory.Rel.ofPairHom_iff`.
* `CategoryTheory.EquivalenceRelation.equivalence_ofPairHom`: an internal equivalence relation
  induces an equivalence relation on `T ⟶ X` for every `T`.
* `TauCeti.CategoryTheory.isEquivalenceRelation_iff`: if the pullback of `p₂` and `p₁` exists,
  then `p₁, p₂` is an internal equivalence relation if and only if it is jointly monic and
  `Rel.ofPairHom p₁ p₂ T` is an equivalence for every `T`.
* `CategoryTheory.IsEquivalenceRelation.refl`, `.symm`, `.trans`: chosen reflexivity, symmetry
  and transitivity morphisms of an internal equivalence relation, with their laws.
* `CategoryTheory.IsEquivalenceRelation.swap`: exchanging the projections of an internal
  equivalence relation gives an internal equivalence relation.
* `CategoryTheory.IsKernelPair.isEquivalenceRelation`: a kernel pair is an internal equivalence
  relation.

## References

* [Stacks Project, Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P)
-/

public section

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory Limits

variable {C : Type*} [Category* C] {R X : C}

/-- The relation on morphisms `T ⟶ X` given by a pair `p₁ p₂ : R ⟶ X`: `a` is related to `b` when
`a = r ≫ p₁` and `b = r ≫ p₂` for some `r : T ⟶ R`. -/
def Rel.ofPairHom (p₁ p₂ : R ⟶ X) (T : C) (a b : T ⟶ X) : Prop :=
  ∃ r : T ⟶ R, r ≫ p₁ = a ∧ r ≫ p₂ = b

variable {p₁ p₂ : R ⟶ X}

/-- `a` and `b` are related by `Rel.ofPairHom p₁ p₂ T` when `a = r ≫ p₁` and `b = r ≫ p₂` for some
`r : T ⟶ R`. -/
theorem Rel.ofPairHom_iff {T : C} {a b : T ⟶ X} :
    Rel.ofPairHom p₁ p₂ T a b ↔ ∃ r : T ⟶ R, r ≫ p₁ = a ∧ r ≫ p₂ = b := (Iff.rfl)

end TauCeti.CategoryTheory

namespace CategoryTheory

open Limits TauCeti.CategoryTheory

variable {C : Type*} [Category* C] {R X : C} {p₁ p₂ : R ⟶ X}

/-- The relation on morphisms `T ⟶ X` given by an internal equivalence relation is an equivalence
relation. -/
theorem EquivalenceRelation.equivalence_ofPairHom (e : EquivalenceRelation p₁ p₂) (T : C) :
    _root_.Equivalence (Rel.ofPairHom p₁ p₂ T) where
  refl a := ⟨a ≫ e.r, by rw [Category.assoc, e.reflexivity₁, Category.comp_id],
    by rw [Category.assoc, e.reflexivity₂, Category.comp_id]⟩
  symm := fun ⟨r, h₁, h₂⟩ ↦ ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁, h₂],
    by rw [Category.assoc, e.symmetry₂, h₁]⟩
  trans := fun ⟨r, h₁, h₂⟩ ⟨r', h₁', h₂'⟩ ↦
    ⟨PullbackCone.IsLimit.lift e.isLimit r r' (h₂.trans h₁'.symm) ≫ e.t,
      by rw [Category.assoc, e.transitivity₁, PullbackCone.IsLimit.lift_fst_assoc, h₁],
      by rw [Category.assoc, e.transitivity₂, PullbackCone.IsLimit.lift_snd_assoc, h₂']⟩

end CategoryTheory

namespace TauCeti.CategoryTheory

open _root_.CategoryTheory Limits

variable {C : Type*} [Category* C] {R X : C} {p₁ p₂ : R ⟶ X}

/-- A pair of parallel morphisms `p₁ p₂ : R ⟶ X` with a pullback of `p₂` and `p₁` is an internal
equivalence relation if and only if it is jointly monic and, for every `T`, the induced relation
on `T ⟶ X` is an equivalence relation. -/
theorem isEquivalenceRelation_iff [HasPullback p₂ p₁] :
    IsEquivalenceRelation p₁ p₂ ↔
      JointlyMono₂ p₁ p₂ ∧ ∀ T : C, _root_.Equivalence (Rel.ofPairHom p₁ p₂ T) := by
  refine ⟨fun ⟨⟨e⟩⟩ ↦ ⟨e.toJointlyMono₂, e.equivalence_ofPairHom⟩, fun ⟨hm, h⟩ ↦ ?_⟩
  obtain ⟨r, hr₁, hr₂⟩ := (h X).refl (𝟙 X)
  obtain ⟨s, hs₁, hs₂⟩ := (h R).symm ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
  obtain ⟨t, ht₁, ht₂⟩ := (h (pullback p₂ p₁)).trans
    ⟨pullback.fst p₂ p₁, rfl, rfl⟩ ⟨pullback.snd p₂ p₁, pullback.condition.symm, rfl⟩
  exact ⟨⟨{ toJointlyMono₂ := hm
            r := r
            s := s
            c := PullbackCone.mk _ _ pullback.condition
            isLimit := pullbackIsPullback p₂ p₁
            t := t }⟩⟩

end TauCeti.CategoryTheory

namespace CategoryTheory

open Limits TauCeti.CategoryTheory

variable {C : Type*} [Category* C] {R X : C} {p₁ p₂ : R ⟶ X}

/-- The projections of an internal equivalence relation are jointly monic. -/
instance IsEquivalenceRelation.jointlyMono₂ [h : IsEquivalenceRelation p₁ p₂] :
    JointlyMono₂ p₁ p₂ :=
  h.nonempty_equivalenceRelation.some.toJointlyMono₂

/-- A kernel pair `p₁, p₂` of `f` admitting a pullback of `p₂` and `p₁` is an internal equivalence
relation. -/
theorem IsKernelPair.isEquivalenceRelation {Y : C} {f : X ⟶ Y} (hk : IsKernelPair f p₁ p₂)
    [HasPullback p₂ p₁] : IsEquivalenceRelation p₁ p₂ :=
  (IsKernelPair.equivalenceRelation f p₁ p₂ (pullbackIsPullback p₂ p₁) hk).isEquivalenceRelation

namespace IsEquivalenceRelation

/-- A chosen internal equivalence relation structure. -/
private noncomputable def equivalenceRelation (h : IsEquivalenceRelation p₁ p₂) :
    EquivalenceRelation p₁ p₂ :=
  h.nonempty_equivalenceRelation.some

/-- The relation on morphisms `T ⟶ X` given by an internal equivalence relation is an equivalence
relation. -/
theorem equivalence_ofPairHom (h : IsEquivalenceRelation p₁ p₂) (T : C) :
    _root_.Equivalence (Rel.ofPairHom p₁ p₂ T) :=
  h.equivalenceRelation.equivalence_ofPairHom T

/-- Exchanging the two projections of an internal equivalence relation gives an internal
equivalence relation. -/
theorem swap (h : IsEquivalenceRelation p₁ p₂) : IsEquivalenceRelation p₂ p₁ :=
  let e := h.equivalenceRelation
  ⟨⟨{ right_cancellation := fun _ f g h₂ h₁ ↦ e.right_cancellation f g h₁ h₂
      r := e.r
      reflexivity₁ := e.reflexivity₂
      reflexivity₂ := e.reflexivity₁
      s := e.s
      symmetry₁ := e.symmetry₂
      symmetry₂ := e.symmetry₁
      c := e.c.flip
      isLimit := PullbackCone.flipIsLimit e.isLimit
      t := e.t
      transitivity₁ := e.transitivity₂
      transitivity₂ := e.transitivity₁ }⟩⟩

/-- The chosen reflexivity morphism `X ⟶ R` of an internal equivalence relation, a section of both
projections. -/
noncomputable def refl (h : IsEquivalenceRelation p₁ p₂) : X ⟶ R :=
  h.equivalenceRelation.r

@[reassoc (attr := simp)]
theorem reflexivity₁ (h : IsEquivalenceRelation p₁ p₂) : h.refl ≫ p₁ = 𝟙 X :=
  h.equivalenceRelation.reflexivity₁

@[reassoc (attr := simp)]
theorem reflexivity₂ (h : IsEquivalenceRelation p₁ p₂) : h.refl ≫ p₂ = 𝟙 X :=
  h.equivalenceRelation.reflexivity₂

/-- The chosen symmetry morphism `R ⟶ R` of an internal equivalence relation, exchanging the
projections. -/
noncomputable def symm (h : IsEquivalenceRelation p₁ p₂) : R ⟶ R :=
  h.equivalenceRelation.s

@[reassoc (attr := simp)]
theorem symmetry₁ (h : IsEquivalenceRelation p₁ p₂) : h.symm ≫ p₁ = p₂ :=
  h.equivalenceRelation.symmetry₁

@[reassoc (attr := simp)]
theorem symmetry₂ (h : IsEquivalenceRelation p₁ p₂) : h.symm ≫ p₂ = p₁ :=
  h.equivalenceRelation.symmetry₂

/-- The chosen transitivity morphism `R ×_X R ⟶ R` of an internal equivalence relation, where the
fibre product is formed over `p₂` on the first factor and `p₁` on the second: it relates `p₁` of
the first point to `p₂` of the second. -/
noncomputable def trans (h : IsEquivalenceRelation p₁ p₂) [HasPullback p₂ p₁] :
    pullback p₂ p₁ ⟶ R :=
  (h.equivalenceRelation.isLimit.conePointUniqueUpToIso (pullbackIsPullback p₂ p₁)).inv ≫
    h.equivalenceRelation.t

@[reassoc (attr := simp)]
theorem transitivity₁ (h : IsEquivalenceRelation p₁ p₂) [HasPullback p₂ p₁] :
    h.trans ≫ p₁ = pullback.fst p₂ p₁ ≫ p₁ := by
  simp [trans, h.equivalenceRelation.transitivity₁]

@[reassoc (attr := simp)]
theorem transitivity₂ (h : IsEquivalenceRelation p₁ p₂) [HasPullback p₂ p₁] :
    h.trans ≫ p₂ = pullback.snd p₂ p₁ ≫ p₂ := by
  simp [trans, h.equivalenceRelation.transitivity₂]

@[reassoc (attr := simp)]
theorem symm_symm (h : IsEquivalenceRelation p₁ p₂) : h.symm ≫ h.symm = 𝟙 R :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

@[reassoc (attr := simp)]
theorem refl_symm (h : IsEquivalenceRelation p₁ p₂) : h.refl ≫ h.symm = h.refl :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

theorem isIso_symm (h : IsEquivalenceRelation p₁ p₂) : IsIso h.symm :=
  ⟨h.symm, h.symm_symm, h.symm_symm⟩

/-- Composing a point with the reflexivity at its second projection is the point itself. -/
@[reassoc (attr := simp)]
theorem lift_id_refl_trans (h : IsEquivalenceRelation p₁ p₂) [HasPullback p₂ p₁] :
    pullback.lift (𝟙 R) (p₂ ≫ h.refl) (by simp) ≫ h.trans = 𝟙 R :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- Composing the reflexivity at the first projection of a point with the point is the point
itself. -/
@[reassoc (attr := simp)]
theorem lift_refl_id_trans (h : IsEquivalenceRelation p₁ p₂) [HasPullback p₂ p₁] :
    pullback.lift (p₁ ≫ h.refl) (𝟙 R) (by simp) ≫ h.trans = 𝟙 R :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

/-- Composing a point with its inverse gives the reflexivity at its first projection. -/
@[reassoc (attr := simp)]
theorem lift_id_symm_trans (h : IsEquivalenceRelation p₁ p₂) [HasPullback p₂ p₁] :
    pullback.lift (𝟙 R) h.symm (by simp) ≫ h.trans = p₁ ≫ h.refl :=
  JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) _ _ (by simp) (by simp)

end IsEquivalenceRelation

end CategoryTheory
