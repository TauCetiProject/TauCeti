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
