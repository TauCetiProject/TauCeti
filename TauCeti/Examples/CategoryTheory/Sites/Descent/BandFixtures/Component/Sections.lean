/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.Component.Sections

/-!
# Checks for the central sections of constant diagrams of copies of `B(C₃)`

On the point category `Discrete PUnit`, with `C₃ = Multiplicative (ZMod 3)`:

* the section of the profile with coefficient `1` evaluates to the group element `1`, at every
  arrow;
* restriction keeps the profile, and the inverse recovers it;
* for the connected diagram `B(C₃)`, evaluation at the canonical object is bijective, and there
  are three central sections;
* for the two-component diagram `Discrete Bool × B(C₃)` there is a section other than the unit
  whose evaluation on the `false` component is the identity, so evaluation there is not injective;
  there are nine central sections, and the diagram is not a gerbe for the bottom topology;
* for the one-component diagram with trivial inertia there is one central section.
-/

public section

namespace TauCeti.Examples.ComponentSections

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.BandFixtures

/-- The cyclic group of order three, written multiplicatively. -/
abbrev C₃ : Type := Multiplicative (ZMod 3)

/-- The point category. -/
abbrev pt : Type := Discrete PUnit.{1}

/-- The object of the point category. -/
abbrev star : pt := ⟨PUnit.unit⟩

/-- **Band evaluation.** In the connected `C₃` diagram, the section of the profile with coefficient
`1` evaluates to the group element `1` at every arrow. -/
example (f : star ⟶ star) :
    ((IntrinsicBandSections.evaluation f (componentObj star PUnit.unit)
      (componentSectionsEquiv pt PUnit C₃ star fun _ ↦ Multiplicative.ofAdd 1)).asIso.hom).2 =
      (Multiplicative.ofAdd 1 : C₃) :=
  evaluation_componentSectionsEquiv_snd f _ _

/-- **Restriction and inverse.** Restriction keeps the profile, and the inverse recovers it. -/
example (f : star ⟶ star) (a : Bool → C₃) :
    IntrinsicBandSections.restrict f (componentSectionsEquiv pt Bool C₃ star a) =
        componentSectionsEquiv pt Bool C₃ star a ∧
      (componentSectionsEquiv pt Bool C₃ star).symm (componentSectionsEquiv pt Bool C₃ star a) =
        a :=
  ⟨restrict_componentSectionsEquiv f a, MulEquiv.symm_apply_apply _ a⟩

/-- **Connected: evaluation is bijective.** -/
example : Function.Bijective (IntrinsicBandSections.evaluation
    (F := constant pt (Discrete PUnit × SingleObj C₃)) (𝟙 star) (componentObj star PUnit.unit)) :=
  component_eval_bijective star PUnit.unit

/-- **Connected: three central sections.** -/
example :
    Nat.card (IntrinsicBandSections (constant pt (Discrete PUnit × SingleObj C₃)) star) = 3 := by
  rw [← Nat.card_congr (componentSectionsEquiv pt PUnit C₃ star).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun]
  simp [Fintype.card_multiplicative, ZMod.card]

/-- **Two components: a section other than the unit evaluates to the identity on `false`.** -/
example : ∃ s : IntrinsicBandSections (constant pt (Discrete Bool × SingleObj C₃)) star, s ≠ 1 ∧
    IntrinsicBandSections.evaluation (𝟙 star) (componentObj star false) s = 1 := by
  refine ⟨componentSectionsEquiv pt Bool C₃ star fun b ↦ if b then Multiplicative.ofAdd 1 else 1,
    fun h ↦ ?_, ?_⟩
  · have := congrFun ((componentSectionsEquiv pt Bool C₃ star).injective
      (h.trans (map_one _).symm)) true
    exact absurd this (by decide)
  · rw [← map_one (IntrinsicBandSections.evaluation (𝟙 star) (componentObj star false)),
      ← map_one (componentSectionsEquiv pt Bool C₃ star)]
    refine componentObj_aut_ext ?_
    rw [evaluation_componentSectionsEquiv_snd, evaluation_componentSectionsEquiv_snd]
    simp

/-- **Two components: evaluation on `false` is not injective.** -/
example : ¬ Function.Injective (IntrinsicBandSections.evaluation
    (F := constant pt (Discrete Bool × SingleObj C₃)) (𝟙 star) (componentObj star false)) :=
  component_eval_not_injective star (g := Multiplicative.ofAdd 1) (by decide)

/-- **Two components: nine central sections.** -/
example :
    Nat.card (IntrinsicBandSections (constant pt (Discrete Bool × SingleObj C₃)) star) = 9 := by
  rw [← Nat.card_congr (componentSectionsEquiv pt Bool C₃ star).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fun]
  simp [Fintype.card_multiplicative, ZMod.card]

/-- **Two components: not a gerbe** for the bottom topology. -/
example : ¬ (constant pt (Discrete Bool × SingleObj C₃)).IsGerbe ⊥ :=
  constant_two_components_not_gerbe star

/-- **Trivial inertia: one central section.** -/
example : Nat.card
    (IntrinsicBandSections (constant pt (Discrete PUnit × SingleObj (Multiplicative PUnit))) star) =
      1 := by
  rw [← Nat.card_congr (componentSectionsEquiv pt PUnit (Multiplicative PUnit) star).toEquiv]
  simp

end TauCeti.Examples.ComponentSections
