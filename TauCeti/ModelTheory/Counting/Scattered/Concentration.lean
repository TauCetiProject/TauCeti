/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.Basic

/-!
# Concentration at back-and-forth levels

A set `C` of relational configurations on `ℕ` is *concentrated at back-and-forth levels* when, at
every countable level `α`, some configuration `k` (the centre, possibly outside `C`, possibly
depending on `α`) has all but countably many isomorphism classes of `C` inside its level-`α`
class. The members of `C` off the centre's class meet only countably many isomorphism classes.

Concentration is the combinatorial shape of minimally uncountable classes of models, in which
every sentence cut has a side meeting countably many isomorphism classes (Montalbán, Chapter XII).
This file proves the facts about concentration that need no descriptive set theory.

* A concentrated set is back-and-forth scattered: at level `α`, the members of `C` on the centre's
  class give one level class, and the countably many isomorphism classes off it give countably
  many more, since isomorphism refines every level.
* A set meeting countably many isomorphism classes is concentrated, with any centre.
* **One side is small.** If `B ⊆ C` is saturated in `C` at a single countable level `α` (every
  member of `C` that is `α`-equivalent to a member of `B` lies in `B`) and `C` is concentrated,
  then `B` or `C \ B` meets only countably many isomorphism classes. If a member of `B` lies in
  the centre's class at level `α`, then all of `C \ B` lies off it; otherwise all of `B` does.

No definability or invariance of `C`, and no countability of the language, is assumed.

## Main definitions

* `TauCeti.ConcentratedAtBFLevels C`: at every countable level, all but countably many isomorphism
  classes of `C` lie in one level class.

## Main results

* `TauCeti.ConcentratedAtBFLevels.mono`: subsets of concentrated sets are concentrated.
* `TauCeti.ConcentratedAtBFLevels.of_countable_isoClasses`: countably many isomorphism classes
  give a concentrated set.
* `TauCeti.ConcentratedAtBFLevels.bfScattered`: a concentrated set is back-and-forth scattered.
* `TauCeti.ConcentratedAtBFLevels.countable_isoClasses_or_of_saturated`: one side of a split
  saturated at a countable level meets countably many isomorphism classes.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII
  (minimally uncountable and minimally unbounded sentences).
* Concentration, the passage to scatteredness and the one-side-small argument are also formalized
  in Cameron Freer's `cameronfreer/infinitary-logic`,
  `InfinitaryLogic/Descriptive/BFConcentration.lean` (checkpoint `518a366`, Apache-2.0), whose
  definition and proof plan are followed here. Here the counting statements are phrased through
  the restricted quotients used by `TauCeti.BFScattered`, and the saturation hypothesis of the
  one-side-small argument is one-sided.
-/

public section

universe u v

open FirstOrder Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {B C K : Set (RelationalConfiguration L ℕ)}

/-- A set `C` of configurations on `ℕ` is *concentrated at back-and-forth levels* when, at every
countable level `α`, some configuration `k` has the property that the members of `C` not
`α`-equivalent to `k` meet only countably many isomorphism classes. The centre `k` may lie outside
`C` and may depend on `α`. -/
def ConcentratedAtBFLevels (C : Set (RelationalConfiguration L ℕ)) : Prop :=
  ∀ α : Ordinal.{0}, α < ω₁ → ∃ k : RelationalConfiguration L ℕ,
    (Quotient.mk (isoSetoid L ℕ) '' {c ∈ C | ¬ bfEquivSetoid L ℕ α c k}).Countable

/-- Unfolding lemma for `TauCeti.ConcentratedAtBFLevels`. -/
theorem concentratedAtBFLevels_iff : ConcentratedAtBFLevels C ↔
    ∀ α : Ordinal.{0}, α < ω₁ → ∃ k : RelationalConfiguration L ℕ,
      (Quotient.mk (isoSetoid L ℕ) '' {c ∈ C | ¬ bfEquivSetoid L ℕ α c k}).Countable :=
  Iff.rfl

namespace ConcentratedAtBFLevels

/-- Subsets of concentrated sets are concentrated, with the same centres. -/
theorem mono (hKC : K ⊆ C) (hC : ConcentratedAtBFLevels C) : ConcentratedAtBFLevels K :=
  fun α hα =>
    let ⟨k, hk⟩ := hC α hα
    ⟨k, hk.mono (image_mono fun _ hc => by exact ⟨hKC hc.1, hc.2⟩)⟩

/-- A set meeting countably many isomorphism classes is concentrated, with any centre. -/
theorem of_countable_isoClasses
    [Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : C → _)))] :
    ConcentratedAtBFLevels C := by
  have hC := Setoid.countable_quotient_comap_val_iff.1
    (inferInstance : Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : C → _))))
  exact fun _ _ => ⟨RelationalConfiguration.mk fun _ => false,
    hC.mono (image_mono fun _ hc => hc.1)⟩

/-- **A concentrated set is back-and-forth scattered.** At a countable level `α` with centre
`k`, the members of `C` that are `α`-equivalent to `k` form one level class, and the remaining
members meet countably many isomorphism classes, each contained in a single level class. -/
theorem bfScattered (hC : ConcentratedAtBFLevels C) : BFScattered C := by
  refine bfScattered_iff_countable_image.2 fun α hα => ?_
  obtain ⟨k, hk⟩ := hC α hα
  -- The level-`α` classes off the centre are images of the countably many isomorphism classes.
  have hoff := hk.image (Quotient.lift (Quotient.mk (bfEquivSetoid L ℕ α))
    fun _ _ h => Quotient.sound (isoSetoid_le_bfEquivSetoid α h))
  rw [image_image] at hoff
  simp only [Quotient.lift_mk] at hoff
  refine (hoff.insert (Quotient.mk _ k)).mono ?_
  rintro _ ⟨c, hc, rfl⟩
  by_cases hck : bfEquivSetoid L ℕ α c k
  · exact Or.inl (Quotient.sound hck)
  · exact Or.inr ⟨c, ⟨hc, hck⟩, rfl⟩

/-- **One side of a saturated split is small.** Let `C` be concentrated and `B ⊆ C` saturated in
`C` at a countable level `α`: every member of `C` that is `α`-equivalent to a member of `B` lies
in `B`. Then `B` or `C \ B` meets only countably many isomorphism classes. -/
theorem countable_isoClasses_or_of_saturated (hC : ConcentratedAtBFLevels C) (hBC : B ⊆ C)
    {α : Ordinal.{0}} (hα : α < ω₁)
    (hsat : ∀ b ∈ B, ∀ c ∈ C, bfEquivSetoid L ℕ α b c → c ∈ B) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : B → _))) ∨
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C \ B) → _))) := by
  simp only [Setoid.countable_quotient_comap_val_iff]
  obtain ⟨k, hk⟩ := hC α hα
  by_cases hB : ∃ b ∈ B, bfEquivSetoid L ℕ α b k
  · -- A member of `B` lies in the centre's class, so saturation keeps `C \ B` off that class.
    obtain ⟨b, hb, hbk⟩ := hB
    refine Or.inr (hk.mono (image_mono fun c hc => ?_))
    exact ⟨hc.1, fun hck => hc.2 (hsat b hb c hc.1
      ((bfEquivSetoid L ℕ α).trans' hbk ((bfEquivSetoid L ℕ α).symm' hck)))⟩
  · -- Otherwise all of `B` lies off the centre's class.
    exact Or.inl (hk.mono (image_mono fun b hb => by exact ⟨hBC hb, fun hbk => hB ⟨b, hb, hbk⟩⟩))

end ConcentratedAtBFLevels

end TauCeti
