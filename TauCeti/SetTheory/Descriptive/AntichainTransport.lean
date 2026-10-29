/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Antichain
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.MeasureTheory.Constructions.Polish.Perfect

/-!
# Transporting antichains along measurable embeddings

Let `g : X → Y` be a measurable embedding of Polish spaces with their Borel σ-algebras, and let
`E` on `X` and `F` on `Y` be equivalence relations with `F (g x) (g y) ↔ E x y`. Then a set
`A ⊆ X` carries a Cantor antichain for `E` exactly when `g '' A` carries one for `F`, and `A` is
thin for `E` exactly when `g '' A` is thin for `F`. Neither `A` nor the relations need be Borel,
and `g` need not be continuous.

## Main results

* `Setoid.hasCantorAntichainOn_image_iff`: Cantor antichains transport along `g` in both
  directions.
* `Setoid.isThinOn_image_iff`: thinness transports along `g` in both directions.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/AntichainTransport.lean`.
* Divergences from that source: the results are in the `Setoid` namespace, with the antichain
  vocabulary of `TauCeti.SetTheory.Descriptive.Antichain`; the range of a Cantor antichain is shown
  uncountable from the cardinality of Cantor space rather than by a diagonal argument.
-/

public section

open MeasureTheory Set Function Cardinal

namespace Setoid

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {E : Setoid X} {F : Setoid Y} {g : X → Y}

/-- **Cantor antichains transport along measurable embeddings.** If `g` is a measurable embedding
of Polish spaces with `F (g x) (g y) ↔ E x y`, then `g '' A` carries a Cantor antichain for `F`
exactly when `A` carries one for `E`. -/
theorem hasCantorAntichainOn_image_iff (hg : MeasurableEmbedding g)
    (hrel : ∀ x y, F (g x) (g y) ↔ E x y) (A : Set X) :
    F.HasCantorAntichainOn (g '' A) ↔ E.HasCantorAntichainOn A := by
  -- The witness is transported as a Borel set, never as a map. The range of a Cantor antichain is
  -- an uncountable Borel set of pairwise inequivalent points; its preimage or image under `g` is
  -- again one, and the Borel perfect set theorem extracts a new Cantor antichain from it.
  -- Cantor space is uncountable, so the range of an injection of it is too
  have hcard : #(ℕ → Bool) = 𝔠 := by simp
  have hcantor : ¬ Countable (ℕ → Bool) := fun _ =>
    aleph0_lt_continuum.not_ge (hcard ▸ mk_le_aleph0)
  have huncX {f : (ℕ → Bool) → X} (hinj : Injective f) : ¬ (range f).Countable := fun hc =>
    hcantor (by have := hc.to_subtype; exact (rangeFactorization_injective.2 hinj).countable)
  have huncY {f : (ℕ → Bool) → Y} (hinj : Injective f) : ¬ (range f).Countable := fun hc =>
    hcantor (by have := hc.to_subtype; exact (rangeFactorization_injective.2 hinj).countable)
  constructor
  · intro h
    obtain ⟨f, hf, hfA, hinj, hF⟩ := h.exists_injective
    -- the preimage of the witness: Borel, uncountable, inside `A`
    have hpre : MeasurableSet (g ⁻¹' range f) :=
      hg.measurable (isCompact_range hf).isClosed.measurableSet
    have hpre_unc : ¬ (g ⁻¹' range f).Countable := fun hc => huncY hinj <| (hc.image g).mono <| by
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, -, ha⟩ := hfA ⟨x, rfl⟩
      exact ⟨a, by rw [mem_preimage, ha]; exact ⟨x, rfl⟩, ha⟩
    obtain ⟨k, hkrange, hk, hkinj⟩ :=
      MeasurableSet.exists_nat_bool_injection_of_not_countable hpre hpre_unc
    refine hasCantorAntichainOn_iff.2 ⟨k, hk, fun x => ?_, fun x y hxy hE => ?_⟩
    · obtain ⟨b, hb⟩ := hkrange ⟨x, rfl⟩
      obtain ⟨a, ha, hga⟩ := hfA ⟨b, rfl⟩
      rwa [hg.injective (hga.trans hb)] at ha
    · obtain ⟨a, ha⟩ := hkrange ⟨x, rfl⟩
      obtain ⟨b, hb⟩ := hkrange ⟨y, rfl⟩
      have hab : a ≠ b := by
        rintro rfl
        exact hkinj.ne hxy (hg.injective (ha.symm.trans hb))
      exact hF a b hab (by rw [ha, hb]; exact (hrel _ _).2 hE)
  · intro h
    obtain ⟨f, hf, hfA, hinj, hE⟩ := h.exists_injective
    -- the image of the witness: Borel, by Lusin–Souslin through `g`, and uncountable
    have himg : MeasurableSet (g '' range f) :=
      hg.measurableSet_image.2 (isCompact_range hf).isClosed.measurableSet
    have himg_unc : ¬ (g '' range f).Countable := fun hc =>
      huncX hinj ((hc.preimage_of_injOn hg.injective.injOn).mono (subset_preimage_image g _))
    obtain ⟨k, hkrange, hk, hkinj⟩ :=
      MeasurableSet.exists_nat_bool_injection_of_not_countable himg himg_unc
    refine hasCantorAntichainOn_iff.2 ⟨k, hk, fun x => ?_, fun x y hxy hF => ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩, hga⟩ := hkrange ⟨x, rfl⟩
      exact ⟨f a, hfA ⟨a, rfl⟩, hga⟩
    · obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hkrange ⟨x, rfl⟩
      obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hkrange ⟨y, rfl⟩
      have hab : a ≠ b := by
        rintro rfl
        exact hkinj.ne hxy (ha.symm.trans hb)
      rw [← ha, ← hb, hrel] at hF
      exact hE a b hab hF

/-- **Thinness transports along measurable embeddings.** If `g` is a measurable embedding of
Polish spaces with `F (g x) (g y) ↔ E x y`, then `g '' A` is thin for `F` exactly when `A` is thin
for `E`. -/
theorem isThinOn_image_iff (hg : MeasurableEmbedding g) (hrel : ∀ x y, F (g x) (g y) ↔ E x y)
    (A : Set X) : F.IsThinOn (g '' A) ↔ E.IsThinOn A := by
  rw [isThinOn_iff_not_hasCantorAntichainOn, isThinOn_iff_not_hasCantorAntichainOn,
    hasCantorAntichainOn_image_iff hg hrel]

end Setoid
