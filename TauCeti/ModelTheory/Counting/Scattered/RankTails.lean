/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Sentence.Basic
public import TauCeti.SetTheory.Descriptive.ThinRank
import TauCeti.ModelTheory.RelationalConfiguration.Observables
import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Thinness from countable spectra on rank tails

Suppose every countable list of sentences has countable spectrum on some tail of a rank
`r` below `ω₁`. The threshold may depend on the list. On a Borel Cantor antichain of
configurations, choose a list whose truth sequences recover the Cantor parameters. Only
countably many parameters can then lie above the threshold, and their ranks are bounded below
`ω₁`. Thus the entire antichain has bounded rank.

Together with countability of fixed-rank antichains, this gives a `Setoid.IsThinRankOn` for
isomorphism, and hence thinness. Neither the rank nor the ambient class is required to be Borel.
One way of supplying the tail hypothesis is to prove that each individual sentence eventually
has constant truth as the rank increases.

## References

* Adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
  `InfinitaryLogic/Descriptive/FragmentTail.lean` (commit `518a366`, Apache-2.0).
-/

public section

open FirstOrder FirstOrder.Language Ordinal Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
  {C : Set (RelationalConfiguration L V)} {r : RelationalConfiguration L V → Ordinal.{o}}

/-- If every sentence has constant truth above some countable threshold, then each countable
list has countable spectrum above some countable threshold. No countability of the vocabulary
or carrier is needed. -/
theorem exists_countable_image_sentenceTheory_tail_of_eventually_constant
    (h : ∀ φ : L.Sentenceω, ∃ b < ω₁, ∃ p : Bool,
      ∀ c ∈ C, b ≤ r c → (c ∈ modelsOf φ ↔ p = true)) (θ : ℕ → L.Sentenceω) :
    ∃ b < ω₁, (sentenceTheory θ '' {c ∈ C | b ≤ r c}).Countable := by
  choose b hb p hp using fun n => h (θ n)
  refine ⟨⨆ n, b n, iSup_lt_omega_one hb, (countable_singleton p).mono ?_⟩
  rintro _ ⟨c, ⟨hc, hcr⟩, rfl⟩
  refine mem_singleton_iff.2 (funext fun n => Bool.eq_iff_iff.2 ?_)
  simpa only [sentenceTheory_eq_true_iff] using hp n c hc ((Ordinal.le_iSup b n).trans hcr)

variable [Countable V] [∀ n, Countable (L.Relations n)]

/-- Countable sentence spectra on rank tails force the rank to be bounded below `ω₁` on the
range of any measurable family of pairwise non-isomorphic configurations in `C` parametrized
by Cantor space. Neither the rank nor `C` need be measurable or isomorphism invariant. -/
theorem boundedRankOn_range_of_countable_image_sentenceTheory_tails
    (htail : ∀ θ : ℕ → L.Sentenceω,
      ∃ b < ω₁, (sentenceTheory θ '' {c ∈ C | b ≤ r c}).Countable)
    {f : (ℕ → Bool) → RelationalConfiguration L V} (hf : Measurable f) (hfC : range f ⊆ C)
    (hne : ∀ x y, x ≠ y → ¬ isoSetoid L V (f x) (f y))
    (hr : ∀ x, r (f x) < ω₁) : BoundedRankOn r (range f) := by
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_apply_eq hf hne
  obtain ⟨b, hb, hcount⟩ := htail θ
  have hhigh : {x | b ≤ r (f x)}.Countable := by
    apply hcount.mono
    intro x hx
    exact ⟨f x, ⟨hfC (mem_range_self x), hx⟩, hθ x⟩
  obtain ⟨d, hd, hbound⟩ := hhigh.exists_lt_omega_one_forall_lt (r := r ∘ f) fun x _ => hr x
  refine boundedRankOn_iff.2 ⟨max b d, max_lt hb hd, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : b ≤ r (f x)
  · exact (hbound x hx).trans_le (le_max_right b d)
  · exact (lt_of_not_ge hx).trans_le (le_max_left b d)

/-- Countability of fixed-rank antichains and eventual countability of every sentence spectrum
supply a thinness rank analysis for isomorphism. The rank bound holds on the whole Cantor
antichain, so no proper subcopy is needed. -/
theorem isThinRankOn_of_countable_image_sentenceTheory_tails
    (hr : ∀ c ∈ C, r c < ω₁)
    (hfib : ∀ α < ω₁, ∀ ⦃B : Set (RelationalConfiguration L V)⦄, B ⊆ C ∩ r ⁻¹' {α} →
      B.Pairwise (fun c d => ¬ isoSetoid L V c d) → B.Countable)
    (htail : ∀ θ : ℕ → L.Sentenceω,
      ∃ b < ω₁, (sentenceTheory θ '' {c ∈ C | b ≤ r c}).Countable) :
    (isoSetoid L V).IsThinRankOn r C where
  lt_omega_one := hr
  countable_antichain := hfib
  exists_boundedRankOn_comp := fun {_} hf hfC hne =>
    ⟨id, continuous_id, Function.injective_id,
      boundedRankOn_range_of_countable_image_sentenceTheory_tails htail hf.measurable hfC hne
        (fun x => hr _ (hfC (mem_range_self x)))⟩

end TauCeti.RelationalConfiguration
