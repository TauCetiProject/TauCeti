/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Vaught
public import TauCeti.ModelTheory.Counting.Scattered.Thin

/-!
# Scattered and rank forms of Vaught's conjecture

Vaught's perfect-set conjecture is equivalent to the assertion that every sentence whose models
on `ℕ` are back-and-forth scattered has countably many models on `ℕ` up to isomorphism.
This is the scattered (or absolute) formulation: scatteredness is equivalent to thinness, and
Vaught's conjecture says precisely that a thin sentence has countably many models on `ℕ`.
`VaughtConjecture` counts all countable models, including finite ones, and
`vaughtConjecture_iff_nat` reduces it to the statement for models on `ℕ`.

On a scattered model class, countability of the isomorphism classes is equivalent to boundedness
of any isolating rank below `ω₁`. Consequently the conjecture also says that every isolating rank
is bounded on every thin sentence, or, equivalently, that the external Scott height is bounded
there. These formulations impose no continuum hypothesis. Only the analogous reformulation of
the *cardinal* conjecture assumes `ℵ₁ < 𝔠`.

## Main results

* `TauCeti.vaughtConjecture_iff_bfScattered`: the scattered-sentence formulation.
* `TauCeti.cardinalVaughtConjecture_iff_bfScattered`: the cardinal formulation when CH fails.
* `TauCeti.vaughtConjecture_iff_bounded_isolatingRank`: the formulation using every isolating rank.
* `TauCeti.vaughtConjecture_iff_bounded_scottHeight`: the canonical external Scott-height form.

## References

* U. Andrews, I. Goldbring, S. Hachtman, H. J. Keisler and D. Marker,
  *Scattered sentences have few separable randomizations*, §§1–2, for the equivalence of the
  absolute and strong forms and their distinction from the cardinal form under CH.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.1, for scattered sentences and bounded Scott ranks.
-/

public section

open FirstOrder FirstOrder.Language Cardinal Ordinal

namespace TauCeti

open RelationalConfiguration

/-- **The scattered formulation of Vaught's conjecture.** The perfect-set conjecture for all
countable models is equivalent, without CH, to countability of the isomorphism classes on `ℕ`
for every sentence whose models on `ℕ` are back-and-forth scattered. -/
theorem vaughtConjecture_iff_bfScattered :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      BFScattered (modelsOf (V := ℕ) φ) → Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [vaughtConjecture_iff_nat]
  constructor
  · intro h L _ _ φ hscat
    exact (h L φ).resolve_right (Setoid.isThinOn_iff.1 hscat.isThinOn)
  · intro h L _ _ φ
    exact or_iff_not_imp_right.2 fun hthin =>
      h L φ (isThinOnNatModels_iff.2 hthin).bfScattered_modelsOf

/-- When `ℵ₁ < 𝔠`, the cardinal Vaught conjecture is equivalent to countability of the models
on `ℕ` of every back-and-forth scattered sentence. CH implies `CardinalVaughtConjecture`
(`cardinalVaughtConjecture_of_aleph_one_eq_continuum`), so the equivalence is stated only under
`ℵ₁ < 𝔠`. -/
theorem cardinalVaughtConjecture_iff_bfScattered (hc : ℵ₁ < (𝔠 : Cardinal.{0})) :
    CardinalVaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      BFScattered (modelsOf (V := ℕ) φ) → Countable (Quotient (isoSetoidOn ℕ φ)) :=
  (cardinalVaughtConjecture_iff_vaughtConjecture hc).trans vaughtConjecture_iff_bfScattered

/-- **The isolating-rank formulation of Vaught's conjecture.** The perfect-set conjecture is
equivalent to boundedness below `ω₁` of every isolating rank on the models on `ℕ` of every thin
sentence. No least isolating rank, and no continuum hypothesis, is assumed. -/
theorem vaughtConjecture_iff_bounded_isolatingRank :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω)
      (ρ : RelationalConfiguration L ℕ → Ordinal.{0}), IsIsolatingRank ρ →
      IsThinOnNatModels φ → ∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, ρ c < β := by
  rw [vaughtConjecture_iff_bfScattered]
  constructor
  · intro h L _ _ φ ρ hρ hthin
    exact (hthin.countable_quotient_isoSetoidOn_iff_bounded hρ).1
      (h L φ hthin.bfScattered_modelsOf)
  · intro h L _ _ φ hscat
    have hthin := bfScattered_modelsOf_iff_isThinOnNatModels.1 hscat
    exact (hthin.countable_quotient_isoSetoidOn_iff_bounded
      (isIsolatingRank_scottHeight L)).2 (h L φ _ (isIsolatingRank_scottHeight L) hthin)

/-- **The Scott-height formulation of Vaught's conjecture.** It suffices to bound the external
Scott height below `ω₁` on the models on `ℕ` of every thin sentence; this is also necessary.
The height is that of the decoded structure, not the internal Scott rank. -/
theorem vaughtConjecture_iff_bounded_scottHeight :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω), IsThinOnNatModels φ →
      ∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, @scottHeight L _ ℕ c.toStructure < β := by
  constructor
  · intro h L _ _ φ hthin
    exact (vaughtConjecture_iff_bounded_isolatingRank.1 h) L φ _
      (isIsolatingRank_scottHeight L) hthin
  · intro h
    refine vaughtConjecture_iff_bfScattered.2 fun L _ _ φ hscat => ?_
    have hthin := bfScattered_modelsOf_iff_isThinOnNatModels.1 hscat
    exact (hthin.countable_quotient_isoSetoidOn_iff_bounded
      (isIsolatingRank_scottHeight L)).2 (h L φ hthin)

end TauCeti
