/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.PotentialIso
public import TauCeti.ModelTheory.BackAndForth.Countable

/-!
# Scott's isomorphism theorem

Every countable structure in a countable relational language has an infinitary sentence
whose countable models are exactly its isomorphic copies. The sentence at any countable
internally stabilizing level has this property; the canonical Scott sentence chooses the
least such level. The model and the original structure may inhabit different universes,
and empty structures are included.

This is Dana Scott's *Logic with denumerably long formulas and finite strings of quantifiers*
(1965), using the tuple-upgrade Scott sentences and potential-isomorphism comparison developed
in `TauCeti.ModelTheory.Scott.Sentence` and `TauCeti.ModelTheory.Scott.PotentialIso`.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Countable M]
variable {N : Type w'} [L.Structure N] [Countable N]

/-- At a countable internally stabilizing level, the Scott sentence characterizes the
original structure up to isomorphism among countable structures.

Use this characterization explicitly: `realize_scottSentenceAt` is the simp normal form
at arbitrary countable levels, where internal stabilization need not hold. -/
theorem realize_scottSentenceAt_iff {α : Ordinal.{o}} (hα : α < ω₁)
    (hs : SelfStabilizesCompletely (L := L) M α) :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N ↔ Nonempty (M ≃[L] N) := by
  constructor
  · intro h
    exact countable_potentialIso_iff_iso.mp (potentialIso_of_realize_scottSentenceAt M hα h)
  · rintro ⟨e⟩
    exact e.realize_scottSentenceAt hα hs

/-- The canonical Scott sentence characterizes a countable structure up to isomorphism
among countable structures, without an additional stabilization hypothesis. -/
@[simp]
theorem realize_scottSentence_iff :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ Nonempty (M ≃[L] N) := by
  rw [scottSentence_def]
  exact realize_scottSentenceAt_iff M (selfStabilizationOrdinal_lt_omega_one M)
    (selfStabilizesCompletely_selfStabilizationOrdinal M)

/-- Scott's isomorphism theorem: every countable structure in a countable relational
language has an Lω₁ω sentence whose countable models are exactly its isomorphic copies.
The quantified models may lie in a universe different from that of the original structure. -/
theorem scott_isomorphism :
    ∃ σ : L.Sentenceω, SentenceInf.Realize σ M ∧
      ∀ (N : Type w') [L.Structure N] [Countable N],
        SentenceInf.Realize σ N ↔ Nonempty (M ≃[L] N) :=
  ⟨scottSentence (L := L) M, realize_scottSentence_self M,
    fun _ _ _ => realize_scottSentence_iff M⟩

end TauCeti
