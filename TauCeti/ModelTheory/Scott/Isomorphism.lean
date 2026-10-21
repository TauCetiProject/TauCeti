/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Scott's isomorphism theorem

For a countable relational language, every countable structure `M` is characterized up to
isomorphism among countable structures by a single `Lω₁ω` sentence. The Scott sentence of `M` at
any countable internally stabilizing level holds in a countable structure exactly when that
structure is isomorphic to `M`: its models are potentially isomorphic to `M`, and potential
isomorphism between countable structures is isomorphism. Conversely, isomorphic copies satisfy
it by invariance of infinitary satisfaction.

The countability of the model cannot be dropped: models of the Scott sentence of any cardinality
are only potentially isomorphic to `M` (`TauCeti.potentialIso_of_realize_scottSentenceAt`).

## Main results

* `TauCeti.realize_scottSentenceAt_iff`: at a countable internally stabilizing level, the Scott
  sentence holds in a countable structure exactly when it is isomorphic to `M`.
* `TauCeti.realize_scottSentence_iff`: the same for the canonical Scott sentence.
* `TauCeti.scott_isomorphism`: **Scott's isomorphism theorem**, every countable structure has an
  `Lω₁ω` sentence true in exactly the countable structures isomorphic to it.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, in
  *The Theory of Models*, 1965.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Countable M]

/-- At a countable internally stabilizing level, the Scott sentence of a countable structure `M`
holds in a countable structure exactly when that structure is isomorphic to `M`. -/
theorem realize_scottSentenceAt_iff {α : Ordinal.{o}} (hα : α < ω₁)
    (hs : SelfStabilizesCompletely (L := L) M α) (N : Type w') [L.Structure N] [Countable N] :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => countable_potentialIso_iff_iso.mp (potentialIso_of_realize_scottSentenceAt M hα h),
    fun ⟨e⟩ => e.realize_scottSentenceAt hα hs⟩

/-- The canonical Scott sentence of a countable structure `M` holds in a countable structure
exactly when that structure is isomorphic to `M`. -/
@[simp]
theorem realize_scottSentence_iff (N : Type w') [L.Structure N] [Countable N] :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => countable_potentialIso_iff_iso.mp (potentialIso_of_realize_scottSentence M h),
    fun ⟨e⟩ => e.realize_scottSentence⟩

/-- **Scott's isomorphism theorem.** In a countable relational language, every countable
structure `M` has an `Lω₁ω` sentence that `M` satisfies and that holds in a countable structure,
in any universe, exactly when that structure is isomorphic to `M`. -/
theorem scott_isomorphism :
    ∃ σ : L.Sentenceω, SentenceInf.Realize σ M ∧
      ∀ (N : Type w') [L.Structure N] [Countable N],
        (SentenceInf.Realize σ N ↔ Nonempty (M ≃[L] N)) :=
  ⟨scottSentence (L := L) M, realize_scottSentence_self M,
    fun N _ _ => realize_scottSentence_iff M N⟩

end TauCeti
