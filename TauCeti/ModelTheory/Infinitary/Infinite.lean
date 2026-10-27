/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# An infinitary sentence for infinite structures

The sentence `FirstOrder.Language.infiniteSentence` is the countable conjunction of Mathlib's
`FirstOrder.Language.Sentence.cardGe` sentences. It holds exactly in infinite structures, so
conjoining it with a sentence restricts that sentence to its infinite models, without changing
its models on an infinite carrier.

The cardinality assertions reuse Mathlib's `FirstOrder.Language.Sentence.cardGe` and
`FirstOrder.Language.Sentence.realize_cardGe`; their characterization of infinite structures
uses `Cardinal.aleph0_le` and `Cardinal.infinite_iff`.
-/

public section

universe u v w

namespace FirstOrder.Language

variable (L : Language.{u, v})

/-- The countable conjunction asserting that the structure has at least `n` elements for every
natural number `n`. -/
def infiniteSentence : L.Sentenceω :=
  .iInf fun n => (Sentence.cardGe L n).toInf

/-- The infinitude sentence is the conjunction of the finitary cardinality sentences. -/
theorem infiniteSentence_def :
    L.infiniteSentence = .iInf fun n => (Sentence.cardGe L n).toInf :=
  (rfl)

/-- A structure satisfies the infinitude sentence exactly when its carrier is infinite. This
also applies to empty structures and to languages with function symbols. -/
@[simp]
theorem realize_infiniteSentence_iff {M : Type w} [L.Structure M] :
    SentenceInf.Realize L.infiniteSentence M ↔ Infinite M := by
  simp only [infiniteSentence_def, SentenceInf.realize_iInf, Sentence.realize_toInf,
    Sentence.realize_cardGe, Cardinal.infinite_iff, Cardinal.aleph0_le]

end FirstOrder.Language
