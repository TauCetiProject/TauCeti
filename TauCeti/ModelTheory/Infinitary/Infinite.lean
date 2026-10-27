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

The cardinality assertions and their characterization of infinite structures reuse Mathlib's
`FirstOrder.Language.infiniteTheory` and `FirstOrder.Language.model_infiniteTheory_iff`.
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
  rw [SentenceInf.realize_def, FormulaInf.realize_def, infiniteSentence_def,
    BoundedFormulaInf.realize_iInf]
  simp only [BoundedFormula.realize_toInf]
  simpa [infiniteTheory, Theory.model_iff, Sentence.Realize, Formula.Realize,
    Subsingleton.elim default (Empty.elim : Empty → M)] using
      (L.model_infiniteTheory_iff (M := M))

/-- Conjoining the infinitude sentence restricts realization to infinite carriers. -/
@[simp]
theorem realize_inf_infiniteSentence_iff {M : Type w} [L.Structure M] (φ : L.Sentenceω) :
    SentenceInf.Realize (φ ⊓ L.infiniteSentence) M ↔ SentenceInf.Realize φ M ∧ Infinite M := by
  simpa only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf] using
      and_congr (Iff.rfl : SentenceInf.Realize φ M ↔ _) (L.realize_infiniteSentence_iff (M := M))

end FirstOrder.Language
