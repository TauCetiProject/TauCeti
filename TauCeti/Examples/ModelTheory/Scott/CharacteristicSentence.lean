/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Scott.CharacteristicSentence
import TauCeti.ModelTheory.Scott.NatPredicate

/-!
# Regression examples for Scott sentences of finite structures

These downstream examples check the characteristic sentence of finite pure sets, including the
empty one, and contrast the infinitary Scott sentence of a one-point structure in the language of
countably many unary predicates with the absence of a first-order one.
-/

namespace TauCeti

open FirstOrder FirstOrder.Language

section PureSets

variable [Language.empty.Structure Bool] [∀ n, Language.empty.Structure (Fin n)]
variable [Language.empty.Structure Empty] [Language.empty.Structure ℕ]

-- A two-element set satisfies the characteristic sentence of `Bool`; a three-element set does
-- not.
example : Fin 2 ⊨ characteristicSentence (L := Language.empty) Bool ∧
    ¬ Fin 3 ⊨ characteristicSentence (L := Language.empty) Bool := by
  simp [realize_characteristicSentence_iff]

-- The characteristic sentence of the empty set rejects every nonempty set.
example : ¬ ℕ ⊨ characteristicSentence (L := Language.empty) Empty := by
  simp [realize_characteristicSentence_iff, Cardinal.aleph0_ne_zero.symm]

-- The Scott sentence of a finite set rejects an infinite set.
example : ¬ SentenceInf.Realize (scottSentence (L := Language.empty) Bool) ℕ := by
  simp [realize_scottSentence_iff_realize_characteristicSentence,
    realize_characteristicSentence_iff, (Cardinal.ofNat_lt_aleph0 (n := 2)).ne]

end PureSets

section NatPredicates

-- The infinitary Scott sentence of a one-point structure in the language of countably many
-- unary predicates characterizes it among structures of every cardinality, although no
-- first-order sentence does so even among countable structures.
example (S : Set ℕ) :
    letI := natPredicateStructure S
    (∀ (N : Type) [natPredicateLanguage.Structure N],
      SentenceInf.Realize (scottSentence (L := natPredicateLanguage) Unit) N ↔
        Nonempty (Unit ≃[natPredicateLanguage] N)) ∧
    ¬ ∃ φ : natPredicateLanguage.Sentence, ∀ (N : Type) [natPredicateLanguage.Structure N]
      [Countable N], N ⊨ φ ↔ Nonempty (Unit ≃[natPredicateLanguage] N) := by
  let := natPredicateStructure S
  exact ⟨fun _ _ => realize_scottSentence_iff_of_finite Unit,
    not_exists_sentence_iff_nonempty_equiv_natPredicateStructure S⟩

end NatPredicates

end TauCeti
