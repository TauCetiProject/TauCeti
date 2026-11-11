/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.NegationClosed

/-!
# Regression examples: negation-closed fragments of `L_{ω₁ω}`

These examples exercise negation closure from a downstream module, through public statements only:

* the negation closure of the empty set is the empty fragment: no `⊥` is added at an arity without
  a member;
* over an arbitrary language, with no countability assumption on its symbols, the negation closure
  of a single sentence is countable and contains its double negation.
-/

universe u v

open FirstOrder FirstOrder.Language

-- The empty set has the empty negation closure.
example {L : Language.{u, v}} :
    Fragment.negationClosure (∅ : Set (Σ n, L.BoundedFormulaω Empty n)) = ⊥ :=
  Fragment.negationClosure_empty

-- Over any language, the negation closure of one sentence is countable and contains `¬¬φ`.
example {L : Language.{u, v}} (φ : L.Sentenceω) :
    ((Fragment.negationClosure {⟨0, φ⟩} : Fragment L) :
        Set (Σ n, L.BoundedFormulaω Empty n)).Countable ∧
      (⟨0, φ.not.not⟩ : Σ n, L.BoundedFormulaω Empty n) ∈
        Fragment.negationClosure {⟨0, φ⟩} := by
  have h := Fragment.negationClosed_negationClosure (L := L) {⟨0, φ⟩}
  exact ⟨Fragment.negationClosure_countable (Set.countable_singleton _),
    h.not_mem (h.not_mem (Fragment.subset_negationClosure _ rfl))⟩
