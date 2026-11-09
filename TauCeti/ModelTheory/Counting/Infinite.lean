/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Classes

/-!
# Restricting the count to infinite models

Conjoining a sentence with `FirstOrder.Language.infiniteSentence` leaves its models on `ℕ`
unchanged and removes all its finite models, including the empty model. Consequently the
count of the conjunction is exactly the number of isomorphism classes on `ℕ`, and a perfect
set of non-isomorphic countable models of the conjunction must occur on `ℕ`.

These identities allow statements about all countable models to be specialized to countably
infinite models without silently discarding the finite tiers. No countability assumption on
the language is needed.

## Main results

* `TauCeti.countableModelCount_inf_infiniteSentence`: the count of the conjunction is the
  cardinality of the isomorphism quotient on `ℕ`.
* `TauCeti.hasPerfectlyManyCountableModels_inf_infiniteSentence_iff`: the conjunction has
  perfectly many countable models exactly when the original sentence has a perfect antichain
  of models on `ℕ`.
-/

public section

universe u v

open FirstOrder FirstOrder.Language Cardinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-- Conjoining the infinitude sentence removes every finite tier, so the count of all countable
models becomes exactly the number of countably infinite models up to isomorphism. -/
@[simp]
theorem countableModelCount_inf_infiniteSentence (φ : L.Sentenceω) :
    countableModelCount (φ ⊓ L.infiniteSentence) = #(Quotient (isoSetoidOn ℕ φ)) := by
  have hnat : modelsOf (V := ℕ) (φ ⊓ L.infiniteSentence) = modelsOf φ := by simp
  have hfin (n : ℕ) : #(Quotient (isoSetoidOn (Fin n) (φ ⊓ L.infiniteSentence))) = 0 := by
    have hempty : modelsOf (V := Fin n) (φ ⊓ L.infiniteSentence) = ∅ := by simp
    have : IsEmpty (modelsOf (V := Fin n) (φ ⊓ L.infiniteSentence)) := by
      rw [hempty]
      infer_instance
    exact mk_eq_zero _
  rw [countableModelCount_eq_add_sum]
  simp only [hfin, sum_const, lift_zero, mul_zero, add_zero]
  unfold isoSetoidOn
  rw [hnat]

/-- A perfect set of non-isomorphic models of the conjunction with infinitude exists exactly
when such a set of models of the original sentence exists on `ℕ`. No finite tier can supply it. -/
@[simp]
theorem hasPerfectlyManyCountableModels_inf_infiniteSentence_iff (φ : L.Sentenceω) :
    HasPerfectlyManyCountableModels (φ ⊓ L.infiniteSentence) ↔
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ) := by
  rw [hasPerfectlyManyCountableModels_iff]
  simp only [modelsOf_inf, modelsOf_infiniteSentence_of_infinite, inter_univ,
    modelsOf_infiniteSentence_of_finite, inter_empty]
  constructor
  · rintro (h | ⟨n, h⟩)
    · exact h
    · obtain ⟨P, _, hP, hsub, _⟩ := Setoid.hasPerfectAntichainOn_iff.1 h
      exact (not_nonempty_empty (hP.mono hsub)).elim
  · exact Or.inl

end TauCeti
