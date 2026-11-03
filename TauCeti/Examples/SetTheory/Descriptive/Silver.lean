/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.Silver

/-!
# Regression examples: Silver's theorem

These examples exercise Silver's theorem from a downstream module, through public statements
only:

* for equality on an uncountable Polish space, Silver's theorem gives a continuous injection of
  Cantor space, the conclusion of Mathlib's perfect set theorem
  `IsClosed.exists_nat_bool_injection_of_not_countable` for the whole space;
* the relative form, applied to equality on a Borel subset, gives the same conclusion inside the
  subset.
-/

open Set

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

-- Equality on an uncountable Polish space: the Cantor antichain is a continuous injection.
example (hX : ¬ Countable X) : ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Injective f := by
  have hinj : Function.Injective (Quotient.mk (⊥ : Setoid X)) := fun _ _ h =>
    by simpa only [Setoid.bot_def] using Quotient.exact h
  obtain h | h := Setoid.silver_dichotomy ⊥
    (by simpa only [Setoid.bot_def, diagonal] using measurableSet_diagonal (α := X))
  · exact absurd hinj.countable hX
  · obtain ⟨f, hf, -, hf_inj, -⟩ := h.exists_injective
    exact ⟨f, hf, hf_inj⟩

-- Equality on an uncountable Borel set `A`: the relative form puts a continuous injection of
-- Cantor space inside `A`.
example {A : Set X} (hA : MeasurableSet A) (hunc : ¬ A.Countable) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ A ∧ Continuous f ∧ Function.Injective f := by
  have hinj : Function.Injective (Quotient.mk (⊥ : Setoid A)) := fun _ _ h =>
    by simpa only [Setoid.bot_def] using Quotient.exact h
  obtain h | h := Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hA ⊥ ⊥
    (fun x y h => by
      simp only [Setoid.bot_def] at h ⊢
      exact Subtype.ext h)
    (by simpa only [Setoid.bot_def, diagonal] using measurableSet_diagonal (α := A))
  · exact absurd (countable_coe_iff.1 hinj.countable) hunc
  · obtain ⟨f, hf, hfA, hf_inj, -⟩ := h.exists_injective
    exact ⟨f, hfA, hf, hf_inj⟩
