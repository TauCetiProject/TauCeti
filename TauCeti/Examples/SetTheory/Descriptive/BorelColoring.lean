/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Cardinality
import TauCeti.SetTheory.Descriptive.BorelColoring

/-!
# Regression examples: countable Borel colorings

These examples exercise the coloring API from a downstream module, through public statements
only:

* inequality of first coordinates on Cantor space is colored by the first coordinate;
* the inequality relation on `ℝ` has no countable Borel coloring, since equality on `ℝ` has
  uncountably many classes;
* a relation with a loop has no coloring, and the empty set is independent for it.
-/

open MeasureTheory

-- Inequality of first coordinates on Cantor space: the first coordinate is a two-color Borel
-- coloring.
example : SetRel.HasCountableBorelColoring {p : (ℕ → Bool) × (ℕ → Bool) | p.1 0 ≠ p.2 0} :=
  SetRel.hasCountableBorelColoring_iff.2
    ⟨fun x ↦ Encodable.encode (x 0),
      (measurable_of_countable Encodable.encode).comp (measurable_pi_apply 0),
      fun _ _ h heq ↦ h (Encodable.encode_injective heq)⟩

-- Equality on `ℝ` has uncountably many classes, so its inequivalence relation, inequality, has no
-- countable Borel coloring.
example : ¬ SetRel.HasCountableBorelColoring {p : ℝ × ℝ | p.1 ≠ p.2} := by
  intro h
  have := (⊥ : Setoid ℝ).countable_quotient_of_hasCountableBorelColoring_not
    (by simpa [Setoid.bot_def] using h)
  exact Cardinal.not_countable_real
    (Set.countable_univ_iff.2 Setoid.quotientBotEquiv.symm.injective.countable)

-- The diagonal relation on `ℕ` has a loop at every point, so it has no coloring, although the
-- empty set is still independent for it.
example : ¬ SetRel.HasCountableBorelColoring (SetRel.id : SetRel ℕ ℕ) ∧
    (SetRel.id : SetRel ℕ ℕ).IsIndependent ∅ :=
  ⟨SetRel.not_hasCountableBorelColoring_of_mem (x := 0) rfl, SetRel.IsIndependent.empty⟩
