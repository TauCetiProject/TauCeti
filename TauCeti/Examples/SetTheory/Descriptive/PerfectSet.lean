/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Cardinality
import TauCeti.SetTheory.Descriptive.PerfectSet

/-!
# Regression examples: the perfect set theorem for analytic sets

These examples exercise the perfect set theorem for analytic sets on concrete spaces:

* the projection to `ℝ` of a closed subset of `ℝ × (ℕ → ℕ)`, an analytic set that need not be
  Borel, contains a Cantor copy and has `𝔠` points as soon as it is uncountable, and its pairs of
  distinct points form an analytic subset of `ℝ × ℝ`;
* the closed equivalence relation `|x| = |y|` on `ℝ`, the kernel of the absolute value, has a
  Cantor antichain.
-/

open Set Cardinal MeasureTheory

-- An uncountable projection of a closed subset of `ℝ × (ℕ → ℕ)` contains a Cantor copy and has
-- cardinality continuum.
example {C : Set (ℝ × (ℕ → ℕ))} (hC : IsClosed C) (hunc : ¬(Prod.fst '' C).Countable) :
    (∃ f : (ℕ → Bool) → ℝ, range f ⊆ Prod.fst '' C ∧ Continuous f ∧ f.Injective) ∧
    #(Prod.fst '' C) = 𝔠 :=
  have hs : AnalyticSet (Prod.fst '' C) := hC.analyticSet.image_of_continuous continuous_fst
  ⟨hs.exists_nat_bool_injection_of_not_countable hunc, hs.mk_eq_continuum_of_not_countable hunc⟩

-- The pairs of distinct points of such a projection form an analytic subset of `ℝ × ℝ`.
example {C : Set (ℝ × (ℕ → ℕ))} (hC : IsClosed C) : AnalyticSet (Prod.fst '' C).offDiag :=
  (hC.analyticSet.image_of_continuous continuous_fst).offDiag

-- The relation `|x| = |y|` on `ℝ` has a Cantor antichain: the range `[0, ∞)` of the absolute
-- value is uncountable.
example : (Setoid.ker fun x : ℝ => |x|).HasCantorAntichainOn univ := by
  refine Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range (f := fun x : ℝ => |x|)
    continuous_abs fun h => ?_
  have hIci : (Ici (0 : ℝ)).Countable := h.mono fun x (hx : 0 ≤ x) =>
    mem_range.2 ⟨x, abs_of_nonneg hx⟩
  have hle := le_aleph0_iff_set_countable.2 hIci
  rw [mk_Ici_real] at hle
  exact hle.not_gt aleph0_lt_continuum
