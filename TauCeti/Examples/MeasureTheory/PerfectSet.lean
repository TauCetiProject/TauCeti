/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Cardinality
import TauCeti.MeasureTheory.Constructions.Polish.Perfect
import TauCeti.Topology.MetricSpace.Perfect
import TauCeti.Topology.Perfect

/-!
# Regression examples: perfect sets and cardinality

These examples exercise the perfect set theorem for Borel sets and the cardinality bounds on
concrete spaces:

* the irrational numbers of `[0, 1]`, an uncountable Borel set that is neither open nor closed,
  contain the range of a continuous injection of Cantor space and have `𝔠` elements;
* Baire space `ℕ → ℕ`, as a nonempty perfect subset of itself, has `𝔠` elements;
* every quotient of `ℝ` has at most `𝔠` classes; here the countable separation hypothesis is
  found by instance search from the standard Borel structure of `ℝ`.
-/

open Set Cardinal

-- The irrationals of `[0, 1]` contain a Cantor copy and have cardinality continuum.
example :
    (∃ f : (ℕ → Bool) → ℝ, range f ⊆ Icc 0 1 \ range ((↑) : ℚ → ℝ) ∧ Continuous f ∧
      f.Injective) ∧
    #(Icc (0 : ℝ) 1 \ range ((↑) : ℚ → ℝ) : Set ℝ) = 𝔠 := by
  have hs : MeasurableSet (Icc (0 : ℝ) 1 \ range ((↑) : ℚ → ℝ)) :=
    measurableSet_Icc.diff (countable_range _).measurableSet
  have hunc : ¬(Icc (0 : ℝ) 1 \ range ((↑) : ℚ → ℝ)).Countable := fun h =>
    (Real.Icc_countable_iff (x := 0) (y := 1)).not.2 (by norm_num) <|
      (h.union (countable_range ((↑) : ℚ → ℝ))).mono fun x hx => by
        by_cases hq : x ∈ range ((↑) : ℚ → ℝ)
        · exact Or.inr hq
        · exact Or.inl ⟨hx, hq⟩
  exact ⟨hs.exists_nat_bool_injection_of_not_countable hunc,
    hs.mk_eq_continuum_of_not_countable hunc⟩

-- Baire space is perfect and Polish, so it has cardinality continuum.
example : #(univ : Set (ℕ → ℕ)) = 𝔠 :=
  (PerfectSpace.univ_perfect (α := ℕ → ℕ)).mk_eq_continuum univ_nonempty

-- Every quotient of `ℝ` has at most continuum many classes.
example (E : Setoid ℝ) : #(Quotient E) ≤ 𝔠 :=
  E.mk_quotient_le_continuum
