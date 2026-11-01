/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Perfect
import TauCeti.MeasureTheory.Constructions.Polish.Perfect
import TauCeti.Topology.Baire.Perfect
import TauCeti.Topology.MetricSpace.Polish.Pi
import TauCeti.Topology.Perfect

/-!
# Regression examples: countable sets in perfect spaces

These examples exercise meagreness of countable sets and uncountability of comeagre sets:

* the rationals are meagre in `ℝ`, so the irrationals are uncountable;
* in Cantor space every countable set is meagre and every comeagre set is uncountable, so a
  comeagre Borel subset of Cantor space contains a Cantor copy by the Borel perfect set theorem;
* a nonempty perfect Polish space contains the range of a continuous injection of Cantor space;
* without perfectness the conclusion fails: a point of the discrete space `ℕ` is not meagre.
-/

open Set

-- The rationals are meagre in `ℝ`.
example : IsMeagre (range ((↑) : ℚ → ℝ)) :=
  (countable_range _).isMeagre

-- Their complement is comeagre, so the irrationals are uncountable.
example : ¬(range ((↑) : ℚ → ℝ))ᶜ.Countable :=
  TauCeti.not_countable_of_mem_residual (countable_range _).isMeagre

-- In Cantor space, countable sets are meagre.
example {s : Set (ℕ → Bool)} (hs : s.Countable) : IsMeagre s :=
  hs.isMeagre

-- In Cantor space, comeagre sets are uncountable.
example {s : Set (ℕ → Bool)} (hs : s ∈ residual (ℕ → Bool)) : ¬s.Countable :=
  TauCeti.not_countable_of_mem_residual hs

-- A comeagre Borel subset of Cantor space contains a copy of Cantor space.
example {s : Set (ℕ → Bool)} (hs : MeasurableSet s) (hres : s ∈ residual (ℕ → Bool)) :
    ∃ f : (ℕ → Bool) → ℕ → Bool, range f ⊆ s ∧ Continuous f ∧ Function.Injective f :=
  hs.exists_nat_bool_injection_of_not_countable (TauCeti.not_countable_of_mem_residual hres)

-- A nonempty perfect Polish space contains a copy of Cantor space.
example {X : Type*} [TopologicalSpace X] [PolishSpace X] [PerfectSpace X] [Nonempty X] :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Injective f := by
  obtain ⟨f, -, hf⟩ := isClosed_univ.exists_nat_bool_injection_of_not_countable
    (TauCeti.not_countable_of_mem_residual (Filter.univ_mem : univ ∈ residual X))
  exact ⟨f, hf⟩

-- Perfectness is needed: in the discrete space `ℕ` a point is open, hence not meagre.
example : ¬IsMeagre ({0} : Set ℕ) :=
  not_isMeagre_of_isOpen (isOpen_discrete _) (singleton_nonempty 0)
