/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Products of discrete σ-algebras

The product of the discrete σ-algebras on two countable types is again discrete. Countability is
what makes this work: the measurable rectangles already exhaust the singletons of the product, and
countably many of them suffice to build any subset.

## Main results

* `TauCeti.MeasureTheory.prod_top_eq_top_of_countable`: the product of the discrete σ-algebras on
  two countable types is discrete.
-/

public section

namespace TauCeti.MeasureTheory

/-- The product of the discrete σ-algebras on two countable types is discrete. -/
theorem prod_top_eq_top_of_countable (α β : Type*) [Countable α] [Countable β] :
    (⊤ : MeasurableSpace α).prod (⊤ : MeasurableSpace β) = ⊤ := by
  apply top_unique
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  intro s _
  exact MeasurableSet.of_discrete

end TauCeti.MeasureTheory
