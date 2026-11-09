/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Filtration

/-!
# Bounds for right-continuous filtrations

The right-continuation of a filtration at a time is contained in its sigma-algebra at
any strictly later time. This bound allows independence and measurability statements
at later times to be applied to the right-continuous past.
-/

public section

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/-- The right-continuation at `i` is contained in the filtration at every later time `j`. -/
theorem rightCont_le_of_lt [LinearOrder ι] [DenselyOrdered ι]
    (ℱ : Filtration ι m) {i j : ι} (hij : i < j) : ℱ.rightCont i ≤ ℱ j := by
  rw [ℱ.rightCont_eq_of_not_isMax (not_isMax_iff.mpr ⟨j, hij⟩)]
  exact iInf₂_le j hij

end MeasureTheory.Filtration
