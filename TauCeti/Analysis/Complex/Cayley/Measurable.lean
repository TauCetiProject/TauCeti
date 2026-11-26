/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import TauCeti.Analysis.Complex.Cayley.Basic

/-!
# Measurability of the real inverse Cayley coordinate

The real inverse coordinate is measurable on the complex plane, including its value at the pole.
-/

public section

open MeasureTheory

namespace Complex

/-- The inverse Cayley coordinate is measurable. -/
@[fun_prop] theorem measurable_inverseCayleyCoord : Measurable inverseCayleyCoord := by
  rw [funext inverseCayleyCoord_def]
  fun_prop

end Complex
