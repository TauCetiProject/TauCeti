/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.FinTrdeg

/-!
# Transcendence degree in field towers

This file records general consequences of the transcendence-degree tower formula for field
extensions.

## Main results

* `TauCeti.isAlgebraic_of_trdeg_eq_one`: if a field has transcendence degree one over two fields
  in a tower, then the intermediate extension is algebraic.

The proof uses Mathlib's `lift_trdeg_add_eq`.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {k' : Type v} {F : Type w} [Field k] [Field k'] [Field F]
variable [Algebra k k'] [Algebra k' F] [Algebra k F] [IsScalarTower k k' F]

/-- If `F` has transcendence degree one over both `k` and an intermediate field `k'`, then `k'`
is algebraic over `k`: transcendence degree one leaves no room for a transcendental element. -/
theorem isAlgebraic_of_trdeg_eq_one (h : Algebra.trdeg k F = 1) (h' : Algebra.trdeg k' F = 1) :
    Algebra.IsAlgebraic k k' := by
  rw [← trdeg_eq_zero_iff]
  have hadd := lift_trdeg_add_eq k k' F
  rw [h, h'] at hadd
  simp only [Cardinal.lift_one] at hadd
  rcases Cardinal.add_eq_right_iff.mp hadd with hle | hzero
  -- the first alternative would force `ℵ₀ ≤ 1`
  · exact absurd ((le_max_left _ _).trans hle) (by simp)
  · simpa using hzero

end TauCeti
