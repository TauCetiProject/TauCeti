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

* `TauCeti.isAlgebraic_of_trdeg_eq`: if a field has the same finite transcendence degree over two
  fields in a tower, then the intermediate extension is algebraic;
  `TauCeti.isAlgebraic_of_trdeg_eq_one` is the case of transcendence degree one.

The proof uses Mathlib's `lift_trdeg_add_eq`.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {k' : Type v} {F : Type w} [Field k] [Field k'] [Field F]
variable [Algebra k k'] [Algebra k' F] [Algebra k F] [IsScalarTower k k' F]

/-- If `F` has the same transcendence degree over `k` and over an intermediate field `k'`, and
that degree is finite, then `k'` is algebraic over `k`: a transcendental element of `k' / k`
would raise the transcendence degree of `F / k`.  Finiteness of that degree is what lets it be
cancelled from the tower formula. -/
theorem isAlgebraic_of_trdeg_eq (h : Algebra.trdeg k' F = Algebra.trdeg k F)
    (hfin : Algebra.trdeg k F < Cardinal.aleph0) : Algebra.IsAlgebraic k k' := by
  rw [← trdeg_eq_zero_iff]
  have hadd := lift_trdeg_add_eq k k' F
  rw [h] at hadd
  rcases Cardinal.add_eq_right_iff.mp hadd with hle | hzero
  -- the first alternative would force the transcendence degree of `F / k` to be infinite
  · exact absurd ((le_max_left _ _).trans hle) (not_le.2 (Cardinal.lift_lt_aleph0.2 hfin))
  · simpa using hzero

/-- If `F` has transcendence degree one over both `k` and an intermediate field `k'`, then `k'`
is algebraic over `k`: transcendence degree one leaves no room for a transcendental element. -/
theorem isAlgebraic_of_trdeg_eq_one (h : Algebra.trdeg k F = 1) (h' : Algebra.trdeg k' F = 1) :
    Algebra.IsAlgebraic k k' :=
  isAlgebraic_of_trdeg_eq (h'.trans h.symm) (by rw [h]; exact Cardinal.one_lt_aleph0)

end TauCeti
