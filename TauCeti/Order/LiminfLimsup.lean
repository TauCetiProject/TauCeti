/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.LiminfLimsup

/-!
# The lower limit of a pointwise maximum

In a conditionally complete linear order the lower limit of a pointwise maximum
`max (u i) (v i)` is at most `max (liminf u) (limsup v)`, under the usual boundedness side
conditions, which hold automatically in a complete linear order. Mathlib's `limsup_max` computes
the upper limit of a maximum exactly; for the lower limit only this mixed bound holds in general.
Taking the maximum with a sequence whose upper limit is at most the lower limit of `u` therefore
leaves that lower limit unchanged; this is how an exponentially negligible error is absorbed into
a large deviation lower bound.
-/

public section

open Filter

namespace TauCeti

variable {α β : Type*} [ConditionallyCompleteLinearOrder β] {f : Filter α}

/-- The lower limit of a pointwise maximum is at most the larger of the lower limit of the first
sequence and the upper limit of the second. -/
theorem liminf_max_le_max_liminf_limsup (u v : α → β)
    (hu : IsCoboundedUnder (· ≥ ·) f u := by isBoundedDefault)
    (hv : IsBoundedUnder (· ≤ ·) f v := by isBoundedDefault)
    (huv : IsBoundedUnder (· ≥ ·) f (fun i => max (u i) (v i)) := by isBoundedDefault) :
    liminf (fun i => max (u i) (v i)) f ≤ max (liminf u f) (limsup v f) := by
  refine liminf_le_of_le huv fun b hb => le_max_iff.2 (or_iff_not_imp_right.2 fun hbv => ?_)
  -- Where `v` is eventually below `b`, the bound `b ≤ max (u i) (v i)` forces `b ≤ u i`.
  refine le_liminf_of_le hu ?_
  filter_upwards [hb, eventually_lt_of_limsup_lt (not_le.1 hbv) hv] with i hi hvi
  exact (le_max_iff.1 hi).resolve_right hvi.not_ge

end TauCeti
