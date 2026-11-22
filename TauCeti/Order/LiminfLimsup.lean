/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.LiminfLimsup

/-!
# The lower limit of a pointwise maximum

In a complete linear order the lower limit of a pointwise maximum `max (u i) (v i)` is at most
`max (liminf u) (limsup v)`. Mathlib's `limsup_max` computes the upper limit of a maximum
exactly; for the lower limit only this mixed bound holds in general. Taking the maximum with a
sequence whose upper limit is at most the lower limit of `u` therefore leaves that lower limit
unchanged; this is how an exponentially negligible error is absorbed into a large deviation lower
bound.
-/

public section

open Filter

namespace TauCeti

variable {α β : Type*} [CompleteLinearOrder β] {f : Filter α}

/-- The lower limit of a pointwise maximum is at most the larger of the lower limit of the first
sequence and the upper limit of the second. -/
theorem liminf_max_le_max_liminf_limsup (u v : α → β) :
    liminf (fun i => max (u i) (v i)) f ≤ max (liminf u f) (limsup v f) := by
  rw [liminf_eq_iSup_iInf]
  refine iSup₂_le fun s hs => le_max_iff.2 (or_iff_not_imp_right.2 fun hv => ?_)
  -- Where `v` is eventually below the infimum `c` of the maximum over `s`, `u` is at least `c`.
  have hu : ∀ᶠ i in f, ⨅ j ∈ s, max (u j) (v j) ≤ u i := by
    filter_upwards [hs, eventually_lt_of_limsup_lt (not_le.1 hv)] with i his hvi
    exact (le_max_iff.1 (biInf_le _ his)).resolve_right hvi.not_ge
  exact le_liminf_of_le (by isBoundedDefault) hu

end TauCeti
