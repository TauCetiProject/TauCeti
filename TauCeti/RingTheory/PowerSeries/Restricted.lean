/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted

/-!
# Introduction rules for restricted power series

Mathlib's `PowerSeries.IsRestricted` asks the weighted coefficient norms of a power series to
tend to zero. A series whose coefficients vanish in every degree past some bound — a polynomial —
satisfies that condition at every radius, and a series restricted at one radius is restricted at
every smaller one. This file records these two introduction rules.

## Main results

* `TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero`: a series with a vanishing tail is
  restricted at every radius.
* `TauCeti.PowerSeries.isRestricted_of_abs_le`: restrictedness passes to smaller radii, and
  `TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le` is the resulting containment of subrings.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

/-- A power series whose coefficients vanish in every degree `≥ n` is restricted at every radius:
its weighted coefficient norms are eventually zero. Such a series is a polynomial of degree less
than `n`. -/
theorem isRestricted_of_forall_coeff_eq_zero {n : ℕ}
    (hf : ∀ m, n ≤ m → f.coeff m = 0) : f.IsRestricted c := by
  rw [PowerSeries.isRestricted_iff']
  have h : ∀ᶠ m in Filter.atTop, (0 : ℝ) = ‖f.coeff m‖ * c ^ m := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    simp [hf m hm]
  exact Filter.Tendsto.congr' h tendsto_const_nhds

/-- **Restrictedness passes to smaller radii.** If the weighted coefficient norms of `f` tend to
zero at the radius `c'`, they do so at every radius `c` with `|c| ≤ |c'|`, being dominated by the
former. -/
theorem isRestricted_of_abs_le {c' : ℝ} (hf : f.IsRestricted c') (h : |c| ≤ |c'|) :
    f.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf ⊢
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hf
  gcongr

/-- Over an ultrametric ring, the subring of series restricted at `c'` lies in the subring of
series restricted at any `c` with `|c| ≤ |c'|`. -/
theorem isRestrictedSubring_le_of_abs_le [IsUltrametricDist R] {c' : ℝ} (h : |c| ≤ |c'|) :
    PowerSeries.IsRestricted.subring (R := R) c' ≤ PowerSeries.IsRestricted.subring c :=
  fun _ hf ↦ isRestricted_of_abs_le hf h

end TauCeti.PowerSeries
