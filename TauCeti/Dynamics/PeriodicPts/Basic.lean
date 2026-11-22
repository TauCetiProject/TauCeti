/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Minimal periods of intertwined self-maps

If a map `f : α → β` intertwines two self-maps `fa : α → α` and `fb : β → β`
(`Function.Semiconj f fa fb`), then the periodic behavior of `x` under `fa` governs that of
`f x` under `fb`:

* `Function.Semiconj.minimalPeriod_dvd`: the minimal period of `f x` divides that of `x`.
* `Function.Semiconj.minimalPeriod_eq`: when `f` is injective, the two minimal periods coincide.
* `Function.Semiconj.minimalPeriod_eq_mul_iterate`: the minimal period of `x` under `fa` factors
  as the minimal period `c` of `f x` under `fb` times the minimal period of `x` under the return
  map `fa^[c]`.
-/

public section

namespace Function.Semiconj

variable {α β : Type*} {f : α → β} {fa : α → α} {fb : β → β}

/-- If `f` intertwines `fa` with `fb`, the minimal period of `f x` under `fb` divides the
minimal period of `x` under `fa`. When `x` is not periodic the right side is `0`. -/
theorem minimalPeriod_dvd (h : Semiconj f fa fb) (x : α) :
    minimalPeriod fb (f x) ∣ minimalPeriod fa x :=
  ((isPeriodicPt_minimalPeriod fa x).map h).minimalPeriod_dvd

/-- An injective map intertwining two self-maps preserves minimal periods. -/
theorem minimalPeriod_eq (h : Semiconj f fa fb) (hf : Injective f) (x : α) :
    minimalPeriod fa x = minimalPeriod fb (f x) :=
  minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ by
    simp only [IsPeriodicPt, IsFixedPt, ← h.iterate_right n x, hf.eq_iff]

/-- If `f` intertwines `fa` and `fb`, then the minimal period of `x` under `fa` factors as the
minimal period of `f x` under `fb` times the minimal period of `x` under `fa^[c]`. -/
theorem minimalPeriod_eq_mul_iterate (h : Semiconj f fa fb) (x : α) :
    minimalPeriod fa x =
      minimalPeriod fb (f x) * minimalPeriod (fa^[minimalPeriod fb (f x)]) x := by
  set c := minimalPeriod fb (f x)
  have hdvd : c ∣ minimalPeriod fa x := h.minimalPeriod_dvd x
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, Nat.zero_mul]
    exact Nat.zero_dvd.mp (hc ▸ hdvd)
  · rw [minimalPeriod_iterate_eq_div_gcd hc, Nat.gcd_eq_right hdvd, Nat.mul_div_cancel' hdvd]

end Function.Semiconj
