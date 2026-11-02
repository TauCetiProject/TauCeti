/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic cutoffs along the natural numbers

For any real shift `c`, the logarithms `log (N + c)` of the shifted natural numbers tend to `+∞`.
The logarithms `log n` cut `(0, ∞)` into the steps `(log n, log (n + 1))`, on each of which the
step function `t ↦ ⌊exp t⌋₊` is constant, equal to `n`. At the cutoffs `log (N + 1)`, the
truncated Laplace integral of `t ↦ a ⌊exp t⌋₊` is therefore the partial sum of the Dirichlet
series of `a` plus the corresponding partial sum of a step correction.

## Main results

* `Real.tendsto_log_natCast_add_atTop` — `log (N + c)` tends to `atTop` as `N → ∞`.
* `Real.floor_exp_eq_of_mem_Ioo` — `⌊exp t⌋₊ = n` for `t ∈ (log n, log (n + 1))`, `n > 0`.
-/

public section

namespace Real

open Filter Set

/-- For any real shift `c`, `log (N + c)` tends to `+∞` as the natural number `N` does. -/
theorem tendsto_log_natCast_add_atTop (c : ℝ) :
    Tendsto (fun N : ℕ ↦ log (N + c)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- On the open step `(log n, log (n + 1))`, `n > 0`, the floor of `exp t` is `n`. -/
theorem floor_exp_eq_of_mem_Ioo {n : ℕ} (hn : (0 : ℝ) < n) {t : ℝ}
    (ht : t ∈ Ioo (log n) (log (n + 1))) : ⌊exp t⌋₊ = n := by
  have hlo : (n : ℝ) < exp t := by simpa [exp_log hn] using exp_lt_exp.mpr ht.1
  have hhi : exp t < n + 1 := by
    simpa [exp_log (by positivity : (0 : ℝ) < n + 1)] using exp_lt_exp.mpr ht.2
  exact (Nat.floor_eq_iff (exp_pos t).le).mpr ⟨hlo.le, hhi⟩

end Real
