/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import TauCeti.Algebra.Order.Floor.Semifield

/-!
# Logarithmic cutoffs along the natural numbers

The logarithms `log (N + c)` of the shifted natural numbers are positive for a real shift
`c > 1`, and tend to `+∞` for any real shift `c`.
The logarithms `log n` cut `(0, ∞)` into the steps `(log n, log (n + 1))`, on each of which the
step function `t ↦ ⌊exp t⌋₊` is constant, equal to `n`. At the cutoffs `log (N + 1)`, the
truncated Laplace integral of `t ↦ a ⌊exp t⌋₊` is therefore the partial sum of the Dirichlet
series of `a` plus the corresponding partial sum of a step correction.

## Main results

* `Real.log_natCast_add_pos` — `log (N + c)` is positive for every shift `c > 1`.
* `Real.tendsto_log_natCast_add_atTop` — `log (N + c)` tends to `atTop` as `N → ∞`.
* `Real.floor_exp_eq_of_mem_Ioo` — `⌊exp t⌋₊ = n` for `t ∈ (log n, log (n + 1))`.
* `TauCeti.exists_rounded_scales` — round two exponential cutoffs, using a multiple of the
  lower cutoff for the upper cutoff, with logarithmic errors at most one.
-/

public section

namespace Real

open Filter Set

/-- For a real shift `c > 1`, `log (N + c)` is positive for every natural number `N`. -/
theorem log_natCast_add_pos {c : ℝ} (hc : 1 < c) (N : ℕ) : 0 < log (N + c) :=
  log_pos (by linarith [N.cast_nonneg (α := ℝ)])

/-- For any real shift `c`, `log (N + c)` tends to `+∞` as the natural number `N` does. -/
theorem tendsto_log_natCast_add_atTop (c : ℝ) :
    Tendsto (fun N : ℕ ↦ log (N + c)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- On the open step `(log n, log (n + 1))`, the floor of `exp t` is `n`. For `n = 0` the step is
empty. -/
theorem floor_exp_eq_of_mem_Ioo {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (log n) (log (n + 1))) : ⌊exp t⌋₊ = n := by
  rcases n.eq_zero_or_pos with rfl | hn'
  · simp at ht
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn'
  have hlo : (n : ℝ) < exp t := by simpa [exp_log hn] using exp_lt_exp.mpr ht.1
  have hhi : exp t < n + 1 := by
    simpa [exp_log (by positivity : (0 : ℝ) < n + 1)] using exp_lt_exp.mpr ht.2
  exact (Nat.floor_eq_iff (exp_pos t).le).mpr ⟨hlo.le, hhi⟩

end Real

namespace TauCeti

/-- Round `exp u` down to a natural number `y` and `exp v` strictly up to the least multiple `b`
of `q * y`. If `0 ≤ u`, `0 < q`, and `q * exp u ≤ exp v`, both cutoffs are positive and rounding
changes their logarithms by at most one. -/
theorem exists_rounded_scales {u v : ℝ} {q : ℕ} (hu : 0 ≤ u) (hq : 0 < q)
    (hstep : (q : ℝ) * Real.exp u ≤ Real.exp v) :
    let y := ⌊Real.exp u⌋₊
    ∃ b : ℕ, 0 < y ∧ 0 < b ∧ IsLeast {n : ℕ | q * y ∣ n ∧ Real.exp v < (n : ℝ)} b ∧
      u - 1 ≤ Real.log y ∧ Real.log y ≤ u ∧ v ≤ Real.log b ∧ Real.log b ≤ v + 1 := by
  intro y
  have hExp : 1 ≤ Real.exp u := Real.one_le_exp_iff.2 hu
  have hy : 0 < y := Nat.le_floor (by simpa using hExp)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlo : u - 1 ≤ Real.log y := by
    refine (Real.le_log_iff_exp_le hy').2 ?_
    rw [Real.exp_sub]
    exact (div_le_div_of_nonneg_left (Real.exp_pos u).le zero_lt_two he).trans
      (Nat.div_two_lt_floor hExp).le
  have hfloor : (y : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
  let d := q * y
  have hd : 0 < d := Nat.mul_pos hq hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdv : (d : ℝ) ≤ Real.exp v := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg q)).trans hstep
  obtain ⟨j, _, hlt, hle⟩ := exists_pos_nat_mul_bounds (Real.exp_pos v).le hd'
  have hb : (0 : ℝ) < (j : ℝ) * d := (Real.exp_pos v).trans hlt
  refine ⟨j * d, hy, by exact_mod_cast hb, ⟨⟨dvd_mul_left _ _, by exact_mod_cast hlt⟩, ?_⟩,
    hlo, (Real.log_le_iff_le_exp hy').2 hfloor, ?_, ?_⟩
  · rintro n ⟨⟨k, rfl⟩, hn⟩
    rw [Nat.mul_comm d k]
    apply Nat.mul_le_mul_right
    by_contra! hjk
    have hgap : (k : ℝ) * d + d ≤ (j : ℝ) * d := by
      rw [← add_one_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hjk) hd'.le
    have hn' : Real.exp v < (d : ℝ) * k := by exact_mod_cast hn
    rw [mul_comm (d : ℝ)] at hn'
    linarith
  · push_cast
    exact (Real.le_log_iff_exp_le hb).2 hlt.le
  · push_cast
    refine (Real.log_le_iff_le_exp hb).2 ?_
    rw [Real.exp_add]
    calc
      _ ≤ Real.exp v + d := hle
      _ ≤ Real.exp v * 2 := by linarith
      _ ≤ Real.exp v * Real.exp 1 := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le

end TauCeti
