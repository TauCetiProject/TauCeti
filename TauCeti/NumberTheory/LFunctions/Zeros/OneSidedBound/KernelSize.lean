/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetSize
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The non-row cost in a Gaussian theta-jet bound

The bound for a single translated vacuum contains three costs besides the logarithmic sizes of
its rows: the vacuum bound, the Gaussian factor for the matrix variables, and the sum of the
row lengths divided by the growth rate. At growth rate `a + 1`, where `a = x * b`, their total
logarithmic cost fits within `x ^ 50`. This leaves the row sizes as the only terms that require
a precise comparison when composing the lifts.

The factors and scales are those in `New.Data.sqrt_weylNormSq_jetMap_le` in
`grh/src/New/UpperBound/Size/ArchimedeanSize.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Finset Real

namespace TauCeti.OneSidedBound

private theorem log_gaussianScale_le {x : ℝ} {b : ℕ} (hx : 5 ≤ x)
    (hL : log b ≤ x) : log (2 * (x * b + 1) + 2) ≤ 3 * x := by
  obtain rfl | hb := Nat.eq_zero_or_pos b
  · norm_num
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hb₁ : 1 ≤ (b : ℝ) := by exact_mod_cast hb
  have hxb : 1 ≤ x * b := one_le_mul_of_one_le_of_one_le (by linarith) hb₁
  calc
    _ ≤ log (6 * x * b) := log_le_log (by positivity) (by linarith)
    _ = log 6 + log x + log b := by
      rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity)]
    _ ≤ _ := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6),
      log_le_sub_one_of_pos (by linarith : 0 < x)]

/-- The logarithmic cost of a vacuum bound and a Gaussian factor at growth rate `x * b + 1`,
including the row-length correction. Here `q` is the cyclotomic order, `f` the number of
infinite places, and `n` and `n'` the two ranks. The row indices range over at most `f * n`
rows, each of length at most `2 * x * b`. -/
theorem vacuumJetLogCost_le {ι : Type*} {rows : Finset ι} {row : ι → ℕ}
    {q f n n' b : ℕ} {x C : ℝ} (hb : 3 ≤ log b) (hscale : log b ^ 100 ≤ x)
    (hC : C ≤ log b) (hq : (q : ℝ) ≤ x ^ 12) (hf : (f : ℝ) ≤ x ^ 12)
    (hn : (n : ℝ) ≤ x ^ 6) (hn' : (n' : ℝ) ≤ x ^ 6)
    (hcard : rows.card ≤ f * n) (hrow : ∀ i ∈ rows, (row i : ℝ) ≤ 2 * (x * b)) :
    C * ((q : ℝ) * (n' * (n : ℝ)) + 1) ^ 2 +
        (f : ℝ) * (n' * (n : ℝ)) * log (2 * (x * b + 1) + 2) +
        (∑ i ∈ rows, (row i : ℝ) / (x * b + 1)) / 2 ≤ x ^ 50 := by
  have hx : 8 ≤ x := (by norm_num : (8 : ℝ) ≤ 3 ^ 100).trans
    ((pow_le_pow_left₀ (by norm_num) hb 100).trans hscale)
  have hbx : log b ≤ x := (le_self_pow₀ (by linarith) (by decide : 100 ≠ 0)).trans hscale
  have hcount {p : ℕ} (hp : (p : ℝ) ≤ x ^ 12) : (p : ℝ) * (n' * (n : ℝ)) ≤ x ^ 24 := by
    calc
      _ ≤ x ^ 12 * (x ^ 6 * x ^ 6) := by gcongr
      _ = _ := by ring
  have hvac : C * ((q : ℝ) * (n' * (n : ℝ)) + 1) ^ 2 ≤ 4 * x ^ 49 := by
    calc
      _ ≤ x * (2 * x ^ 24) ^ 2 := by
        gcongr
        · exact hC.trans hbx
        · linarith [hcount hq, one_le_pow₀ (by linarith : 1 ≤ x) (n := 24)]
      _ = _ := by ring
  have hgauss : (f : ℝ) * (n' * (n : ℝ)) * log (2 * (x * b + 1) + 2) ≤ 3 * x ^ 25 := by
    calc
      _ ≤ x ^ 24 * (3 * x) := by
        have hxb : 0 ≤ x * (b : ℝ) := by positivity
        exact mul_le_mul (hcount hf) (log_gaussianScale_le (by linarith) hbx)
          (log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hrows : (∑ i ∈ rows, (row i : ℝ) / (x * b + 1)) / 2 ≤ x ^ 18 := by
    have hi (i) (hi : i ∈ rows) : (row i : ℝ) / (x * b + 1) ≤ 2 := by
      exact (div_le_iff₀ (by positivity)).mpr (by linarith [hrow i hi])
    have hsum := sum_le_sum hi
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcard' : (rows.card : ℝ) ≤ f * n := by exact_mod_cast hcard
    have hfn : (f : ℝ) * n ≤ x ^ 18 := by
      calc
        _ ≤ x ^ 12 * x ^ 6 := by gcongr
        _ = _ := by ring
    linarith [hcard'.trans hfn]
  have hx25 : x ^ 25 ≤ x ^ 49 := pow_le_pow_right₀ (by linarith) (by decide)
  have hx18 : x ^ 18 ≤ x ^ 49 := pow_le_pow_right₀ (by linarith) (by decide)
  have hx50 : 8 * x ^ 49 ≤ x ^ 50 := by
    rw [pow_succ' x 49]
    gcongr
  linarith

/-- At growth rate `x * b + 1`, the Gaussian vacuum factor is bounded by the exponential of
half the sum of the logarithmic jet sizes plus an error of `x ^ 50`. The logarithmic jet scale
`c` does not enter the error estimate. -/
theorem vacuumJetFactor_le {ι : Type*} {rows : Finset ι} {row : ι → ℕ}
    {q f n n' b : ℕ} {x C c : ℝ} (hb : 3 ≤ log b)
    (hscale : log b ^ 100 ≤ x) (hC : C ≤ log b) (hq : (q : ℝ) ≤ x ^ 12)
    (hf : (f : ℝ) ≤ x ^ 12) (hn : (n : ℝ) ≤ exp 12 * x ^ (11 / 2 : ℝ))
    (hn' : (n' : ℝ) ≤ exp 12 * x ^ (11 / 2 : ℝ))
    (hcard : rows.card ≤ f * n) (hrow : ∀ i ∈ rows, (row i : ℝ) ≤ 2 * (x * b)) :
    exp (C * ((q : ℝ) * (n' * (n : ℝ)) + 1) ^ 2 +
        (∑ i ∈ rows, ((row i : ℝ) / (x * b + 1) + jetSize c (row i))) / 2) *
        (2 * (x * b + 1) + 2) ^ (f * (n' * n)) ≤
      exp (x ^ 50 + (∑ i ∈ rows, jetSize c (row i)) / 2) := by
  have hL : 0 < log b := by linarith
  have hx : 0 < x := (pow_pos hL 100).trans_le hscale
  have hlogx : 100 ≤ log x := by
    have hlogL : 1 ≤ log (log b) := (le_log_iff_exp_le hL).mpr
      (Real.exp_one_lt_d9.le.trans (by linarith))
    have hlog := log_le_log (pow_pos hL 100) hscale
    rw [log_pow] at hlog
    norm_num at hlog
    linarith
  have hrank : exp 12 * x ^ (11 / 2 : ℝ) ≤ x ^ 6 := by
    have h12 : exp 12 ≤ x ^ (1 / 2 : ℝ) := by
      rw [rpow_def_of_pos hx]
      exact exp_le_exp.mpr (by linarith)
    calc
      _ ≤ x ^ (1 / 2 : ℝ) * x ^ (11 / 2 : ℝ) := by gcongr
      _ = x ^ 6 := by rw [← rpow_add hx]; norm_num
  have hcost := vacuumJetLogCost_le hb hscale hC hq hf
    (hn.trans hrank) (hn'.trans hrank) hcard hrow
  rw [← rpow_natCast (2 * (x * b + 1) + 2) (f * (n' * n)),
    rpow_def_of_pos (by positivity), ← exp_add, exp_le_exp, sum_add_distrib]
  push_cast
  linarith only [hcost, mul_comm (log (2 * (x * b + 1) + 2)) ((f : ℝ) * (n' * n))]

end TauCeti.OneSidedBound
