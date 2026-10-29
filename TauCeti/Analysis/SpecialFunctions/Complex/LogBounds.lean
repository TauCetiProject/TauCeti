/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Taylor series bounds for `-log (1 - ·)`

Mathlib's `Complex.hasSum_taylorSeries_neg_log'` expands `-log (1 - z)` as `∑' e, z ^ (e+1)/(e+1)`
for a single `z` of modulus less than one.  This file first sums that over a family `r : ι → ℂ`: the
double family indexed by `ι × ℕ` is summable, so the sum may be regrouped fibrewise and the
prime-power-style sum over pairs equals the sum of local logarithms.

Both hypotheses are needed.  `∀ i, ‖r i‖ < 1` alone does not suffice: the fibre at `i` sums to
`‖r i‖ / (1 - ‖r i‖)`, which is dominated by `‖r i‖` only when `‖r i‖` is bounded away from `1`,
and summability of `r` is what supplies that uniformity.  That fibrewise argument is not carried out
here: it is `TauCeti.summable_mul_norm_pow_succ`, stated for a seminormed additive group and an
arbitrary real weight, and this file uses it at weight `1`.

The file also gives an explicit truncation error for a single `z`: the `n`-th partial sum
`∑ j ∈ Icc 1 n, z ^ j / j` differs from `log (1 - z)⁻¹` by at most
`‖z‖ ^ (n + 1) / ((1 - ‖z‖) (n + 1))`, which restates Mathlib's
`Complex.norm_log_one_sub_inv_add_logTaylor_neg_le` with the Taylor polynomial written out.  At
`z = w / p`, for `‖w‖ ≤ 1` and a natural number `p ≥ 2`, this becomes `2 / p ^ (n + 1)`, and the
factor `1 - w / p` is nonzero.  These are the estimates used to compare an Euler factor
`(1 - w / p)⁻¹` with the prime-power partial sums of its logarithm.

## Main results

* `Complex.summable_taylorSeries_neg_log`: for a summable `r : ι → ℂ` with every `‖r i‖ < 1`, the
  family `(i, e) ↦ r i ^ (e + 1) / (e + 1)` is summable over `ι × ℕ`.
* `Complex.tsum_taylorSeries_neg_log`: its sum over `ι × ℕ` is `∑' i, -log (1 - r i)`.
* `Complex.norm_log_one_sub_inv_sub_sum_Icc_le`: the truncation error of the same Taylor series
  for a single `z`, with its `n`-th partial sum `∑ j ∈ Icc 1 n, z ^ j / j`.
* `Complex.norm_log_one_sub_div_inv_sub_sum_Icc_le`: the same truncation error at `z = w / p`,
  for `‖w‖ ≤ 1` and a natural number `p ≥ 2`, bounded by `2 / p ^ (n + 1)`.
* `Complex.one_sub_div_natCast_ne_zero`: for `‖w‖ ≤ 1` and a natural number `p > 1`, the factor
  `1 - w / p` is nonzero.
-/

public section

namespace Complex

/-- **The Taylor family of `-log (1 - rᵢ)` is summable over index and exponent together.**  For a
summable family `r` of complex numbers, all of modulus less than one, the double family
`(i, e) ↦ rᵢ ^ (e + 1) / (e + 1)` is absolutely summable, so its sum may be taken fibrewise.

Both hypotheses are needed, and neither is arithmetic: see the module docstring for why
`∀ i, ‖r i‖ < 1` alone does not suffice. -/
theorem summable_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    Summable fun ie : ι × ℕ ↦ r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) := by
  -- The majorant is the weighted geometric bound at weight `1`; summability of `r` supplies its
  -- eventual bound with `ε = 1 / 2`.
  have hhalf : ∀ᶠ i in Filter.cofinite, ‖r i‖ ≤ 1 / 2 :=
    hr.tendsto_cofinite_zero.norm.eventually_le_const (by norm_num)
  have hbd : ∃ ε > 0, ∀ᶠ i in Filter.cofinite, (1 : ℝ) ≠ 0 → ‖r i‖ ≤ 1 - ε :=
    ⟨1 / 2, by norm_num, by filter_upwards [hhalf] with i hi _; linarith⟩
  have hmaj : Summable fun ie : ι × ℕ ↦ ‖r ie.1‖ ^ (ie.2 + 1) := by
    simpa using TauCeti.summable_mul_norm_pow_succ (w := fun _ ↦ (1 : ℝ)) hbd
      (by simpa using hr.norm) (fun i _ ↦ h1 i)
  refine hmaj.of_norm_bounded ?_
  rintro ⟨i, e⟩
  rw [norm_div, norm_pow]
  refine div_le_self (by positivity) ?_
  have hcast : ((e : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_natCast]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le e)


/-- **The double sum is the sum of the local logarithms.**  For a summable `r : ι → ℂ` with every
`‖r i‖ < 1`, summing the Taylor series of `-log (1 - r i)` over `ι × ℕ` gives `∑' i, -log (1 - r i)`
— the fibrewise regrouping that `summable_taylorSeries_neg_log` licenses. -/
theorem tsum_taylorSeries_neg_log {ι : Type*} {r : ι → ℂ} (hr : Summable r)
    (h1 : ∀ i, ‖r i‖ < 1) :
    ∑' ie : ι × ℕ, r ie.1 ^ (ie.2 + 1) / ((ie.2 : ℂ) + 1) = ∑' i, -Complex.log (1 - r i) := by
  have hfib : ∀ i, HasSum (fun e : ℕ ↦ r i ^ (e + 1) / ((e : ℂ) + 1))
      (-Complex.log (1 - r i)) := fun i ↦ hasSum_taylorSeries_neg_log' (h1 i)
  exact ((summable_taylorSeries_neg_log hr h1).hasSum.prod_fiberwise hfib).tsum_eq.symm

/-- **The truncation error of the Taylor series of `log (1 - z)⁻¹`.** For `‖z‖ < 1`, the partial
sum `∑ j ∈ Icc 1 n, z ^ j / j` approximates `log (1 - z)⁻¹ = -log (1 - z)` to within
`‖z‖ ^ (n + 1) / ((1 - ‖z‖) (n + 1))`. This restates Mathlib's
`Complex.norm_log_one_sub_inv_add_logTaylor_neg_le` with the Taylor polynomial written out. -/
theorem norm_log_one_sub_inv_sub_sum_Icc_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ - ∑ j ∈ Finset.Icc 1 n, z ^ j / j‖ ≤
      ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  have hT : ∀ n : ℕ, logTaylor (n + 1) (-z) = -∑ j ∈ Finset.Icc 1 n, z ^ j / j := by
    intro n
    induction n with
    | zero => simp [logTaylor_succ, logTaylor_zero]
    | succ n ih =>
      rw [logTaylor_succ, Pi.add_apply, ih, Finset.sum_Icc_succ_top (by lia), neg_pow z]
      have : ((-1 : ℂ) ^ (n + 1 + 1) * (-1) ^ (n + 1)) = -1 := by
        rw [← pow_add, show n + 1 + 1 + (n + 1) = 2 * (n + 1) + 1 by ring, pow_succ, pow_mul]
        simp
      linear_combination (z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) * this
  simpa [hT, sub_eq_add_neg] using norm_log_one_sub_inv_add_logTaylor_neg_le n hz

/-- For `2 ≤ p` and `‖w‖ ≤ 1`, the partial sum of the Taylor series of `log (1 - w / p)⁻¹` up to
degree `K` is within `2 / p ^ (K + 1)` of it. This is the local comparison at a single prime in an
Euler product with coefficients of modulus at most one. -/
theorem norm_log_one_sub_div_inv_sub_sum_Icc_le {p : ℕ} (hp : 2 ≤ p) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (K : ℕ) :
    ‖log (1 - w / p)⁻¹ - ∑ k ∈ Finset.Icc 1 K, (w / p) ^ k / k‖ ≤
      2 * ((p : ℝ) ^ (K + 1))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp
  have hz : ‖w / p‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_div, norm_natCast, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) hw
  have hz1 : ‖w / p‖ ≤ 1 / 2 := hz.trans (by rw [one_div]; gcongr)
  have hpos : 0 < 1 - ‖w / p‖ := by linarith
  refine (norm_log_one_sub_inv_sub_sum_Icc_le K (by linarith)).trans ?_
  have h2 : (1 - ‖w / p‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos two_pos]
    linarith
  calc ‖w / p‖ ^ (K + 1) * (1 - ‖w / p‖)⁻¹ / (K + 1)
      ≤ ‖w / p‖ ^ (K + 1) * (1 - ‖w / p‖)⁻¹ :=
        div_le_self (by have := inv_pos.mpr hpos; positivity) (by simp)
    _ ≤ ((p : ℝ)⁻¹) ^ (K + 1) * 2 := by gcongr
    _ = 2 * ((p : ℝ) ^ (K + 1))⁻¹ := by rw [inv_pow, mul_comm]

/-- For `1 < p` and `‖w‖ ≤ 1`, the Euler factor `1 - w / p` is nonzero. -/
theorem one_sub_div_natCast_ne_zero {p : ℕ} (hp : 1 < p) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1 - w / p ≠ 0 := by
  refine sub_ne_zero.mpr fun h ↦ ?_
  have h1 : ‖w / p‖ = 1 := by rw [← h, norm_one]
  have h2 : (1 : ℝ) < p := mod_cast hp
  rw [norm_div, norm_natCast, div_eq_one_iff_eq (by positivity)] at h1
  linarith

end Complex
