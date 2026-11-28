/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Data.Nat.Cast.SetInterval
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.NumberTheory.Bernoulli.Values
import TauCeti.NumberTheory.ZetaValues

/-!
# The asymptotic expansion of the harmonic sums

The Euler–Maclaurin formula applied to `x ↦ 1/x` gives the asymptotic expansion of the harmonic
sums (DLMF 2.10.8)

`∑_{j=1}^{n-1} 1/j ∼ log n + γ - 1/(2n) - ∑_{s ≥ 1} B_{2s} / (2s) · n^{-2s}` as `n → ∞`,

where `γ` is the Euler–Mascheroni constant and `B_{2s}` are the Bernoulli numbers. Writing
`B'_s` for Mathlib's `bernoulli'` (with `B'_1 = 1/2`, and `B'_s = B_s` otherwise), the series is
`log n + γ - ∑_{s ≥ 1} B'_s / s · n^{-s}`, since the odd `B'_s` with `s ≥ 3` vanish. The
expansion diverges, but the remainder after the terms up to `n^{-2m+2}` has the sign of the first
neglected term `-B_{2m} / (2m) · n^{-2m}` and is at most that term in absolute value.

## Main results

* `TauCeti.sum_Ico_inv_eq_log_add_eulerMascheroniConstant`: for `k ≥ 1` and `n ≥ 1`, the exact
  identity
  `∑_{j=1}^{n-1} 1/j = log n + γ - ∑_{s=1}^k B'_s / s · n^{-s} + ∫_n^∞ B_k({x}) / x^(k+1) dx`,
  with `B_k({x}) = bernoulliFun k (Int.fract x)` the periodic Bernoulli function. For `k = 1` it
  is a form of `TauCeti.eulerMascheroniConstant_eq_sum_sub_log_add_sawtooth` at integer points.
* `TauCeti.integrableOn_Ioi_bernoulliFun_fract_div_pow` and
  `TauCeti.isBigO_integral_Ioi_bernoulliFun_fract_div_pow`: the remainder integral converges and is
  `O(n^{-k})`.
* `TauCeti.hasAsymptoticExpansion_sum_Ico_inv_sub_log_sub_eulerMascheroniConstant`: the
  expansion, as `Asymptotics.HasAsymptoticExpansion` of `∑_{j=1}^{n-1} 1/j - log n - γ` in the
  scale `n^{-k}` along `atTop` with coefficients `-B'_k / k`.
* `TauCeti.exists_mem_Icc_sum_Ico_inv_eq`: DLMF 2.10.8 with its remainder enclosed: for `m ≥ 1`
  and `n ≥ 1` there is `θ ∈ [0, 1]` with
  `∑_{j=1}^{n-1} 1/j = log n + γ - 1/(2n) - ∑_{s=1}^{m-1} B_{2s} / (2s) · n^{-2s}
    - θ · B_{2m} / (2m) · n^{-2m}`.

The constant term is identified by letting `n → ∞` in the finite Euler–Maclaurin formula and
comparing with `Real.tendsto_harmonic_sub_log`. After the terms up to `n^{-2m+2}`, the remainder is
`∫_n^∞ (B_{2m}({x}) - B_{2m}) / x^(2m+1) dx`, whose integrand has the constant sign
`(-1)^m` by `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg`. The remainders after
`m - 1` and after `m` even terms then have opposite signs and differ by the first neglected term,
which encloses the former.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.8.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §§1–4.
-/

public section

open Finset MeasureTheory Filter Asymptotics
open scoped Nat Topology

namespace TauCeti

/-- The derivatives of `x ↦ 1/x`: `(-1)^i i! / x^(i+1)` has derivative
`(-1)^(i+1) (i+1)! / x^(i+2)` at every `x ≠ 0`. -/
private theorem hasDerivAt_neg_one_pow_mul_factorial_div_pow (i : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (-1) ^ i * i ! / y ^ (i + 1))
      ((-1) ^ (i + 1) * (i + 1)! / x ^ (i + 1 + 1)) x := by
  have h := ((hasDerivAt_pow (i + 1) x).inv (pow_ne_zero _ hx)).const_mul ((-1) ^ i * i ! : ℝ)
  convert h using 1
  · ext y
    simp [div_eq_mul_inv]
  · rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The Euler–Maclaurin term of order `s ≥ 2` for `x ↦ 1/x` on `[1, n]`:
`Bₛ/s! · (f^{(s-1)}(n) - f^{(s-1)}(1)) = B'ₛ/s · (1 - n^{-s})`. -/
private theorem bernoulli_div_factorial_mul_sub_eq {s : ℕ} (hs : 2 ≤ s) (y : ℝ) :
    (bernoulli s / s ! : ℝ) *
      ((-1) ^ (s - 1) * ((s - 1)! : ℕ) / y ^ (s - 1 + 1) - (-1) ^ (s - 1) * ((s - 1)! : ℕ)) =
      (bernoulli' s / s : ℝ) * (1 - y⁻¹ ^ s) := by
  have hs1 : s - 1 + 1 = s := by omega
  have hfac : (s ! : ℝ) = s * ((s - 1)! : ℕ) := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
  have hB : (bernoulli' s : ℝ) = (-1) ^ s * bernoulli s := by
    exact_mod_cast bernoulli'_eq_bernoulli s
  have hsign : ((-1 : ℝ) ^ s) = -(-1) ^ (s - 1) := by
    conv_lhs => rw [← hs1]
    ring
  have : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : ((s - 1)! : ℝ) ≠ 0 := by positivity
  rw [hs1, div_eq_mul_inv _ (y ^ s), ← inv_pow, hB, hfac, hsign]
  field_simp
  ring

/-- The Euler–Maclaurin formula of order `k ≥ 1` for `x ↦ 1/x` on `[1, n]`, rearranged:
`∑_{j=1}^{n-1} 1/j = log n + ∑_{s=1}^k B'ₛ/s · (1 - n^{-s}) - ∫_1^n Bₖ({x}) / x^(k+1) dx`. -/
private theorem sum_Ico_inv_eq_log_add_sum_sub_intervalIntegral {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ = Real.log n +
      ∑ s ∈ Icc 1 k, (bernoulli' s / s : ℝ) * (1 - (n : ℝ)⁻¹ ^ s) -
      ∫ x in (1 : ℝ)..n, bernoulliFun k (Int.fract x) / x ^ (k + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcont : ∀ i : ℕ, ContinuousOn (fun y : ℝ => (-1) ^ i * i ! / y ^ (i + 1))
      (Set.Icc ((1 : ℤ) : ℝ) ((n : ℤ) : ℝ)) := fun i x hx => by
    have hx0 : x ≠ 0 := by simp at hx; linarith [hx.1]
    exact (continuousAt_const.div (continuousAt_pow _ _) (pow_ne_zero _ hx0)).continuousWithinAt
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt
    (g := fun i y => (-1) ^ i * i ! / y ^ (i + 1)) (by exact_mod_cast hn) hk
    (fun i _ => hcont i)
    (fun i _ x hx => hasDerivAt_neg_one_pow_mul_factorial_div_pow i (by simp at hx; linarith))
    ((hcont k).intervalIntegrable_of_Icc (by simpa using hn'))
  -- Pass from the integer interval `[1, n]` to the natural one, and evaluate `∫_1^n 1/x`.
  have hmap : (Icc 1 n).map Nat.castEmbedding = Icc (1 : ℤ) n := by
    simpa [← Finset.coe_inj] using Nat.image_cast_int_Icc 1 n
  rw [← hmap, sum_map] at hEM
  simp only [Nat.castEmbedding_apply, Int.cast_natCast, Int.cast_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_mul, zero_add, pow_one, one_div, one_pow, div_one, smul_eq_mul] at hEM
  rw [integral_inv_of_pos one_pos (by linarith), div_one,
    sum_congr rfl fun s hs => bernoulli_div_factorial_mul_sub_eq (mem_Icc.mp hs).1 n,
    ← intervalIntegral.integral_const_mul] at hEM
  -- The remainder: `(-1)^k/k! · ∫ Bₖ({x}) · (-1)^k k!/x^(k+1) = ∫ Bₖ({x})/x^(k+1)`.
  have hR : ∫ x in (1 : ℝ)..n, (-1) ^ k / (k ! : ℝ) *
        (bernoulliFun k (Int.fract x) * ((-1) ^ k * (k ! : ℝ) / x ^ (k + 1))) =
      ∫ x in (1 : ℝ)..n, bernoulliFun k (Int.fract x) / x ^ (k + 1) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hk! : (k ! : ℝ) ≠ 0 := by positivity
    have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    calc _ = ((-1) ^ k * (-1) ^ k) * ((k ! : ℝ) / k !) *
          (bernoulliFun k (Int.fract x) / x ^ (k + 1)) := by ring
      _ = _ := by rw [hsq, div_self hk!, one_mul, one_mul]
  have hIcc : ∑ j ∈ Icc 1 n, (j : ℝ)⁻¹ = ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ + (n : ℝ)⁻¹ := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top hn]
  rw [hR, hIcc] at hEM
  -- The `s = 1` term `B'₁ (1 - 1/n) = (1 - 1/n)/2` combines the endpoint terms with `-1/n`.
  rw [← add_sum_Ioc_eq_sum_Icc hk, ← Finset.Icc_add_one_left_eq_Ioc, bernoulli'_one]
  push_cast
  linarith

/-- For `k ≥ 1` and `c > 0`, the remainder integrand `Bₖ({x}) / x^(k+1)` of the harmonic sums is
integrable on `(c, ∞)`, where `Bₖ({x})` is the periodic Bernoulli function. -/
theorem integrableOn_Ioi_bernoulliFun_fract_div_pow {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x => bernoulliFun k (Int.fract x) / x ^ (k + 1)) (Set.Ioi c) := by
  obtain ⟨M, hM⟩ := exists_norm_bernoulliFun_fract_le k
  simp only [div_eq_mul_inv]
  exact (integrableOn_Ioi_inv_pow_succ hk hc).bdd_mul
    ((continuous_bernoulliFun k).measurable.comp measurable_fract).aestronglyMeasurable
    (Eventually.of_forall hM)

/-- **The harmonic sums by the Euler–Maclaurin formula.** For `k ≥ 1` and `n ≥ 1`,
`∑_{j=1}^{n-1} 1/j = log n + γ - ∑_{s=1}^k B'_s / s · n^{-s} + ∫_n^∞ Bₖ({x}) / x^(k+1) dx`,
where `B'_s = bernoulli' s` (so `B'_1 = 1/2`), `γ` is the Euler–Mascheroni constant and `Bₖ({x})`
is the periodic Bernoulli function. -/
theorem sum_Ico_inv_eq_log_add_eulerMascheroniConstant {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ = Real.log n + Real.eulerMascheroniConstant -
      ∑ s ∈ Icc 1 k, (bernoulli' s / s : ℝ) * (n : ℝ)⁻¹ ^ s +
      ∫ x in Set.Ioi (n : ℝ), bernoulliFun k (Int.fract x) / x ^ (k + 1) := by
  set r : ℝ → ℝ := fun x => bernoulliFun k (Int.fract x) / x ^ (k + 1)
  have hint := integrableOn_Ioi_bernoulliFun_fract_div_pow hk one_pos
  -- `γ = ∑ B'ₛ/s - ∫_1^∞ r`, by letting `n → ∞` in the finite identity.
  have hγ : Real.eulerMascheroniConstant =
      ∑ s ∈ Icc 1 k, (bernoulli' s / s : ℝ) - ∫ x in Set.Ioi (1 : ℝ), r x := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h₁ : Tendsto (fun n : ℕ => ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ - Real.log n) atTop
        (𝓝 Real.eulerMascheroniConstant) := by
      have := Real.tendsto_harmonic_sub_log.sub (tendsto_inv_atTop_zero.comp hnat)
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [harmonic_eq_sum_Icc, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top hn]
        push_cast
        simp only [Function.comp_apply]
        ring
    have h₂ : Tendsto (fun n : ℕ => ∑ s ∈ Icc 1 k, (bernoulli' s / s : ℝ) * (1 - (n : ℝ)⁻¹ ^ s) -
        ∫ x in (1 : ℝ)..n, r x) atTop
        (𝓝 (∑ s ∈ Icc 1 k, (bernoulli' s / s : ℝ) - ∫ x in Set.Ioi (1 : ℝ), r x)) := by
      refine Tendsto.sub ?_ (intervalIntegral_tendsto_integral_Ioi 1 hint hnat)
      refine tendsto_finsetSum _ fun s hs => ?_
      have hs0 : s ≠ 0 := by simp at hs; omega
      have := ((tendsto_inv_atTop_zero.comp hnat).pow s).const_sub 1
      rw [zero_pow hs0, sub_zero] at this
      simpa using this.const_mul (bernoulli' s / s : ℝ)
    refine tendsto_nhds_unique h₁ (h₂.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [sum_Ico_inv_eq_log_add_sum_sub_intervalIntegral hk hn]
    ring
  rw [sum_Ico_inv_eq_log_add_sum_sub_intervalIntegral hk hn, hγ,
    ← intervalIntegral.integral_Ioi_sub_Ioi hint (by exact_mod_cast hn)]
  simp only [mul_sub, mul_one, sum_sub_distrib]
  ring

/-- For `k ≥ 1`, the remainder `∫_n^∞ Bₖ({x}) / x^(k+1) dx` of the harmonic sums is `O(n^{-k})`
as `n → ∞`: it is at most `M / (k n^k)` when `|Bₖ| ≤ M` on `[0, 1]`. -/
theorem isBigO_integral_Ioi_bernoulliFun_fract_div_pow {k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℕ => ∫ x in Set.Ioi (n : ℝ), bernoulliFun k (Int.fract x) / x ^ (k + 1)) =O[atTop]
      fun n : ℕ => (n : ℝ)⁻¹ ^ k := by
  obtain ⟨M, hM⟩ := exists_norm_bernoulliFun_fract_le k
  refine IsBigO.of_bound (M / k) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := norm_integral_le_of_norm_le
    (f := fun x => bernoulliFun k (Int.fract x) / x ^ (k + 1))
    ((integrableOn_Ioi_inv_pow_succ hk hn0).const_mul M)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x (hx : (n : ℝ) < x) => by
      have hx0 : 0 < x ^ (k + 1) := pow_pos (hn0.trans hx) _
      rw [norm_div, Real.norm_of_nonneg hx0.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hM x) hx0.le))
  rw [integral_const_mul, integral_Ioi_inv_pow_succ hk hn0, mul_inv, ← mul_assoc,
    ← div_eq_mul_inv] at h
  rwa [norm_pow, norm_inv, Real.norm_natCast, inv_pow]

/-- **The asymptotic expansion of the harmonic sums** (DLMF 2.10.8). As `n → ∞`,
`∑_{j=1}^{n-1} 1/j - log n - γ ∼ ∑_{k ≥ 0} -B'_k / k · n^{-k}`
in the scale `n^{-k}`, where `B'_k = bernoulli' k`; the coefficient at `k = 0` is `0` (Lean's
`B'_0 / 0 = 0`), the one at `k = 1` is `-1/2`, and those at odd `k ≥ 3` vanish. -/
theorem hasAsymptoticExpansion_sum_Ico_inv_sub_log_sub_eulerMascheroniConstant :
    HasAsymptoticExpansion atTop (fun k (n : ℕ) => (n : ℝ)⁻¹ ^ k)
      (fun k => -(bernoulli' k / k : ℝ))
      (fun n => ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ - Real.log n - Real.eulerMascheroniConstant) := by
  have hscale := isAsymptoticScale_pow (l := (atTop : Filter ℕ)) (w := fun n : ℕ => (n : ℝ)⁻¹)
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  -- The remainder after the terms `k ≤ N` is `-B'_{N+1}/(N+1) n^{-N-1} + ∫_n^∞ B_{N+1}({x})/…`.
  refine HasAsymptoticExpansion.of_isLittleO fun N => ?_
  refine IsBigO.trans_isLittleO ?_ (hscale.isLittleO N)
  have hB := (isBigO_integral_Ioi_bernoulliFun_fract_div_pow (k := N + 1) (by omega)).sub
    ((isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹ ^ (N + 1)) atTop).const_mul_left
      (bernoulli' (N + 1) / (N + 1 : ℕ) : ℝ))
  refine hB.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sum_Ico_inv_eq_log_add_eulerMascheroniConstant (k := N + 1) (by omega) hn,
    sum_range_eq_add_Ico _ (by omega), ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_succ_top (by omega : 1 ≤ N + 1)]
  simp only [smul_eq_mul, CharP.cast_eq_zero, div_zero, neg_zero, mul_zero, zero_add,
    mul_neg, sum_neg_distrib]
  simp only [mul_comm ((n : ℝ)⁻¹ ^ _)]
  ring

/-- DLMF 2.10.8 truncated after `m` even terms, with its exact remainder:
`∑_{j=1}^{n-1} 1/j = log n + γ - 1/(2n) - ∑_{s=1}^{m-1} B_{2s}/(2s) · n^{-2s}
  + ∫_n^∞ (B_{2m}({x}) - B_{2m}) / x^(2m+1) dx`. -/
private theorem sum_Ico_inv_eq_sub_sum_add_integral {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ = Real.log n + Real.eulerMascheroniConstant - (2 * n : ℝ)⁻¹ -
      ∑ s ∈ Ico 1 m, (bernoulli (2 * s) / (2 * s) : ℝ) * (n : ℝ)⁻¹ ^ (2 * s) +
      ∫ x in Set.Ioi (n : ℝ),
        (bernoulliFun (2 * m) (Int.fract x) - bernoulli (2 * m)) / x ^ (2 * m + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2m : 1 ≤ 2 * m := by omega
  -- Split off `∫_n^∞ B_{2m} / x^(2m+1) dx = B_{2m} / (2m n^{2m})`.
  have hsub : ∫ x in Set.Ioi (n : ℝ),
        (bernoulliFun (2 * m) (Int.fract x) - bernoulli (2 * m)) / x ^ (2 * m + 1) =
      (∫ x in Set.Ioi (n : ℝ), bernoulliFun (2 * m) (Int.fract x) / x ^ (2 * m + 1)) -
        (bernoulli (2 * m) / (2 * m) : ℝ) * (n : ℝ)⁻¹ ^ (2 * m) := by
    have h := integral_sub (integrableOn_Ioi_bernoulliFun_fract_div_pow h2m hn0)
      ((integrableOn_Ioi_inv_pow_succ h2m hn0).const_mul (bernoulli (2 * m) : ℝ))
    rw [integral_const_mul, integral_Ioi_inv_pow_succ h2m hn0] at h
    simp only [sub_div, ← div_eq_mul_inv] at h ⊢
    rw [h, inv_pow]
    push_cast
    field_simp
  rw [hsub, sum_Ico_inv_eq_log_add_eulerMascheroniConstant h2m hn,
    sum_Icc_two_mul_bernoulli'_div_mul_pow hm, ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_succ_top hm]
  ring

/-- The remainder `∫_c^∞ (B_{2m}({x}) - B_{2m}) / x^(2m+1) dx` has the sign `(-1)^m`. -/
private theorem neg_one_pow_mul_integral_nonneg (m : ℕ) {c : ℝ} (hc : 0 < c) :
    0 ≤ (-1) ^ m * ∫ x in Set.Ioi c,
      (bernoulliFun (2 * m) (Int.fract x) - bernoulli (2 * m)) / x ^ (2 * m + 1) := by
  rw [← integral_const_mul]
  refine setIntegral_nonneg measurableSet_Ioi fun x (hx : c < x) => ?_
  have h := neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg m
    (x := Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← mul_div_assoc]
  refine div_nonneg ?_ (pow_pos (hc.trans hx) _).le
  convert h using 1
  ring

/-- **The harmonic sums with an enclosed remainder** (DLMF 2.10.8). For `m ≥ 1` and `n ≥ 1`,
truncating the expansion
`∑_{j=1}^{n-1} 1/j ∼ log n + γ - 1/(2n) - ∑_{s ≥ 1} B_{2s}/(2s) · n^{-2s}`
before the term of order `n^{-2m}` leaves a remainder `-θ · B_{2m}/(2m) · n^{-2m}` with
`θ ∈ [0, 1]`: it has the sign of the first neglected term and is at most that term in absolute
value. -/
theorem exists_mem_Icc_sum_Ico_inv_eq {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      ∑ j ∈ Ico 1 n, (j : ℝ)⁻¹ = Real.log n + Real.eulerMascheroniConstant - (2 * n : ℝ)⁻¹ -
        ∑ s ∈ Ico 1 m, (bernoulli (2 * s) / (2 * s) : ℝ) * (n : ℝ)⁻¹ ^ (2 * s) -
        θ * ((bernoulli (2 * m) / (2 * m) : ℝ) * (n : ℝ)⁻¹ ^ (2 * m)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set R : ℕ → ℝ := fun m => ∫ x in Set.Ioi (n : ℝ),
    (bernoulliFun (2 * m) (Int.fract x) - bernoulli (2 * m)) / x ^ (2 * m + 1) with hR
  set T : ℝ := (bernoulli (2 * m) / (2 * m) : ℝ) * (n : ℝ)⁻¹ ^ (2 * m) with hT
  -- The remainders after `m - 1` and after `m` even terms differ by the neglected term `-T`.
  have hrec : R m = R (m + 1) - T := by
    have h₁ := sum_Ico_inv_eq_sub_sum_add_integral hm hn
    have h₂ := sum_Ico_inv_eq_sub_sum_add_integral (m := m + 1) (by omega) hn
    rw [sum_Ico_succ_top hm] at h₂
    simp only [hR, hT]
    linarith
  -- `(-1)^m (-T) > 0`, while `(-1)^m R m ≥ 0` and `(-1)^(m+1) R (m+1) ≥ 0`.
  have hTpos : 0 < (-1) ^ m * (-T) := by
    have hB : (0 : ℝ) < (-1) ^ (m + 1) * bernoulli (2 * m) := by
      exact_mod_cast neg_one_pow_mul_bernoulli_two_mul_pos (k := m) (by omega)
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) < (2 * m : ℝ)⁻¹ * (n : ℝ)⁻¹ ^ (2 * m) := by positivity
    convert mul_pos hB this using 1
    simp only [hT]
    ring
  have hRm := neg_one_pow_mul_integral_nonneg m hn0
  have hRm' := neg_one_pow_mul_integral_nonneg (m + 1) hn0
  rw [pow_succ] at hRm'
  have hsign : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero m (by norm_num)
  refine ⟨R m / -T, ⟨?_, ?_⟩, ?_⟩
  · rw [← mul_div_mul_left _ _ hsign]
    exact div_nonneg hRm hTpos.le
  · rw [← mul_div_mul_left _ _ hsign, div_le_one hTpos, hrec]
    nlinarith
  · have hT0 : T ≠ 0 := fun h => by simp [h] at hTpos
    rw [sum_Ico_inv_eq_sub_sum_add_integral hm hn]
    field_simp
    ring

end TauCeti
