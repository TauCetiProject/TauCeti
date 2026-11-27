/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Binomial
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Cast.SetInterval
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.MellinTransform.UpperTail
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ZetaValues
import TauCeti.RingTheory.Binomial

/-!
# The asymptotic expansion of the power sums

For complex `α ≠ -1`, the power sums `∑_{j=1}^{n-1} j^α` have the expansion (DLMF 2.10.7)

`∑_{j=1}^{n-1} j^α ∼ ζ(-α) + n^(α+1)/(α+1) · ∑_{s ≥ 0} C(α+1, s) Bₛ n^(-s)` as `n → ∞`,

where `ζ` is the Riemann zeta function, `C(α+1, s)` is the generalized binomial coefficient
`Ring.choose (α + 1) s` and `Bₛ = bernoulli s` (with `B₁ = -1/2`). The expansion is with respect
to the scale `n^(α+1-s)` together with the constant term `ζ(-α)`: after subtracting `ζ(-α)`, the
difference is an asymptotic expansion in the scale `n^(α+1-s)` in the sense of
`Asymptotics.HasAsymptoticExpansion`. For `Re α < -1` the constant `ζ(-α)` is the sum of the
series, and the expansion describes its tail; for `Re α > -1` the sums diverge and `ζ(-α)` is the
value of the analytic continuation of `ζ`.

For real `α` the expansion has an enclosed remainder: truncated after the term `s = 2m - 1`,
where `α ≤ 2m - 1`, the remainder has the sign of the first neglected term `s = 2m` and is at most
that term in absolute value.

## Main results

* `TauCeti.sum_Ico_cpow_eq_riemannZeta_add`: for `n ≥ 1`, `k ≥ 1` and `α ≠ -1` with
  `Re α < k - 1`, the exact identity
  `∑_{j=1}^{n-1} j^α = ζ(-α) + ∑_{s=0}^k C(α+1, s) Bₛ/(α+1) · n^(α+1-s)
    + (-1)^k C(α, k) ∫_n^∞ Bₖ({x}) x^(α-k) dx`,
  with `Bₖ({x}) = bernoulliFun k (Int.fract x)` the periodic Bernoulli function.
* `TauCeti.integrableOn_Ioi_bernoulliFun_fract_mul_cpow` and
  `TauCeti.norm_integral_bernoulliFun_fract_mul_cpow_le`: the remainder integral converges
  absolutely and is at most `M n^(Re α + 1 - k) / (k - 1 - Re α)` in norm when `|Bₖ| ≤ M` on
  `[0, 1]`.
* `TauCeti.hasAsymptoticExpansion_sum_Ico_cpow_sub_riemannZeta`: the expansion, as
  `Asymptotics.HasAsymptoticExpansion` of `∑_{j=1}^{n-1} j^α - ζ(-α)` in the scale `n^(α+1-s)`
  with coefficients `C(α+1, s) Bₛ / (α+1)`, together with
  `TauCeti.isAsymptoticScale_natCast_cpow_sub`, the scale property.
* `TauCeti.exists_mem_Icc_sum_Ico_cpow_eq`: for real `α ≠ -1` and `α ≤ 2m - 1`, the truncation
  after the term `s = 2m - 1` leaves `θ` times the term `s = 2m`, with `θ ∈ [0, 1]`.

## Implementation notes

The Euler–Maclaurin formula of order `k` (`TauCeti.sum_Icc_eq_eulerMaclaurin_of_hasDerivAt`)
applied to `x ↦ x^α` on `[n, N]`, whose derivatives are `i! C(α, i) x^(α-i)`
(`TauCeti.hasDerivAt_factorial_mul_choose_mul_cpow`), gives the identity
with `∑_{j=n}^{N-1}` in place of `ζ(-α) - ∑_{j=1}^{n-1}`. For `Re α < -1` letting `N → ∞` gives
the identity, the sums tending to `ζ(-α)`. Both sides are holomorphic in `α` on `Re α < k - 1`
once the pole of `ζ(-α)` at `α = -1` is cancelled against that of `n^(α+1)/(α+1)`, so the identity
theorem extends it; the coefficients `C(α, k)` are entire in `α` by
`TauCeti.differentiable_ringChoose`. The remainder integral is `O(n^(Re α + 1 - k))`, which gives
the expansion.

For the enclosure, the remainders after the terms up to `s = 2m - 1` and up to `s = 2m + 1` are
`C(α, 2m) ∫_n^∞ (B_{2m}({x}) - B_{2m}) x^(α-2m) dx` and its analogue for `m + 1`. The integrands
have the constant signs `(-1)^m` and `(-1)^(m+1)` by
`TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg`, while `C(α, 2m + 2)` is `C(α, 2m)`
times a positive factor; so the two remainders lie on opposite sides of `0` and differ by the term
`s = 2m` (the term `s = 2m + 1` vanishes), which encloses the first of them.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.7.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §§1–4.
-/

public section

open Finset MeasureTheory Filter Asymptotics Complex
open scoped Nat Topology

namespace TauCeti

/-! ### Preliminaries -/

/-- The kernel `x^(α - k)` of the remainder written as `x^(-(s + 1))` with `s = k - 1 - α`. -/
private theorem cpow_sub_natCast_eq (α : ℂ) (k : ℕ) (x : ℝ) :
    (x : ℂ) ^ (α - k) = (x : ℂ) ^ (-(((k : ℂ) - 1 - α) + 1)) := by
  congr 1
  ring

/-- For `Re α < k - 1` and `c > 0`, the remainder integrand `Bₖ({x}) x^(α - k)` is integrable on
`(c, ∞)`, where `Bₖ({x})` is the periodic Bernoulli function. -/
theorem integrableOn_Ioi_bernoulliFun_fract_mul_cpow {k : ℕ} {α : ℂ} (hα : α.re < k - 1)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k))
      (Set.Ioi c) := by
  obtain ⟨M, hM⟩ := exists_norm_bernoulliFun_fract_le k
  simp_rw [cpow_sub_natCast_eq α k]
  exact integrableOn_mul_cpow_of_bound hc
    ((continuous_ofReal.comp (continuous_bernoulliFun k)).measurable.comp
      measurable_fract).aestronglyMeasurable (fun x _ => by simpa using hM x)
    (by simp; linarith)

/-- For `c > 0` and `Re α < k - 1`, the remainder integral `∫_c^∞ Bₖ({x}) x^(α - k) dx` is at
most `M c^(Re α + 1 - k) / (k - 1 - Re α)` in norm, where `|Bₖ({x})| ≤ M`. -/
theorem norm_integral_bernoulliFun_fract_mul_cpow_le {k : ℕ} {α : ℂ} (hα : α.re < k - 1)
    {M : ℝ} (hM : ∀ x : ℝ, ‖bernoulliFun k (Int.fract x)‖ ≤ M) {c : ℝ} (hc : 0 < c) :
    ‖∫ x in Set.Ioi c, (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k)‖ ≤
      M * c ^ (α.re + 1 - k) / (k - 1 - α.re) := by
  simp_rw [cpow_sub_natCast_eq α k]
  have h := norm_integral_mul_cpow_le_of_bound
    (g := fun x : ℝ => (bernoulliFun k (Int.fract x) : ℂ)) hc (fun x _ => by simpa using hM x)
    (s := (k : ℂ) - 1 - α) (by simp; linarith)
  convert h using 3
  congr 1
  simp only [sub_re, natCast_re, one_re]
  ring

/-! ### The identity for `Re α < -1` -/

/-- The terms of the expansion of `∑_{j=1}^{n-1} j^α` up to order `k` at the point `x`, without
the constant term: `x^(α+1)/(α+1) + ∑_{s=1}^k C(α, s-1) Bₛ/s · x^(α+1-s)`. -/
private noncomputable def powerSumPart (α : ℂ) (k : ℕ) (x : ℂ) : ℂ :=
  x ^ (α + 1) / (α + 1) + ∑ s ∈ Icc 1 k, x ^ (α + 1 - s) * (Ring.choose α (s - 1) * bernoulli s / s)

/-- The Euler–Maclaurin term of order `s ≥ 1` for `x ↦ x^α` between `y` and `x`:
`Bₛ/s! · ((s-1)! C(α, s-1) x^(α-(s-1)) - (s-1)! C(α, s-1) y^(α-(s-1)))` is the difference of the
terms `C(α, s-1) Bₛ/s · x^(α+1-s)` of `powerSumPart`. -/
private theorem bernoulli_div_factorial_mul_sub_eq (α : ℂ) {s : ℕ} (hs : 1 ≤ s) (x y : ℂ) :
    ((bernoulli s / s ! : ℝ) : ℂ) * (((s - 1)! : ℂ) * Ring.choose α (s - 1) *
        x ^ (α - ((s - 1 : ℕ) : ℂ)) - ((s - 1)! : ℂ) * Ring.choose α (s - 1) *
        y ^ (α - ((s - 1 : ℕ) : ℂ))) =
      x ^ (α + 1 - s) * (Ring.choose α (s - 1) * bernoulli s / s) -
        y ^ (α + 1 - s) * (Ring.choose α (s - 1) * bernoulli s / s) := by
  have hexp : α - ((s - 1 : ℕ) : ℂ) = α + 1 - s := by rw [Nat.cast_sub hs]; push_cast; ring
  have hfac : (s ! : ℂ) = s * ((s - 1)! : ℕ) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred (by omega)]
  have hs0 : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hf0 : ((s - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hexp]
  push_cast
  rw [hfac]
  field_simp

/-- The Euler–Maclaurin formula for `x ↦ x^α` on `[n, N]`:
`∑_{j=n}^{N-1} j^α = P(N) - P(n) - (-1)^k C(α, k) ∫_n^N Bₖ({x}) x^(α-k) dx`, where `P` is
`powerSumPart α k`. -/
private theorem sum_Ico_cpow_eq_powerSumPart_sub {α : ℂ} (hα : α ≠ -1) {k : ℕ} (hk : 1 ≤ k)
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ j ∈ Ico n N, (j : ℂ) ^ α = powerSumPart α k N - powerSumPart α k n -
      (-1) ^ k * Ring.choose α k *
        ∫ x in (n : ℝ)..N, (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos {x : ℝ} (hx : x ∈ Set.Icc ((n : ℤ) : ℝ) ((N : ℤ) : ℝ)) : 0 < x := by
    simp only [Int.cast_natCast] at hx; linarith [hx.1]
  set g : ℕ → ℝ → ℂ := fun i y => (i ! : ℂ) * Ring.choose α i * (y : ℂ) ^ (α - i) with hg
  have hcont (i : ℕ) : ContinuousOn (g i) (Set.Icc ((n : ℤ) : ℝ) ((N : ℤ) : ℝ)) := fun x hx =>
    (continuousAt_const.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr (hpos hx).ne'))).continuousWithinAt
  have hEM := sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := g) (a := n) (n := N)
    (by exact_mod_cast hnN) hk (fun i _ => hcont i)
    (fun i _ x hx =>
      hasDerivAt_factorial_mul_choose_mul_cpow α i (hpos (Set.Ioo_subset_Icc_self hx)))
    ((hcont k).intervalIntegrable_of_Icc (by simpa using hnN))
  -- Pass from the integer interval `[n, N]` to the natural one.
  have hmap : (Icc n N).map Nat.castEmbedding = Icc (n : ℤ) N := by
    simpa [← Finset.coe_inj] using Nat.image_cast_int_Icc n N
  rw [← hmap, sum_map] at hEM
  simp only [hg, Nat.castEmbedding_apply, Int.cast_natCast, Nat.factorial_zero, Nat.cast_one,
    Ring.choose_zero_right, one_mul, CharP.cast_eq_zero, sub_zero, ofReal_natCast,
    real_smul] at hEM
  rw [integral_cpow (Or.inr ⟨hα, by simp [Set.mem_uIcc]; omega⟩), ofReal_natCast,
    ofReal_natCast] at hEM
  -- Pull the constants out of the remainder and rewrite the Bernoulli terms.
  have hR : ∫ x in (n : ℝ)..N, (bernoulliFun k (Int.fract x) : ℂ) *
        ((k ! : ℂ) * Ring.choose α k * (x : ℂ) ^ (α - k)) =
      ((k ! : ℂ) * Ring.choose α k) *
        ∫ x in (n : ℝ)..N, (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hIcc : ∑ j ∈ Icc n N, (j : ℂ) ^ α = ∑ j ∈ Ico n N, (j : ℂ) ^ α + (N : ℂ) ^ α := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top hnN]
  rw [hR, sum_congr rfl fun s hs => bernoulli_div_factorial_mul_sub_eq α
    (by simp only [mem_Icc] at hs; omega) _ _, sum_sub_distrib, hIcc] at hEM
  -- The term `s = 1` of `powerSumPart` is `-x^α / 2`.
  simp only [powerSumPart]
  rw [← add_sum_Ioc_eq_sum_Icc hk, ← add_sum_Ioc_eq_sum_Icc hk, ← Finset.Icc_add_one_left_eq_Ioc]
  simp only [Nat.reduceAdd, Nat.cast_one, add_sub_cancel_right, Nat.sub_self,
    Ring.choose_zero_right, bernoulli_one, one_mul, div_one]
  have hk! : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast at hEM ⊢
  field_simp at hEM ⊢
  linear_combination hEM

/-- For `Re α < -1`, letting `N → ∞` in `sum_Ico_cpow_eq_powerSumPart_sub` gives
`∑_{j=1}^{n-1} j^α = ζ(-α) + P(n) + (-1)^k C(α, k) ∫_n^∞ Bₖ({x}) x^(α-k) dx`. -/
private theorem sum_Ico_cpow_eq_of_re_lt {α : ℂ} (hα : α.re < -1) {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℂ) ^ α = riemannZeta (-α) + powerSumPart α k n +
      (-1) ^ k * Ring.choose α k *
        ∫ x in Set.Ioi (n : ℝ), (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k) := by
  have hα1 : α ≠ -1 := fun h => by simp [h] at hα
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hαk : α.re < k - 1 := by linarith
  -- `∑_{j=1}^{N-1} j^α → ζ(-α)`.
  have hsum : Tendsto (fun N : ℕ => ∑ j ∈ Ico 1 N, (j : ℂ) ^ α) atTop
      (𝓝 (riemannZeta (-α))) := by
    have hs : 1 < (-α).re := by simp only [neg_re]; linarith
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    refine ((Complex.summable_one_div_nat_cpow.mpr hs).hasSum.tendsto_sum_nat).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hN]
    have h0 : (-α) ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    simp [cpow_neg, zero_cpow h0]
  -- `P(N) → 0`, since every exponent has negative real part.
  have hpow (β : ℂ) (hβ : β.re < 0) : Tendsto (fun N : ℕ => (N : ℂ) ^ β) atTop (𝓝 0) := by
    simpa using tendsto_natCast_cpow_neg_atTop (y := -β) (by simpa using hβ)
  have hP : Tendsto (fun N : ℕ => powerSumPart α k N) atTop (𝓝 0) := by
    have h0 := (hpow (α + 1) (by simp only [add_re, one_re]; linarith)).div_const (α + 1)
    have h1 := tendsto_finsetSum (Icc 1 k) fun s _ =>
      (hpow (α + 1 - s) (by
        simp only [sub_re, add_re, one_re, natCast_re]
        linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])).mul_const
        (Ring.choose α (s - 1) * bernoulli s / s)
    simpa [powerSumPart] using h0.add h1
  have hI := intervalIntegral_tendsto_integral_Ioi (n : ℝ)
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow hαk hn') tendsto_natCast_atTop_atTop
  have hlim := ((hsum.sub hP).add_const (powerSumPart α k n)).add
    (hI.const_mul ((-1) ^ k * Ring.choose α k))
  rw [sub_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [← sum_Ico_consecutive _ hn hN, sum_Ico_cpow_eq_powerSumPart_sub hα1 hk hn hN]
  ring

/-! ### Continuation to `Re α < k - 1` -/

/-- Away from `α = -1`, `ζ₀(-α) + (n^(α+1) - 1)/(α+1) = ζ(-α) + n^(α+1)/(α+1)`, where `ζ₀` is the
entire function `riemannZeta₀` and the quotient is written as a `dslope`, which is entire. -/
private theorem riemannZeta₀_add_dslope {α : ℂ} (hα : α ≠ -1) (n : ℕ) :
    riemannZeta₀ (-α) + dslope (fun β : ℂ => (n : ℂ) ^ β) 0 (α + 1) =
      riemannZeta (-α) + (n : ℂ) ^ (α + 1) / (α + 1) := by
  have hα' : α + 1 ≠ 0 := fun h => hα (by linear_combination h)
  have hpole : -α - 1 = -(α + 1) := by ring
  rw [riemannZeta_eq_inv_sub_add (fun h => hα (by linear_combination -h)), hpole,
    dslope_of_ne _ hα', slope_def_field, cpow_zero]
  field_simp
  ring

/-- The remainder integral `∫_n^∞ Bₖ({x}) x^(α-k) dx` is holomorphic in `α` on `Re α < k - 1`. -/
private theorem differentiableOn_integral_bernoulliFun_fract_mul_cpow (k : ℕ) {c : ℝ}
    (hc : 0 < c) :
    DifferentiableOn ℂ (fun α : ℂ => ∫ x in Set.Ioi c,
      (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k)) {α | α.re < k - 1} := by
  obtain ⟨M, hM⟩ := exists_norm_bernoulliFun_fract_le k
  have hO : (fun x : ℝ => (bernoulliFun k (Int.fract x) : ℂ)) =O[atTop]
      fun t : ℝ => t ^ (0 : ℝ) :=
    IsBigO.of_bound M (Eventually.of_forall fun x => by simpa using hM x)
  have hmaps : Set.MapsTo (fun α : ℂ => (k : ℂ) - 1 - α) {α : ℂ | α.re < k - 1}
      {s : ℂ | 0 < s.re} := by
    intro α hα
    simp only [Set.mem_ofPred_eq, sub_re, natCast_re, one_re] at hα ⊢
    linarith
  have h := (differentiableOn_integral_mul_cpow_of_isBigO hc hO).comp
    (by fun_prop : Differentiable ℂ fun α : ℂ => (k : ℂ) - 1 - α).differentiableOn hmaps
  simpa only [Function.comp_def, ← cpow_sub_natCast_eq] using h

/-- For `n ≥ 1`, `k ≥ 1` and `α ≠ -1` with `Re α < k - 1`,
`∑_{j=1}^{n-1} j^α = ζ(-α) + n^(α+1)/(α+1) + ∑_{s=1}^k C(α, s-1) Bₛ/s · n^(α+1-s)
  + (-1)^k C(α, k) ∫_n^∞ Bₖ({x}) x^(α-k) dx`, by the identity theorem from `Re α < -1`. -/
private theorem sum_Ico_cpow_eq_powerSumPart {α : ℂ} (hα : α ≠ -1) {k : ℕ} (hk : 1 ≤ k)
    (hαk : α.re < k - 1) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℂ) ^ α = riemannZeta (-α) + powerSumPart α k n +
      (-1) ^ k * Ring.choose α k *
        ∫ x in Set.Ioi (n : ℝ), (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- The difference of the two sides, with the pole at `α = -1` removed.
  set F : ℂ → ℂ := fun α => ∑ j ∈ Ico 1 n, (j : ℂ) ^ α - riemannZeta₀ (-α) -
    dslope (fun β : ℂ => (n : ℂ) ^ β) 0 (α + 1) -
    ∑ s ∈ Icc 1 k, (n : ℂ) ^ (α + 1 - s) * (Ring.choose α (s - 1) * bernoulli s / s) -
    (-1) ^ k * Ring.choose α k *
      ∫ x in Set.Ioi (n : ℝ), (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k) with hF
  have hFeq {α : ℂ} (hα : α ≠ -1) : F α = ∑ j ∈ Ico 1 n, (j : ℂ) ^ α -
      (riemannZeta (-α) + powerSumPart α k n +
        (-1) ^ k * Ring.choose α k *
          ∫ x in Set.Ioi (n : ℝ), (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k)) := by
    have h := riemannZeta₀_add_dslope hα n
    simp only [hF, powerSumPart]
    linear_combination -h
  have hU : IsOpen {α : ℂ | α.re < k - 1} := isOpen_lt continuous_re continuous_const
  have hnpow : Differentiable ℂ fun β : ℂ => (n : ℂ) ^ β := fun β =>
    differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (by omega)))
  have hdslope : Differentiable ℂ (dslope (fun β : ℂ => (n : ℂ) ^ β) 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact hnpow.differentiableOn
  have hFan : AnalyticOnNhd ℂ F {α : ℂ | α.re < k - 1} := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    refine ((((DifferentiableOn.sub ?_ ?_).sub ?_).sub ?_).sub ?_)
    · exact (Differentiable.fun_sum fun j hj => differentiable_id.const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr (by simp only [mem_Ico] at hj; omega)))).differentiableOn
    · exact (differentiable_riemannZeta₀.comp differentiable_neg).differentiableOn
    · exact (hdslope.comp (differentiable_id.add_const 1)).differentiableOn
    · exact (Differentiable.fun_sum fun s _ => ((differentiable_id.add_const 1).sub_const
        _ |>.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (by omega)))).mul
        (((differentiable_ringChoose _).mul_const _).div_const _)).differentiableOn
    · exact (((differentiable_ringChoose k).const_mul _).differentiableOn).mul
        (differentiableOn_integral_bernoulliFun_fract_mul_cpow k hn')
  -- `F` vanishes on `Re α < -1`, hence on the preconnected half-plane `Re α < k - 1`.
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm2 : (-2 : ℂ).re < -1 := by norm_num
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_lt (k - 1 : ℝ)).isPreconnected (z₀ := -2)
    (by simp only [Set.mem_ofPred_eq, neg_re, re_ofNat]; linarith) (by
      filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hm2] with α
        (hα : α.re < -1)
      rw [hFeq (fun h => by simp [h] at hα), Pi.zero_apply,
        sum_Ico_cpow_eq_of_re_lt hα hk hn, sub_self])
  have h := hzero hαk
  rw [hFeq hα, Pi.zero_apply, sub_eq_zero] at h
  exact h

/-- For `s ≥ 1` and `α ≠ -1`, `C(α+1, s) b / (α+1) = C(α, s-1) b / s`, by the absorption identity
`s C(α+1, s) = (α+1) C(α, s-1)`. -/
private theorem choose_add_one_mul_div {α : ℂ} (hα : α ≠ -1) {s : ℕ} (hs : 1 ≤ s) (b : ℂ) :
    Ring.choose (α + 1) s * b / (α + 1) = Ring.choose α (s - 1) * b / s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  -- The absorption identity `(t + 1) C(α + 1, t + 1) = (α + 1) C(α, t)`.
  have h := Ring.add_one_nsmul_choose_add_one_add_one α t
  rw [nsmul_eq_mul] at h
  push_cast at h
  have hα' : α + 1 ≠ 0 := fun h => hα (by linear_combination h)
  have ht : (t : ℂ) + 1 ≠ 0 := by exact_mod_cast t.succ_ne_zero
  rw [add_tsub_cancel_right]
  push_cast
  field_simp
  linear_combination b * h

/-! ### The expansion -/

/-- **The power sums by the Euler–Maclaurin formula** (DLMF 2.10.7 with an exact remainder). For
`n ≥ 1`, `k ≥ 1` and `α ≠ -1` with `Re α < k - 1`,
`∑_{j=1}^{n-1} j^α = ζ(-α) + ∑_{s=0}^k C(α+1, s) Bₛ/(α+1) · n^(α+1-s)
  + (-1)^k C(α, k) ∫_n^∞ Bₖ({x}) x^(α-k) dx`,
where `C(α+1, s) = Ring.choose (α + 1) s`, `Bₛ = bernoulli s` and `Bₖ({x})` is the periodic
Bernoulli function. The integral converges absolutely
(`TauCeti.integrableOn_Ioi_bernoulliFun_fract_mul_cpow`). -/
theorem sum_Ico_cpow_eq_riemannZeta_add {α : ℂ} (hα : α ≠ -1) {k : ℕ} (hk : 1 ≤ k)
    (hαk : α.re < k - 1) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℂ) ^ α = riemannZeta (-α) +
      ∑ s ∈ range (k + 1), (n : ℂ) ^ (α + 1 - s) *
        (Ring.choose (α + 1) s * bernoulli s / (α + 1)) +
      (-1) ^ k * Ring.choose α k *
        ∫ x in Set.Ioi (n : ℝ), (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k) := by
  have hsum : ∑ s ∈ Icc 1 k, (n : ℂ) ^ (α + 1 - s) *
      (Ring.choose (α + 1) s * bernoulli s / (α + 1)) =
      ∑ s ∈ Icc 1 k, (n : ℂ) ^ (α + 1 - s) * (Ring.choose α (s - 1) * bernoulli s / s) :=
    sum_congr rfl fun s hs => by rw [choose_add_one_mul_div hα (mem_Icc.mp hs).1]
  rw [sum_Ico_cpow_eq_powerSumPart hα hk hαk hn, powerSumPart, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_add_one_right_eq_Icc, hsum]
  simp [div_eq_mul_inv]

/-- The functions `n^(β - s)`, `s ∈ ℕ`, form an asymptotic scale as `n → ∞` along `ℕ`. -/
theorem isAsymptoticScale_natCast_cpow_sub (β : ℂ) :
    IsAsymptoticScale atTop (fun s (n : ℕ) => (n : ℂ) ^ (β - s)) := by
  refine ((isAsymptoticScale_pow (l := (atTop : Filter ℕ)) (w := fun n : ℕ => (n : ℂ)⁻¹)
    tendsto_inv_atTop_nhds_zero_nat).mul_left fun n : ℕ => (n : ℂ) ^ β).congr' fun s => ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [cpow_sub _ _ hn0, cpow_natCast, inv_pow, div_eq_mul_inv]

/-- **The asymptotic expansion of the power sums** (DLMF 2.10.7). For `α ≠ -1`, as `n → ∞`,
`∑_{j=1}^{n-1} j^α - ζ(-α) ∼ n^(α+1)/(α+1) · ∑_{s ≥ 0} C(α+1, s) Bₛ n^(-s)`
in the scale `n^(α+1-s)`, where `C(α+1, s) = Ring.choose (α + 1) s` and `Bₛ = bernoulli s`. -/
theorem hasAsymptoticExpansion_sum_Ico_cpow_sub_riemannZeta {α : ℂ} (hα : α ≠ -1) :
    HasAsymptoticExpansion atTop (fun s (n : ℕ) => (n : ℂ) ^ (α + 1 - s))
      (fun s => Ring.choose (α + 1) s * bernoulli s / (α + 1))
      (fun n => ∑ j ∈ Ico 1 n, (j : ℂ) ^ α - riemannZeta (-α)) := by
  have hscale := isAsymptoticScale_natCast_cpow_sub (α + 1)
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  -- Use the exact identity of an order `k ≥ N` with `Re α < k - 1`.
  obtain ⟨K, hK⟩ := exists_nat_gt (α.re + 2)
  set k := N + K + 1 with hk
  have hαk : α.re < k - 1 := by
    simp only [hk]
    push_cast
    linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  obtain ⟨M, hM⟩ := exists_norm_bernoulliFun_fract_le k
  -- The terms `N ≤ s ≤ k` are `O(n^(α+1-N))`.
  have hterms : (fun n : ℕ => ∑ s ∈ Ico N (k + 1), (n : ℂ) ^ (α + 1 - s) *
      (Ring.choose (α + 1) s * bernoulli s / (α + 1))) =O[atTop]
      fun n : ℕ => (n : ℂ) ^ (α + 1 - N) :=
    IsBigO.fun_sum fun s hs => by
      simpa only [mul_comm] using
        (hscale.isBigO_of_le (mem_Ico.mp hs).1).const_mul_left
          (Ring.choose (α + 1) s * bernoulli s / (α + 1))
  -- The remainder is `O(n^(α+1-k))`.
  have hrem : (fun n : ℕ => (-1) ^ k * Ring.choose α k *
      ∫ x in Set.Ioi (n : ℝ), (bernoulliFun k (Int.fract x) : ℂ) * (x : ℂ) ^ (α - k)) =O[atTop]
      fun n : ℕ => (n : ℂ) ^ (α + 1 - k) := by
    refine IsBigO.const_mul_left (IsBigO.of_bound (M / (k - 1 - α.re)) ?_) _
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_natCast_cpow_of_pos (by omega)]
    refine (norm_integral_bernoulliFun_fract_mul_cpow_le hαk hM hn0).trans_eq ?_
    simp only [sub_re, add_re, one_re, natCast_re]
    ring
  refine (hterms.add (hrem.trans (hscale.isBigO_of_le (by omega)))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sum_Ico_cpow_eq_riemannZeta_add hα (by omega) hαk hn,
    ← sum_range_add_sum_Ico _ (by omega : N ≤ k + 1)]
  simp only [smul_eq_mul]
  ring

/-! ### The enclosure of the remainder for real `α` -/

/-- For `p ≥ 1` and `Re α < 2p - 1`, the remainder after the terms `s < 2p` of the expansion is
`C(α, 2p) ∫_n^∞ (B_{2p}({x}) - B_{2p}) x^(α - 2p) dx`. -/
private theorem sum_Ico_cpow_sub_eq_integral {α : ℂ} (hα : α ≠ -1) {p : ℕ} (hp : 1 ≤ p)
    (hαp : α.re < 2 * p - 1) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, (j : ℂ) ^ α - riemannZeta (-α) -
      ∑ s ∈ range (2 * p), (n : ℂ) ^ (α + 1 - s) *
        (Ring.choose (α + 1) s * bernoulli s / (α + 1)) =
    Ring.choose α (2 * p) * ∫ x in Set.Ioi (n : ℝ),
      ((bernoulliFun (2 * p) (Int.fract x) - bernoulli (2 * p) : ℝ) : ℂ) *
        (x : ℂ) ^ (α - (2 * p : ℕ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hαk : α.re < ((2 * p : ℕ) : ℝ) - 1 := by push_cast; exact hαp
  have hre : (α - (2 * p : ℕ)).re < -1 := by
    simp only [sub_re, natCast_re]
    push_cast
    linarith
  have hα' : α - (2 * p : ℕ) + 1 ≠ 0 := fun h => by
    have := congrArg re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  -- Split the integral and evaluate `∫_n^∞ x^(α - 2p) dx`.
  have hsplit : ∫ x in Set.Ioi (n : ℝ),
      ((bernoulliFun (2 * p) (Int.fract x) - bernoulli (2 * p) : ℝ) : ℂ) *
        (x : ℂ) ^ (α - (2 * p : ℕ)) =
      (∫ x in Set.Ioi (n : ℝ), (bernoulliFun (2 * p) (Int.fract x) : ℂ) *
        (x : ℂ) ^ (α - (2 * p : ℕ))) +
        (bernoulli (2 * p) : ℂ) * ((n : ℂ) ^ (α - (2 * p : ℕ) + 1) / (α - (2 * p : ℕ) + 1)) := by
    have h := integral_sub (integrableOn_Ioi_bernoulliFun_fract_mul_cpow hαk hn')
      ((integrableOn_Ioi_cpow_of_lt hre hn').const_mul (bernoulli (2 * p) : ℂ))
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hre hn', ofReal_natCast] at h
    simp only [ofReal_sub, ofReal_ratCast, sub_mul]
    rw [h]
    ring
  -- The recursion `2p C(α, 2p) = C(α, 2p - 1) (α - (2p - 1))`.
  have hrec := Ring.add_one_nsmul_choose_add_one α (2 * p - 1)
  rw [nsmul_eq_mul, Nat.sub_add_cancel (by omega)] at hrec
  have h2p' : ((2 * p - 1 : ℕ) : ℂ) = (2 * p : ℕ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hp0 : ((2 * p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [h2p'] at hrec
  rw [sum_Ico_cpow_eq_riemannZeta_add hα (by omega) hαk hn, sum_range_succ, hsplit,
    choose_add_one_mul_div hα (by omega), Even.neg_one_pow (by simp)]
  have hexp : α + 1 - ((2 * p : ℕ) : ℂ) = α - (2 * p : ℕ) + 1 := by ring
  rw [hexp]
  field_simp
  linear_combination -(bernoulli (2 * p) : ℂ) * (n : ℂ) ^ (α - (2 * p : ℕ) + 1) * hrec

/-- The remainder integral `∫_c^∞ (B_{2p}({x}) - B_{2p}) x^β dx` has the sign `(-1)^p`. -/
private theorem neg_one_pow_mul_integral_bernoulliFun_sub_nonneg (p : ℕ) (β : ℝ) {c : ℝ}
    (hc : 0 < c) :
    0 ≤ (-1) ^ p * ∫ x in Set.Ioi c,
      (bernoulliFun (2 * p) (Int.fract x) - bernoulli (2 * p)) * x ^ β := by
  rw [← integral_const_mul]
  refine setIntegral_nonneg measurableSet_Ioi fun x (hx : c < x) => ?_
  have h := neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg p
    (x := Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← mul_assoc]
  refine mul_nonneg ?_ (Real.rpow_nonneg (hc.trans hx).le _)
  convert h using 1
  ring

/-- For real `α` and `x > 0`, the complex remainder integral of `sum_Ico_cpow_sub_eq_integral` is
the real integral `∫_n^∞ (B_{2p}({x}) - B_{2p}) x^(α - 2p) dx`. -/
private theorem integral_ofReal_bernoulliFun_sub_mul_cpow (α : ℝ) (p : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ x in Set.Ioi c, ((bernoulliFun (2 * p) (Int.fract x) - bernoulli (2 * p) : ℝ) : ℂ) *
        (x : ℂ) ^ ((α : ℂ) - (2 * p : ℕ)) =
      ((∫ x in Set.Ioi c,
        (bernoulliFun (2 * p) (Int.fract x) - bernoulli (2 * p)) * x ^ (α - (2 * p : ℕ)) : ℝ) :
          ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : c < x) => ?_
  rw [ofReal_mul, ofReal_cpow (hc.trans hx).le, ofReal_sub, ofReal_sub, ofReal_natCast,
    ofReal_ratCast]

/-- The remainder integral `∫_c^∞ (B_{2p}({x}) - B_{2p}) x^(α - 2p) dx` after the terms `s < 2p`,
for real `α`. -/
private noncomputable def evenRemainder (α c : ℝ) (p : ℕ) : ℝ :=
  ∫ x in Set.Ioi c, (bernoulliFun (2 * p) (Int.fract x) - bernoulli (2 * p)) * x ^ (α - (2 * p : ℕ))

/-- Two steps of the recursion of the binomial coefficients:
`(2m + 1)(2m + 2) C(α, 2m + 2) = C(α, 2m) (α - 2m)(α - 2m - 1)`. -/
private theorem mul_choose_two_mul_add_one (α : ℝ) (m : ℕ) :
    ((2 * m + 1) * (2 * m + 2) : ℝ) * Ring.choose α (2 * (m + 1)) =
      Ring.choose α (2 * m) * ((α - 2 * m) * (α - (2 * m + 1))) := by
  have hc1 := Ring.add_one_nsmul_choose_add_one α (2 * m)
  have hc2 := Ring.add_one_nsmul_choose_add_one α (2 * m + 1)
  rw [nsmul_eq_mul] at hc1 hc2
  have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  rw [h2]
  push_cast at hc1 hc2 ⊢
  linear_combination (2 * (m : ℝ) + 1) * hc2 + (α - (2 * m + 1)) * hc1

/-- For real `α < 2m - 1` and `c > 0`, the remainders `C(α, 2m) R_m` and `C(α, 2m + 2) R_{m+1}`,
with `R_p` the integral `evenRemainder α c p`, lie on opposite sides of `0`, so the first is `θ`
times their difference with `θ ∈ [0, 1]`. -/
private theorem exists_mem_Icc_choose_mul_evenRemainder_eq {α : ℝ} {m : ℕ} (hαm : α < 2 * m - 1)
    {c : ℝ} (hc : 0 < c) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, Ring.choose α (2 * m) * evenRemainder α c m =
      θ * (Ring.choose α (2 * m) * evenRemainder α c m -
        Ring.choose α (2 * (m + 1)) * evenRemainder α c (m + 1)) := by
  -- If `e a ≥ 0`, `e b ≤ 0` and `a = 0` when `e = 0`, then `a = θ (a - b)` with `θ ∈ [0, 1]`.
  have key {a b e : ℝ} (ha : 0 ≤ e * a) (hb : e * b ≤ 0) (he : e = 0 → a = 0) :
      ∃ θ ∈ Set.Icc (0 : ℝ) 1, a = θ * (a - b) := by
    rcases eq_or_ne e 0 with he0 | he0
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [he he0, zero_mul]⟩
    have hab0 : 0 ≤ e * (a - b) := by rw [mul_sub]; linarith
    rcases hab0.eq_or_lt with h0 | h0
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      rw [zero_mul]
      exact (mul_eq_zero.mp (by linarith [mul_sub e a b])).resolve_left he0
    refine ⟨e * a / (e * (a - b)), ⟨div_nonneg ha h0.le, (div_le_one h0).mpr (by linarith)⟩, ?_⟩
    have hab : a - b ≠ 0 := fun h => by simp [h] at h0
    field_simp
  set C : ℝ := Ring.choose α (2 * m)
  have hsign := neg_one_pow_mul_integral_bernoulliFun_sub_nonneg m (α - (2 * m : ℕ)) hc
  have hsign' := neg_one_pow_mul_integral_bernoulliFun_sub_nonneg (m + 1)
    (α - (2 * (m + 1) : ℕ)) hc
  have hfac : 0 < (α - 2 * m) * (α - (2 * m + 1)) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hden : (0 : ℝ) < (2 * m + 1) * (2 * m + 2) := by positivity
  have hC' : Ring.choose α (2 * (m + 1)) =
      C * ((α - 2 * m) * (α - (2 * m + 1))) / ((2 * m + 1) * (2 * m + 2)) := by
    rw [eq_div_iff hden.ne', mul_comm]
    exact mul_choose_two_mul_add_one α m
  refine key (e := (-1) ^ m * C) ?_ ?_ fun he => ?_
  · have : (-1) ^ m * C * (C * evenRemainder α c m) =
        C ^ 2 * ((-1) ^ m * evenRemainder α c m) := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg C) hsign
  · have h : (-1) ^ m * C * (Ring.choose α (2 * (m + 1)) * evenRemainder α c (m + 1)) =
        -(C ^ 2 * ((α - 2 * m) * (α - (2 * m + 1))) / ((2 * m + 1) * (2 * m + 2)) *
          ((-1) ^ (m + 1) * evenRemainder α c (m + 1))) := by
      rw [hC', pow_succ]
      ring
    rw [h, neg_nonpos]
    exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg C) hfac.le) hden.le) hsign'
  · rw [mul_eq_zero, or_iff_right (pow_ne_zero m (by norm_num))] at he
    rw [he, zero_mul]

/-- **The power sums with an enclosed remainder** (DLMF 2.10.7). For real `α ≠ -1`, `m ≥ 1` with
`α ≤ 2m - 1` and `n ≥ 1`, truncating the expansion
`∑_{j=1}^{n-1} j^α ∼ ζ(-α) + ∑_{s ≥ 0} C(α+1, s) Bₛ/(α+1) · n^(α+1-s)`
after the term `s = 2m - 1` leaves `θ` times the term `s = 2m`, with `θ ∈ [0, 1]`: the remainder
has the sign of the first neglected term and is at most that term in absolute value. -/
theorem exists_mem_Icc_sum_Ico_cpow_eq {α : ℝ} (hα : α ≠ -1) {m : ℕ} (hm : 1 ≤ m)
    (hαm : α ≤ 2 * m - 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      ∑ j ∈ Ico 1 n, (j : ℂ) ^ (α : ℂ) = riemannZeta (-α) +
        ∑ s ∈ range (2 * m), (n : ℂ) ^ ((α : ℂ) + 1 - s) *
          (Ring.choose ((α : ℂ) + 1) s * bernoulli s / ((α : ℂ) + 1)) +
        θ * ((n : ℂ) ^ ((α : ℂ) + 1 - (2 * m : ℕ)) *
          (Ring.choose ((α : ℂ) + 1) (2 * m) * bernoulli (2 * m) / ((α : ℂ) + 1))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hαc : (α : ℂ) ≠ -1 := by exact_mod_cast hα
  set T : ℕ → ℂ := fun s => (n : ℂ) ^ ((α : ℂ) + 1 - s) *
    (Ring.choose ((α : ℂ) + 1) s * bernoulli s / ((α : ℂ) + 1)) with hT
  -- The remainders after the terms `s < 2p`.
  set A : ℕ → ℂ := fun p => ∑ j ∈ Ico 1 n, (j : ℂ) ^ (α : ℂ) - riemannZeta (-α) -
    ∑ s ∈ range (2 * p), T s with hA
  have hAI {p : ℕ} (hp : 1 ≤ p) (hαp : α < 2 * p - 1) :
      A p = ((Ring.choose α (2 * p) * evenRemainder α n p : ℝ) : ℂ) := by
    have h := sum_Ico_cpow_sub_eq_integral hαc hp (by simpa using hαp) hn
    rw [integral_ofReal_bernoulliFun_sub_mul_cpow α p hn', ← evenRemainder] at h
    have hch : ((Ring.choose α (2 * p) : ℝ) : ℂ) = Ring.choose (α : ℂ) (2 * p) := by
      simpa using Ring.map_choose (algebraMap ℝ ℂ) α (2 * p)
    rw [ofReal_mul, hch]
    exact h
  -- `A m - A (m + 1)` is the term `s = 2m`, since `B_{2m+1} = 0`.
  have hstep : A m - A (m + 1) = T (2 * m) := by
    have hodd : T (2 * m + 1) = 0 := by
      simp [hT, bernoulli_eq_zero_of_odd (odd_two_mul_add_one m) (by omega)]
    simp only [hA, mul_add, mul_one, sum_range_succ, hodd]
    ring
  have hAm1 := hAI (p := m + 1) (by omega) (by push_cast; linarith)
  have hcases : ∃ θ ∈ Set.Icc (0 : ℝ) 1, A m = θ * T (2 * m) := by
    rcases hαm.lt_or_eq with hlt | heq
    · -- Opposite signs of the two remainders enclose `A m`.
      obtain ⟨θ, hθ, hθeq⟩ := exists_mem_Icc_choose_mul_evenRemainder_eq hlt hn'
      refine ⟨θ, hθ, ?_⟩
      rw [← hstep, hAI hm hlt, hAm1]
      exact_mod_cast hθeq
    · -- At `α = 2m - 1` the coefficient `C(α, 2m + 2)` vanishes, so `A (m + 1) = 0`.
      have hα' : α = ((2 * m - 1 : ℕ) : ℝ) := by
        rw [heq, Nat.cast_sub (by omega)]
        push_cast
        ring
      have hzero : Ring.choose α (2 * (m + 1)) = 0 := by
        rw [hα', Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [ofReal_one, one_mul, ← hstep, hAm1, hzero, zero_mul, ofReal_zero, sub_zero]
  obtain ⟨θ, hθ, h⟩ := hcases
  refine ⟨θ, hθ, ?_⟩
  simp only [hA, hT] at h ⊢
  linear_combination h

end TauCeti
