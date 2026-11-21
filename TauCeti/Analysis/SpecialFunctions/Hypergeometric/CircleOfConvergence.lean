/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# The Gauss series on its circle of convergence

When none of `a`, `b`, `c` is a nonpositive integer, the Gauss hypergeometric series
`∑ (a)ₛ (b)ₛ / ((c)ₛ s!) zˢ` has radius of convergence `1`. If `a` or `b` is a nonpositive integer
the coefficients are eventually zero and the series is a polynomial; if `c` is one, Mathlib's
convention `x / 0 = 0` makes the coefficients eventually zero as well. The behaviour of the series
on the circle `|z| = 1` is governed by the real part of `c − a − b` (DLMF §15.2(i)):

* the series converges absolutely if `Re(c − a − b) > 0`;
* it converges for `z ≠ 1` if `Re(c − a − b) > −1`, but not absolutely if `Re(c − a − b) ≤ 0`
  and none of `a`, `b`, `c` is a nonpositive integer;
* its partial sums diverge if `Re(c − a − b) ≤ −1` and none of `a`, `b`, `c` is a nonpositive
  integer.

Everything follows from the size of the coefficients. By Euler's limit formula for the Gamma
function, `(a)ₛ (b)ₛ / ((c)ₛ s!) ∼ Γ(c) / (Γ(a) Γ(b)) s^(a + b − c − 1)` as `s → ∞`, for all
complex parameters, with Mathlib's junk values `Γ(−k) = 0` and `x / 0 = 0` covering the
terminating and undefined cases. Convergence for `z ≠ 1` is Dirichlet's test: the partial sums of
`zˢ` are bounded and the coefficients have summable differences, of order `s^(Re(a + b − c) − 2)`.

## Main results

* `Complex.tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow`: the coefficient
  asymptotic `cₛ / s^(a + b − c − 1) → Γ(c) / (Γ(a) Γ(b))`.
* `Complex.isBigO_ordinaryHypergeometricCoefficient`,
  `Complex.isTheta_ordinaryHypergeometricCoefficient`: `cₛ = O(s^(Re(a + b − c) − 1))`, with
  equality of orders when no parameter is a nonpositive integer.
* `Complex.isBigO_ordinaryHypergeometricCoefficient_add_one_sub`:
  `cₛ₊₁ − cₛ = O(s^(Re(a + b − c) − 2))`.
* `Complex.summable_norm_gaussTerm_of_re_pos`: absolute convergence for `Re(c − a − b) > 0`.
* `Complex.exists_tendsto_sum_gaussTerm_of_neg_one_lt_re`: convergence for `z ≠ 1` and
  `Re(c − a − b) > −1`.
* `Complex.not_summable_norm_gaussTerm_of_re_nonpos`: no absolute convergence for
  `Re(c − a − b) ≤ 0`.
* `Complex.not_tendsto_sum_gaussTerm_of_re_le_neg_one`: divergence for `Re(c − a − b) ≤ −1`.

## References

* NIST Digital Library of Mathematical Functions, §15.2(i), <https://dlmf.nist.gov/15.2.i>.
* G. E. Andrews, R. Askey and R. Roy, *Special Functions*, Theorem 2.1.2.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Hypergeometric/Basic/GaussSeries.lean` and `DLMF/Hypergeometric/AnalyticProperties.lean`.
-/

public section

open Asymptotics Filter Polynomial
open scoped Nat Topology

namespace Complex

/-! ### The size of the coefficients -/

/-- **The coefficient asymptotic of the Gauss series.** For all complex `a`, `b`, `c`, the
coefficients `cₛ = (a)ₛ (b)ₛ / ((c)ₛ s!)` of `₂F₁(a, b; c; ·)` satisfy
`cₛ / s^(a + b − c − 1) → Γ(c) / (Γ(a) Γ(b))`. When a parameter is a nonpositive integer both
sides are eventually `0`. -/
theorem tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow (a b c : ℂ) :
    Tendsto (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n / (n : ℂ) ^ (a + b - c - 1))
      atTop (𝓝 (Gamma c / (Gamma a * Gamma b))) := by
  have h := ((tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial a).mul
    (tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial b)).mul
    (tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval c)
  -- Regroup the product of the three limits as the quotient `Γ(c) / (Γ(a) Γ(b))`.
  have hΓ : (Gamma a)⁻¹ * (Gamma b)⁻¹ * Gamma c = Gamma c / (Gamma a * Gamma b) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hΓ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hexp : a + b - c - 1 = (a - 1) + (b - 1) - (c - 1) := by ring
  conv_rhs => rw [hexp, cpow_sub _ _ hn', cpow_add _ _ hn', ordinaryHypergeometricCoefficient]
  have ha := cpow_ne_zero_iff.mpr (Or.inl hn' : (n : ℂ) ≠ 0 ∨ a - 1 = 0)
  have hb := cpow_ne_zero_iff.mpr (Or.inl hn' : (n : ℂ) ≠ 0 ∨ b - 1 = 0)
  have hc := cpow_ne_zero_iff.mpr (Or.inl hn' : (n : ℂ) ≠ 0 ∨ c - 1 = 0)
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

/-- The coefficients of the Gauss series are `O(s^(Re(a + b − c) − 1))`, for all complex
parameters. -/
theorem isBigO_ordinaryHypergeometricCoefficient (a b c : ℂ) :
    ordinaryHypergeometricCoefficient a b c =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + b - c - 1).re := by
  have h := isBigO_of_div_tendsto_nhds ?_ _
    (tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow a b c)
  · refine h.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [norm_natCast_cpow_of_pos hn, Real.norm_of_nonneg (by positivity), one_mul]
  · filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn)))

/-- When none of `a`, `b`, `c` is a nonpositive integer, the coefficients of the Gauss series are
of exact order `s^(Re(a + b − c) − 1)`. -/
theorem isTheta_ordinaryHypergeometricCoefficient {a b c : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) :
    ordinaryHypergeometricCoefficient a b c =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + b - c - 1).re := by
  have hL : Gamma c / (Gamma a * Gamma b) ≠ 0 :=
    div_ne_zero (Gamma_ne_zero hc) (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))
  refine (isTheta_norm_right.mpr (isTheta_of_div_tendsto_nhds_ne_zero
    (tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow a b c) hL).symm).trans_eventuallyEq
      ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact norm_natCast_cpow_of_pos hn _

/-- The recurrence multiplier `r(s) = (a + s)(b + s) / ((s + 1)(c + s))` of the Gauss coefficients,
`cₛ₊₁ = r(s) cₛ` (`TauCeti.ordinaryHypergeometricCoefficient_add_one`), satisfies
`r(s) − 1 = O(1 / s)`, for all complex parameters. It is the ratio `cₛ₊₁ / cₛ` only where
`cₛ ≠ 0`; for a terminating series the coefficients vanish from some index on. -/
private theorem isBigO_coefficientRatio_sub_one (a b c : ℂ) :
    (fun n : ℕ => (a + n) * (b + n) / ((n + 1) * (c + n)) - 1) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-1 : ℝ) := by
  -- `n (r(n) − 1) = (α + β / n) / ((1 + 1 / n) (1 + c / n))` tends to `α = a + b − c − 1`.
  have h0 (s : ℂ) : Tendsto (fun n : ℕ => s / (n : ℂ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat s
  have hlim : Tendsto (fun n : ℕ => (a + b - c - 1 + (a * b - c) / n) /
      ((1 + 1 / n) * (1 + c / n))) atTop (𝓝 (a + b - c - 1)) := by
    have h := ((tendsto_const_nhds (x := a + b - c - 1)).add (h0 (a * b - c))).div
      (((tendsto_const_nhds (x := (1 : ℂ))).add (h0 1)).mul
        ((tendsto_const_nhds (x := (1 : ℂ))).add (h0 c))) (by norm_num)
    rwa [add_zero, add_zero, mul_one, div_one] at h
  have hinv : (fun n : ℕ => ((n : ℂ))⁻¹) =O[atTop] fun n : ℕ => (n : ℝ) ^ (-1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [norm_inv, norm_natCast, Real.rpow_neg_one, Real.norm_of_nonneg (by positivity), one_mul]
  refine ((hlim.isBigO_one ℝ).mul hinv).congr' ?_ (Eventually.of_forall fun n => one_mul _)
  · filter_upwards [eventually_ne_atTop 0,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop ‖c‖] with n hn hcn
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hcn' : (n : ℂ) + c ≠ 0 := by
      intro h
      rw [eq_neg_of_add_eq_zero_right h, norm_neg, norm_natCast] at hcn
      exact lt_irrefl _ hcn
    have hcn'' : c + n ≠ 0 := by rwa [add_comm]
    -- Clear the inner denominators `n` of `1 + 1 / n` and `1 + c / n`.
    have h1 : (1 : ℂ) + 1 / n = (n + 1) / n := by rw [add_div, div_self hn']
    have h2 : (1 : ℂ) + c / n = (n + c) / n := by rw [add_div, div_self hn']
    rw [h1, h2]
    field_simp
    ring

/-- The differences of consecutive coefficients of the Gauss series are
`O(s^(Re(a + b − c) − 2))`, for all complex parameters. -/
theorem isBigO_ordinaryHypergeometricCoefficient_add_one_sub (a b c : ℂ) :
    (fun n : ℕ => ordinaryHypergeometricCoefficient a b c (n + 1) -
      ordinaryHypergeometricCoefficient a b c n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((a + b - c - 1).re - 1) := by
  refine ((isBigO_coefficientRatio_sub_one a b c).mul
    (isBigO_ordinaryHypergeometricCoefficient a b c)).congr' (Eventually.of_forall fun n => ?_) ?_
  · dsimp only
    rw [TauCeti.ordinaryHypergeometricCoefficient_add_one]
    ring
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.rpow_add (Nat.cast_pos.mpr hn), neg_add_eq_sub]

/-! ### The series on the unit circle -/

/-- The norm of a Gauss term on the unit circle is the norm of its coefficient. -/
private theorem norm_gaussTerm_of_norm_eq_one {a b c z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
        ((ascPochhammer ℂ n).eval c * (n ! : ℂ)) * z ^ n‖ =
      ‖ordinaryHypergeometricCoefficient a b c n‖ := by
  rw [TauCeti.ordinaryHypergeometricCoefficient_eq_div, norm_mul, norm_pow, hz, one_pow, mul_one]

/-- **Absolute convergence on the circle** (DLMF §15.2(i)). On `|z| = 1` the Gauss series of
`₂F₁(a, b; c; z)` converges absolutely when `Re(c − a − b) > 0`. -/
theorem summable_norm_gaussTerm_of_re_pos {a b c z : ℂ} (hz : ‖z‖ = 1)
    (h : 0 < (c - a - b).re) :
    Summable fun s : ℕ => ‖(ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
      ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s‖ := by
  simp_rw [norm_gaussTerm_of_norm_eq_one hz]
  refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr ?_)
    (isBigO_ordinaryHypergeometricCoefficient a b c).norm_left
  simp only [sub_re, add_re, one_re] at h ⊢
  linarith

/-- **Convergence on the circle away from `1`** (DLMF §15.2(i)). On `|z| = 1`, `z ≠ 1`, the
partial sums of the Gauss series of `₂F₁(a, b; c; z)` converge when `Re(c − a − b) > −1`. -/
theorem exists_tendsto_sum_gaussTerm_of_neg_one_lt_re {a b c z : ℂ} (hz : ‖z‖ = 1) (hz₁ : z ≠ 1)
    (h : -1 < (c - a - b).re) :
    ∃ L : ℂ, Tendsto (fun N => ∑ s ∈ Finset.range N,
      (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
        ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s) atTop (𝓝 L) := by
  have hσ : (a + b - c - 1).re < 0 := by
    simp only [sub_re, add_re, one_re] at h ⊢
    linarith
  have hf0 : Tendsto (ordinaryHypergeometricCoefficient a b c) atTop (𝓝 0) := by
    refine (isBigO_ordinaryHypergeometricCoefficient a b c).trans_tendsto ?_
    simpa [Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hσ)).comp tendsto_natCast_atTop_atTop
  have hvar : Summable fun n => ‖ordinaryHypergeometricCoefficient a b c (n + 1) -
      ordinaryHypergeometricCoefficient a b c n‖ :=
    summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by linarith))
      (isBigO_ordinaryHypergeometricCoefficient_add_one_sub a b c).norm_left
  have hz0 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz₁)
  have hgeom (n : ℕ) : ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz₁, norm_div, div_le_div_iff_of_pos_right hz0]
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (hf0.cauchySeq_series_smul_of_summable_norm_sub hvar hgeom)
  exact ⟨L, by simpa only [smul_eq_mul, TauCeti.ordinaryHypergeometricCoefficient_eq_div] using hL⟩

/-- **No absolute convergence on the circle** (DLMF §15.2(i)). On `|z| = 1` the nonterminating
Gauss series of `₂F₁(a, b; c; z)` does not converge absolutely when `Re(c − a − b) ≤ 0`. -/
theorem not_summable_norm_gaussTerm_of_re_nonpos {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ = 1) (h : (c - a - b).re ≤ 0) :
    ¬ Summable fun s : ℕ => ‖(ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
      ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s‖ := by
  simp_rw [norm_gaussTerm_of_norm_eq_one hz]
  intro hs
  have hσ := Real.summable_nat_rpow.mp
    (summable_of_isBigO_nat hs (isTheta_ordinaryHypergeometricCoefficient ha hb hc).2.norm_right)
  simp only [sub_re, add_re, one_re] at h hσ
  linarith

/-- **Divergence on the circle** (DLMF §15.2(i)). On `|z| = 1` the partial sums of the
nonterminating Gauss series of `₂F₁(a, b; c; z)` diverge when `Re(c − a − b) ≤ −1`. -/
theorem not_tendsto_sum_gaussTerm_of_re_le_neg_one {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ = 1) (h : (c - a - b).re ≤ -1) :
    ¬ ∃ L : ℂ, Tendsto (fun N => ∑ s ∈ Finset.range N,
      (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
        ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  -- The terms of a convergent series tend to `0`, so the coefficients do as well.
  have hterm := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
  simp only [sub_self, Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left] at hterm
  have hcoef : Tendsto (fun n => ‖ordinaryHypergeometricCoefficient a b c n‖) atTop (𝓝 0) := by
    simpa only [norm_gaussTerm_of_norm_eq_one hz, norm_zero] using hterm.norm
  -- But the coefficients are bounded below by a multiple of `n ^ σ` with `σ ≥ 0`.
  have hpow := (isTheta_ordinaryHypergeometricCoefficient ha hb hc).2.norm_right.trans_tendsto
    hcoef
  have hσ : 0 ≤ (a + b - c - 1).re := by
    simp only [sub_re, add_re, one_re] at h ⊢
    linarith
  obtain ⟨n, hn, hn1⟩ :=
    ((hpow.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop 1)).exists
  exact (Real.one_le_rpow (by exact_mod_cast hn1) hσ).not_gt hn

end Complex
