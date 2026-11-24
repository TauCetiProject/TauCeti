/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.CoefficientAsymptotics
import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
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

The convergence statements are proved on the closed disk `|z| ≤ 1`, the negative ones for
`|z| ≥ 1`. Absolute convergence carries over to the regularized series `𝐅(a, b; c; z)` for every
`c`, including the poles of `Γ`, by the shift `c ↦ c + 1` of DLMF 15.5.15 on its coefficients.

Everything follows from the size of the coefficients
(`TauCeti.Analysis.SpecialFunctions.Hypergeometric.CoefficientAsymptotics`). By Euler's limit
formula for the Gamma function, the normalized coefficients `cₛ / s^(a + b − c − 1)` tend to
`Γ(c) / (Γ(a) Γ(b))` for all complex parameters, with Mathlib's junk values `Γ(−k) = 0` and
`x / 0 = 0` covering the terminating and undefined cases; when no parameter is a nonpositive
integer the limit is nonzero, and `cₛ ∼ Γ(c) / (Γ(a) Γ(b)) s^(a + b − c − 1)`. Convergence for
`z ≠ 1` is Dirichlet's test: the partial sums of `zˢ` are bounded, and the consecutive differences
of the coefficients are `O(s^(Re(a + b − c) − 2))` for all parameters, hence summable when
`Re(c − a − b) > −1`.

## Main results

* `Complex.summable_norm_gaussTerm_of_re_pos`: absolute convergence for `|z| ≤ 1` and
  `Re(c − a − b) > 0`.
* `Complex.summable_norm_coeff_regularizedGaussHGFunSeries_mul_pow_of_re_pos`: the same for the
  regularized series `𝐅(a, b; c; z)`, for every `c`.
* `Complex.exists_tendsto_sum_gaussTerm_of_neg_one_lt_re`: convergence for `|z| ≤ 1`, `z ≠ 1` and
  `Re(c − a − b) > −1`.
* `Complex.not_summable_norm_gaussTerm_of_re_nonpos`: no absolute convergence for `|z| ≥ 1` and
  `Re(c − a − b) ≤ 0`, when none of `a`, `b`, `c` is a nonpositive integer.
* `Complex.not_exists_tendsto_sum_gaussTerm_of_re_le_neg_one`: divergence of the partial sums for
  `|z| ≥ 1` and `Re(c − a − b) ≤ −1`, when none of `a`, `b`, `c` is a nonpositive integer.

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

/-! ### The series on the unit circle -/

/-- The norm of a Gauss term is the norm of its coefficient times `‖z‖ ^ s`. -/
private theorem norm_gaussTerm (a b c z : ℂ) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
        ((ascPochhammer ℂ n).eval c * (n ! : ℂ)) * z ^ n‖ =
      ‖ordinaryHypergeometricCoefficient a b c n‖ * ‖z‖ ^ n := by
  rw [TauCeti.ordinaryHypergeometricCoefficient_eq_div, norm_mul, norm_pow]

/-- **Absolute convergence on the closed disk** (DLMF §15.2(i)). On `|z| ≤ 1` the Gauss series of
`₂F₁(a, b; c; z)` converges absolutely when `Re(c − a − b) > 0`. -/
theorem summable_norm_gaussTerm_of_re_pos {a b c z : ℂ} (hz : ‖z‖ ≤ 1)
    (h : 0 < (c - a - b).re) :
    Summable fun s : ℕ => ‖(ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
      ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s‖ := by
  have hc : Summable fun s : ℕ => ‖ordinaryHypergeometricCoefficient a b c s‖ := by
    refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr ?_)
      (isBigO_ordinaryHypergeometricCoefficient a b c).norm_left
    simp only [sub_re, add_re, one_re] at h ⊢
    linarith
  refine hc.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_gaussTerm]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

/-- **Absolute convergence of the regularized series on the closed disk** (DLMF §15.2(i)). On
`|z| ≤ 1` the series of `𝐅(a, b; c; z) = ∑ (a)ₙ (b)ₙ zⁿ / (n! Γ(c + n))` converges absolutely when
`Re(c − a − b) > 0`, for every `c`, including the poles `c ∈ {0, −1, −2, …}` of `Γ`. -/
theorem summable_norm_coeff_regularizedGaussHGFunSeries_mul_pow_of_re_pos {a b c z : ℂ}
    (hz : ‖z‖ ≤ 1) (h : 0 < (c - a - b).re) :
    Summable fun n : ℕ => ‖(regularizedGaussHGFunSeries a b c).coeff n * z ^ n‖ := by
  -- Shift `c` upward with DLMF 15.5.15 until `Re c > 0`, where `𝐅 = ₂F₁ / Γ(c)`.
  obtain ⟨N, hN⟩ := exists_nat_gt (-c.re)
  induction N generalizing a c with
  | zero =>
    have hc := ne_neg_natCast_of_re_pos (b := c) (by simp only [CharP.cast_eq_zero] at hN; linarith)
    refine ((summable_norm_gaussTerm_of_re_pos hz h).mul_left ‖(Gamma c)⁻¹‖).congr fun n => ?_
    rw [← Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc, ordinaryHypergeometricSeries,
      FormalMultilinearSeries.coeff_ofScalars, mul_assoc, norm_mul (Gamma c)⁻¹, norm_gaussTerm,
      norm_mul _ (z ^ n), norm_pow]
  | succ N ih =>
    have h₁ := ih (a := a) (c := c + 1) (by simp only [sub_re, add_re, one_re] at h ⊢; linarith)
      (by push_cast at hN; simp only [add_re, one_re]; linarith)
    have h₂ := ih (a := a + 1) (c := c + 1) (by simp only [sub_re, add_re, one_re] at h ⊢; linarith)
      (by push_cast at hN; simp only [add_re, one_re]; linarith)
    refine ((h₁.mul_left ‖c - a‖).add (h₂.mul_left ‖a‖)).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun n => ?_
    rw [coeff_regularizedGaussHGFunSeries_eq_sub_mul_add_mul, add_mul, mul_assoc, mul_assoc,
      ← norm_mul, ← norm_mul]
    exact norm_add_le _ _

/-- **Convergence on the closed disk away from `1`** (DLMF §15.2(i)). On `|z| ≤ 1`, `z ≠ 1`, the
partial sums of the Gauss series of `₂F₁(a, b; c; z)` converge when `Re(c − a − b) > −1`. -/
theorem exists_tendsto_sum_gaussTerm_of_neg_one_lt_re {a b c z : ℂ} (hz : ‖z‖ ≤ 1) (hz₁ : z ≠ 1)
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
      _ ≤ 2 := by
        rw [norm_pow, norm_one]
        linarith [pow_le_one₀ (norm_nonneg z) hz (n := n)]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (hf0.cauchySeq_series_smul_of_summable_norm_sub hvar hgeom)
  exact ⟨L, by simpa only [smul_eq_mul, TauCeti.ordinaryHypergeometricCoefficient_eq_div] using hL⟩

/-- **No absolute convergence on and outside the circle** (DLMF §15.2(i)). On `|z| ≥ 1` the
nonterminating Gauss series of `₂F₁(a, b; c; z)` does not converge absolutely when
`Re(c − a − b) ≤ 0`. -/
theorem not_summable_norm_gaussTerm_of_re_nonpos {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hz : 1 ≤ ‖z‖) (h : (c - a - b).re ≤ 0) :
    ¬ Summable fun s : ℕ => ‖(ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
      ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s‖ := by
  intro hs
  have hs' : Summable fun s : ℕ => ‖ordinaryHypergeometricCoefficient a b c s‖ := by
    refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [norm_gaussTerm]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hz)
  have hσ := Real.summable_nat_rpow.mp
    (summable_of_isBigO_nat hs' (isTheta_ordinaryHypergeometricCoefficient ha hb hc).2.norm_right)
  simp only [sub_re, add_re, one_re] at h hσ
  linarith

/-- **Divergence on and outside the circle** (DLMF §15.2(i)). On `|z| ≥ 1` the partial sums of the
nonterminating Gauss series of `₂F₁(a, b; c; z)` have no limit when `Re(c − a − b) ≤ −1`. -/
theorem not_exists_tendsto_sum_gaussTerm_of_re_le_neg_one {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hz : 1 ≤ ‖z‖) (h : (c - a - b).re ≤ -1) :
    ¬ ∃ L : ℂ, Tendsto (fun N => ∑ s ∈ Finset.range N,
      (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b /
        ((ascPochhammer ℂ s).eval c * (s ! : ℂ)) * z ^ s) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  -- The terms of a convergent series tend to `0`, so the coefficients do as well.
  have hterm := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
  simp only [sub_self, Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left] at hterm
  have hcoef : Tendsto (fun n => ‖ordinaryHypergeometricCoefficient a b c n‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa only [norm_zero] using hterm.norm)
    rw [norm_gaussTerm]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hz)
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
