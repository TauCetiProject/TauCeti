/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Hypergeometric
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# The complete elliptic integral `D(k)` as a Gauss series

For real `k` with `0 < k² < 1`, the complete elliptic integral `D(k) = (K(k) − E(k))/k²`
(DLMF 19.2.6) is a Gauss hypergeometric function (DLMF 15.9.26):

$$
\frac{K(k) - E(k)}{k^2} = \frac{\pi}{4}\, {}_2F_1\!\left(\tfrac12, \tfrac32; 2; k^2\right).
$$

## Main results

* `TauCeti.Real.hasSum_ordinaryHypergeometric`: the real Gauss series converges to `₂F₁` on
  `|x| < 1`.
* `TauCeti.Real.legendreD_eq_ordinaryHypergeometric`: DLMF 15.9.26.

## Implementation notes

The proof is termwise. By `TauCeti.Real.legendreK_eq_ordinaryHypergeometric` and
`TauCeti.Real.legendreEc_eq_ordinaryHypergeometric`,
`K − E = (π/2) (₂F₁(½, ½; 1; m) − ₂F₁(−½, ½; 1; m))` with `m = k²`. The constant terms cancel,
and since `(½)ₙ₊₁ − (−½)ₙ₊₁ = (n + 1) (½)ₙ`, the `(n + 1)`-st term of the difference is `m/2`
times the `n`-th term of `₂F₁(½, 3/2; 2; m)`.
-/

@[expose] public section

open Polynomial Finset

open scoped Nat Real

namespace TauCeti.Real

/-- The real Gauss hypergeometric series converges to `₂F₁` inside the unit interval. -/
theorem hasSum_ordinaryHypergeometric (a b c : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => ((n !⁻¹ : ℝ) * (ascPochhammer ℝ n).eval a *
      (ascPochhammer ℝ n).eval b * ((ascPochhammer ℝ n).eval c)⁻¹) * x ^ n) (₂F₁ a b c x) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) (ordinaryHypergeometricSeries ℝ a b c).radius := by
    refine Metric.eball_subset_eball (one_le_radius_ordinaryHypergeometricSeries ℝ a b c) ?_
    simpa [edist_dist, Real.dist_0_eq_abs] using hx
  have hs := ((ordinaryHypergeometricSeries ℝ a b c).summable_norm_apply hmem).of_norm
  simp only [ordinaryHypergeometricSeries_apply_eq, smul_eq_mul] at hs
  rw [ordinaryHypergeometric_eq_tsum]
  simpa only [smul_eq_mul] using hs.hasSum

/-- `(a)ₙ₊₁ = a (a + 1)ₙ`. -/
private theorem ascPochhammer_succ_eval_left (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval a = a * (ascPochhammer ℝ n).eval (a + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]

/-- **DLMF 15.9.26.** For real `k` with `0 < k² < 1`,
`D(k) = (K(k) − E(k))/k² = (π/4) ₂F₁(½, 3/2; 2; k²)`. -/
theorem legendreD_eq_ordinaryHypergeometric {k : ℝ} (hk₀ : 0 < k ^ 2) (hk : k ^ 2 < 1) :
    (legendreK k - legendreEc k) / k ^ 2 = π / 4 * ₂F₁ (1 / 2 : ℝ) (3 / 2) 2 (k ^ 2) := by
  set m := k ^ 2 with hm
  have hm1 : |m| < 1 := by rwa [abs_of_pos hk₀]
  have hK := hasSum_ordinaryHypergeometric (1 / 2) (1 / 2) 1 hm1
  have hE := hasSum_ordinaryHypergeometric (-1 / 2) (1 / 2) 1 hm1
  have hD := hasSum_ordinaryHypergeometric (1 / 2) (3 / 2) 2 hm1
  -- the difference of the two series, with its vanishing constant term dropped
  have hdiff := (hasSum_nat_add_iff' 1).mpr (hK.sub hE)
  simp only [range_one, sum_singleton, pow_zero, ascPochhammer_zero, eval_one,
    Nat.factorial_zero, Nat.cast_one, inv_one, mul_one, sub_self, sub_zero] at hdiff
  -- the shifted terms are `m/2` times the terms of `₂F₁(½, 3/2; 2; m)`
  have hterm : ∀ n : ℕ,
      ((((n + 1) ! : ℝ)⁻¹ * (ascPochhammer ℝ (n + 1)).eval (1 / 2) *
          (ascPochhammer ℝ (n + 1)).eval (1 / 2) *
          ((ascPochhammer ℝ (n + 1)).eval 1)⁻¹) * m ^ (n + 1) -
        (((n + 1) ! : ℝ)⁻¹ * (ascPochhammer ℝ (n + 1)).eval (-1 / 2) *
          (ascPochhammer ℝ (n + 1)).eval (1 / 2) *
          ((ascPochhammer ℝ (n + 1)).eval 1)⁻¹) * m ^ (n + 1)) =
      m / 2 * (((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval (1 / 2) *
        (ascPochhammer ℝ n).eval (3 / 2) * ((ascPochhammer ℝ n).eval 2)⁻¹) * m ^ n) := by
    intro n
    have h1 : (ascPochhammer ℝ (n + 1)).eval (1 / 2 : ℝ) =
        (ascPochhammer ℝ n).eval (1 / 2) * (1 / 2 + n) := ascPochhammer_succ_eval _ _
    have h2 : (ascPochhammer ℝ (n + 1)).eval (-1 / 2 : ℝ) =
        -1 / 2 * (ascPochhammer ℝ n).eval (1 / 2) := by
      rw [ascPochhammer_succ_eval_left]
      norm_num
    have h3 : (ascPochhammer ℝ n).eval (3 / 2 : ℝ) =
        2 * ((ascPochhammer ℝ n).eval (1 / 2) * (1 / 2 + n)) := by
      rw [← h1, ascPochhammer_succ_eval_left, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
      ring
    have h4 : (ascPochhammer ℝ n).eval (2 : ℝ) = ((n + 1) ! : ℝ) := by
      have h := ascPochhammer_succ_eval_left (1 : ℝ) n
      rw [ascPochhammer_eval_one] at h
      norm_num at h
      exact h.symm
    have hf : ((n + 1) ! : ℝ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
    have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [h1, h2, h3, h4, ascPochhammer_eval_one, hf]
    field_simp
    ring
  have hshift : HasSum (fun n : ℕ => m / 2 * (((n ! : ℝ)⁻¹ * (ascPochhammer ℝ n).eval (1 / 2) *
      (ascPochhammer ℝ n).eval (3 / 2) * ((ascPochhammer ℝ n).eval 2)⁻¹) * m ^ n))
      (₂F₁ (1 / 2 : ℝ) (1 / 2) 1 m - ₂F₁ (-1 / 2 : ℝ) (1 / 2) 1 m) := by
    simpa only [hterm] using hdiff
  have hEq := hshift.unique (hD.mul_left (m / 2))
  rw [legendreK_eq_ordinaryHypergeometric hk, legendreEc_eq_ordinaryHypergeometric hk, ← mul_sub,
    hEq]
  field_simp
  ring

end TauCeti.Real
