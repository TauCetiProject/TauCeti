/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.KummerLaplace
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Saddle-point asymptotics and recurrence for Legendre's incomplete Gamma continued fraction

For `z ∈ Complex.slitPlane`, Legendre's continued fraction for the normalized upper incomplete
Gamma combination `z^{-a} e^z Γ(a, z) = K(0, a - 1; z)` has head `0`, partial denominators
`b_n = 1`, and partial numerators `a₁ = z⁻¹`, `a_{2k} = (k - a) z⁻¹`, `a_{2k+1} = k z⁻¹`
(`k ≥ 1`; non-terminating when `a ∉ {1, 2, ...}`). In terms of the rotated Kummer-Laplace
integrals `Complex.kummerLaplace`, the sequence `(f_n)_{n ≥ 0}` defined by
* `f₀ = 1`,
* `f_{2k+1} = -(1 - a)_k z^{-k} K(k, a - 1 - k; z)`,
* `f_{2k+2} = (1 - a)_{k+1} z^{-(k+1)} K(k, a - 2 - k; z)`

satisfies the associated three-term recurrence `f_{n+2} = f_{n+1} + a_{n+1} f_n` on
`Complex.slitPlane` with `f₀ = 1` and `-f₁ / f₀ = K(0, a - 1; z)`. In Gautschi's analysis of
three-term recurrence relations, this sequence is constructed as the candidate minimal solution
used to apply Pincherle's theorem in the non-terminating regime `a ∉ {1, 2, ...}`.

On `Complex.slitPlane`, rescaling the rotated Laplace contour around the saddle point
`t_k = √(k / z)` gives the saddle-point asymptotic of `K(k, a - 1 - k; z)` as `k → ∞`, supplying
both eventual nonvanishing of `f_n` (when `a ∉ {1, 2, ...}`) and the stretched-exponential factor
`exp(-2 √(kz))` needed for Pincherle's theorem.

## Main definitions

* `Complex.upperGammaContFracPartNum a z n` — the `n`-th partial numerator of Legendre's continued
  fraction for `z^{-a} e^z Γ(a, z)`.
* `Complex.upperGammaContFracSolution a z n` — the Kummer-Laplace solution sequence `f_n` of the
  associated three-term recurrence on `Complex.slitPlane`, normalized by `f₀ = 1`.

## Main results

* `Complex.kummerLaplace_isEquivalent` — on `slitPlane`, as `k → ∞`,
  `kummerLaplace k (a - 1 - k) z ~ √π e^{z/2} z^{-a/2 - 1/4} k^{a/2 - 1/4} e^{-2 √(kz)}`.
* `Complex.eventually_kummerLaplace_ne_zero` — for `z ∈ slitPlane`,
  `kummerLaplace k (a - 1 - k) z ≠ 0` eventually as `k → ∞`.
* `Complex.upperGammaContFracPartNum_ne_zero_iff` — `upperGammaContFracPartNum a z n ≠ 0` iff
  `z ≠ 0` and `(Even n → a ≠ (n / 2 : ℕ))`.
* `Complex.upperGammaContFracSolution_add_two` — on `slitPlane`,
  `f (n + 2) = f (n + 1) + upperGammaContFracPartNum a z (n + 1) * f n`.
* `Complex.eventually_upperGammaContFracSolution_ne_zero` — for `z ∈ slitPlane` and `a ≠ m + 1`
  (`m : ℕ`), `upperGammaContFracSolution a z n ≠ 0` eventually as `n → ∞`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9) and
  [§13.8](https://dlmf.nist.gov/13.8).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Polynomial Set
open scoped Nat Real Topology

namespace Complex

/-! ### Saddle-point asymptotics of `kummerLaplace k (a - 1 - k) z` -/

private theorem rpow_neg_quarter {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-1 / 4 : ℝ) = (x ^ (1 / 4 : ℝ))⁻¹ := by
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg hx]

private theorem rpow_quarter_sq (k : ℕ) :
    ((k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k), Real.sqrt_eq_rpow]; norm_num

private abbrev saddleU (k : ℕ) (v : ℝ) : ℝ := 1 + (k : ℝ) ^ (-1 / 4 : ℝ) * v

private abbrev saddleY (σ : ℝ) (k : ℕ) (v : ℝ) : ℝ := saddleU k v + σ / Real.sqrt k

private theorem saddle_u_pos {k : ℕ} (hk : 1 ≤ k) {v : ℝ} (hv : -(k : ℝ) ^ (1 / 4 : ℝ) < v) :
    0 < saddleU k v := by
  have hq : 0 < (k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _
  dsimp only [saddleU]; rw [rpow_neg_quarter (Nat.cast_nonneg k)]
  have hdiv : -1 < v / (k : ℝ) ^ (1 / 4 : ℝ) := by rw [lt_div_iff₀ hq]; linarith
  linarith [div_eq_inv_mul v ((k : ℝ) ^ (1 / 4 : ℝ))]

private theorem tendsto_saddle_u (v : ℝ) :
    Tendsto (fun k : ℕ => saddleU k v) atTop (𝓝 1) := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ (-1 / 4 : ℝ)) atTop (𝓝 0) := by
    rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  simpa [saddleU] using tendsto_const_nhds.add (ht.mul_const v)

private theorem kummerLaplace_eq_sqrt_integral (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerLaplace c d z =
      (z ^ (1 / 2 : ℂ))⁻¹ *
        ∫ s in Ioi (0 : ℝ),
          cexp (-(z ^ (1 / 2 : ℂ)) * s) * ((s : ℂ) * (z ^ (1 / 2 : ℂ))⁻¹) ^ c *
            (1 + (s : ℂ) * (z ^ (1 / 2 : ℂ))⁻¹) ^ d := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  set ω : ℂ := cexp (-(z.arg / 2 : ℝ) * I)
  set ρ : ℝ := Real.exp (-Real.log ‖z‖ / 2)
  have hζ0 : ζ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))
  have hζ_inv : ζ⁻¹ = (ρ : ℂ) * ω := by
    rw [← cpow_neg, cpow_def_of_ne_zero (slitPlane_ne_zero hz), ← re_add_im (log z),
      log_re, log_im]
    have hsplit : ((Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * I) * -(1 / 2 : ℂ) =
        ((-Real.log ‖z‖ / 2 : ℝ) : ℂ) + (-(z.arg / 2 : ℝ) * I) := by push_cast; ring
    rw [hsplit, Complex.exp_add, ← ofReal_exp]
  have hρ : 0 < ρ := Real.exp_pos _
  have hsub :
      (∫ r in Ioi (0 : ℝ), cexp (-z * (r * ω)) * (r * ω) ^ c * (1 + r * ω) ^ d) =
        ρ • ∫ s in Ioi (0 : ℝ),
          cexp (-z * (((ρ * s : ℝ) : ℂ) * ω)) * (((ρ * s : ℝ) : ℂ) * ω) ^ c *
            (1 + ((ρ * s : ℝ) : ℂ) * ω) ^ d := by
    simpa only [mul_zero] using (integral_comp_mul_left_Ioi'
      (fun r : ℝ => cexp (-z * (r * ω)) * (r * ω) ^ c * (1 + r * ω) ^ d) 0 hρ).symm
  rw [kummerLaplace_def, hsub, real_smul, ← mul_assoc, mul_comm ω (ρ : ℂ), ← hζ_inv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  have hrw : ((ρ * s : ℝ) : ℂ) * ω = (s : ℂ) * ζ⁻¹ := by rw [ofReal_mul, hζ_inv]; ring
  have hzeq : -z * ((s : ℂ) * ζ⁻¹) = -ζ * (s : ℂ) := by
    have hz_sq : ζ ^ 2 = z := by simp [ζ, one_div]
    calc -z * ((s : ℂ) * ζ⁻¹) = -ζ * (s : ℂ) * (ζ * ζ⁻¹) := by rw [← hz_sq]; ring
      _ = -ζ * (s : ℂ) := by rw [mul_inv_cancel₀ hζ0, mul_one]
  rw [hrw, hzeq]

private def kummerLaplaceSaddleCore (a z : ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  let u : ℝ := saddleU k v
  let ζ : ℂ := z ^ (1 / 2 : ℂ)
  ((u : ℂ) + ζ / (Real.sqrt k : ℂ)) ^ (a - 1) *
    cexp (-(Real.sqrt k : ℂ) * ζ * ((u : ℂ) - 2)) *
    ((1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k)⁻¹

private def kummerLaplaceSaddleIntegrand (a z : ℂ) (k : ℕ) : ℝ → ℂ :=
  (Ioi (-(k : ℝ) ^ (1 / 4 : ℝ))).indicator (kummerLaplaceSaddleCore a z k)

private theorem saddle_prefactor_eq (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) {k : ℕ} (hk : 1 ≤ k) :
    (z ^ (1 / 2 : ℂ))⁻¹ * (((k : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt k : ℂ) ^ (a - 1) * (z ^ (1 / 2 : ℂ))⁻¹ ^ (a - 1)) =
      (k : ℂ) ^ (a / 2 - 1 / 4) * (z ^ (1 / 2 : ℂ))⁻¹ ^ a := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ0 : ζ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk_pos
  have hk_ne : ((k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk_pos.ne'
  have hsk_ne : (Real.sqrt k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsk_pos.ne'
  have hk_pref : (((k : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * (Real.sqrt k : ℂ) ^ (a - 1) =
      (k : ℂ) ^ (a / 2 - 1 / 4) := by
    rw [ofReal_cpow hk_pos.le, show (k : ℂ) = ((k : ℝ) : ℂ) by simp,
      cpow_def_of_ne_zero hk_ne, cpow_def_of_ne_zero hsk_ne, cpow_def_of_ne_zero hk_ne,
      ← Complex.exp_add, ← ofReal_log hk_pos.le, ← ofReal_log hsk_pos.le, Real.log_sqrt hk_pos.le]
    congr 1; push_cast; ring
  have hζ_pref : ζ⁻¹ * (ζ⁻¹) ^ (a - 1) = (ζ⁻¹) ^ a := by
    nth_rw 1 [← cpow_one ζ⁻¹]
    rw [← cpow_add _ _ (inv_ne_zero hζ0)]; congr 1; ring
  linear_combination (ζ⁻¹ * (ζ⁻¹) ^ (a - 1)) * hk_pref + (k : ℂ) ^ (a / 2 - 1 / 4) * hζ_pref

private theorem kummerLaplace_saddle_pointwise (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    {k : ℕ} (hk : 1 ≤ k) {v : ℝ} (hv : -(k : ℝ) ^ (1 / 4 : ℝ) < v) :
    let ζ : ℂ := z ^ (1 / 2 : ℂ)
    let q₄ : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
    let s : ℝ := Real.sqrt k + q₄ * v
    ζ⁻¹ * (q₄ : ℂ) *
        (cexp (-ζ * s) * ((s : ℂ) * ζ⁻¹) ^ k * (1 + (s : ℂ) * ζ⁻¹) ^ (a - 1 - k)) =
      (k : ℂ) ^ (a / 2 - 1 / 4) * (ζ⁻¹) ^ a * cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) *
        kummerLaplaceSaddleCore a z k v := by
  intro ζ q₄ s
  set u : ℝ := saddleU k v
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk_pos
  have hu_pos : 0 < u := saddle_u_pos hk hv
  have hs_eq : s = Real.sqrt k * u := by
    have hmul : Real.sqrt k * (k : ℝ) ^ (-1 / 4 : ℝ) = q₄ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk_pos]; norm_num [q₄]
    dsimp only [s, u, saddleU]; linear_combination -hmul * v
  have hs_pos : 0 < s := by rw [hs_eq]; positivity
  have hζ0 : ζ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))
  have hζ_re : 0 < ζ.re := by simpa [ζ, sqrt, one_div] using (sqrt_re_pos_iff z).mpr hz
  have hζinv_re : 0 < (ζ⁻¹).re := by
    rw [inv_re]; exact div_pos hζ_re (normSq_pos.mpr hζ0)
  have h1s_re : 0 < (1 + (s : ℂ) * ζ⁻¹).re := by rw [add_re, one_re, re_ofReal_mul]; nlinarith
  have h1s_ne : 1 + (s : ℂ) * ζ⁻¹ ≠ 0 := fun h => by rw [h, zero_re] at h1s_re; linarith
  have hk_pow : ((s : ℂ) * ζ⁻¹) ^ k * (1 + (s : ℂ) * ζ⁻¹) ^ (a - 1 - k) =
      (1 + (s : ℂ) * ζ⁻¹) ^ (a - 1) * ((1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k)⁻¹ := by
    have hfac_k : (1 + (s : ℂ) * ζ⁻¹) ^ k =
        ((s : ℂ) * ζ⁻¹) ^ k * (1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k := by
      rw [← mul_pow]; congr 1; rw [hs_eq, ofReal_mul]
      field_simp [ofReal_ne_zero.mpr hsk_pos.ne', ofReal_ne_zero.mpr hu_pos.ne', hζ0]; ring
    have hsζ_ne : ((s : ℂ) * ζ⁻¹) ^ k ≠ 0 :=
      pow_ne_zero k (mul_ne_zero (ofReal_ne_zero.mpr hs_pos.ne') (inv_ne_zero hζ0))
    rw [cpow_sub _ _ h1s_ne, cpow_natCast, div_eq_mul_inv, hfac_k, mul_inv]
    linear_combination (1 + (s : ℂ) * ζ⁻¹) ^ (a - 1) *
      ((1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k)⁻¹ * mul_inv_cancel₀ hsζ_ne
  have hcpow_split : (1 + (s : ℂ) * ζ⁻¹) ^ (a - 1) =
      (Real.sqrt k : ℂ) ^ (a - 1) * (ζ⁻¹) ^ (a - 1) *
        ((u : ℂ) + ζ / (Real.sqrt k : ℂ)) ^ (a - 1) := by
    have hprod : 1 + (s : ℂ) * ζ⁻¹ =
        ((Real.sqrt k : ℂ) * ζ⁻¹) * ((u : ℂ) + ζ / (Real.sqrt k : ℂ)) := by
      rw [hs_eq, ofReal_mul]; field_simp [ofReal_ne_zero.mpr hsk_pos.ne', hζ0]; ring
    have hre1 : 0 < ((Real.sqrt k : ℂ) * ζ⁻¹).re := by rw [re_ofReal_mul]; positivity
    have hre2 : 0 < ((u : ℂ) + ζ / (Real.sqrt k : ℂ)).re := by
      rw [add_re, ofReal_re, div_ofReal_re]
      exact add_pos hu_pos (div_pos hζ_re hsk_pos)
    rw [hprod, TauCeti.mul_cpow_of_re_pos hre1 hre2, TauCeti.ofReal_mul_cpow hsk_pos.le]
  have hexp_split : cexp (-ζ * (s : ℂ)) =
      cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) * cexp (-(Real.sqrt k : ℂ) * ζ * ((u : ℂ) - 2)) := by
    have hkz : ((k : ℂ) * z) ^ (1 / 2 : ℂ) = (Real.sqrt k : ℂ) * ζ := by
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) by simp, TauCeti.ofReal_mul_cpow hk_pos.le,
        Real.sqrt_eq_rpow, ofReal_cpow hk_pos.le]; push_cast; rfl
    rw [← Complex.exp_add, hkz, hs_eq, ofReal_mul]; congr 1; ring
  unfold kummerLaplaceSaddleCore; dsimp only
  rw [mul_assoc (cexp _), hk_pow, hcpow_split, hexp_split]
  linear_combination (cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) *
    ((u : ℂ) + ζ / (Real.sqrt k : ℂ)) ^ (a - 1) * cexp (-(Real.sqrt k : ℂ) * ζ * ((u : ℂ) - 2)) *
    ((1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k)⁻¹) * saddle_prefactor_eq a hz hk

private theorem kummerLaplace_eq_saddle_integral (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    {k : ℕ} (hk : 1 ≤ k) :
    kummerLaplace k (a - 1 - k) z =
      (k : ℂ) ^ (a / 2 - 1 / 4) * (z ^ (1 / 2 : ℂ))⁻¹ ^ a *
        cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) *
        ∫ v : ℝ, kummerLaplaceSaddleIntegrand a z k v := by
  have hq₄ : 0 < (k : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _
  have h0 : Real.sqrt k + (k : ℝ) ^ (1 / 4 : ℝ) * -(k : ℝ) ^ (1 / 4 : ℝ) = 0 := by
    rw [mul_neg, ← sq, rpow_quarter_sq k, add_neg_cancel]
  have hsub := (h0 ▸ TauCeti.integral_comp_add_mul_left_Ioi'
    (fun s : ℝ => cexp (-(z ^ (1 / 2 : ℂ)) * s) * ((s : ℂ) * (z ^ (1 / 2 : ℂ))⁻¹) ^ k *
      (1 + (s : ℂ) * (z ^ (1 / 2 : ℂ))⁻¹) ^ (a - 1 - k))
    (-(k : ℝ) ^ (1 / 4 : ℝ)) (Real.sqrt k) hq₄).symm
  rw [kummerLaplace_eq_sqrt_integral k (a - 1 - k) hz, hsub, real_smul, ← mul_assoc,
    ← integral_const_mul, kummerLaplaceSaddleIntegrand, integral_indicator measurableSet_Ioi,
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun v hv =>
    kummerLaplace_saddle_pointwise a hz hk hv

private theorem aestronglyMeasurable_kummerLaplaceSaddleIntegrand (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) {k : ℕ} (hk : 1 ≤ k) :
    AEStronglyMeasurable (kummerLaplaceSaddleIntegrand a z k) volume := by
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hζ_re : 0 < (z ^ (1 / 2 : ℂ)).re := by simpa [sqrt, one_div] using (sqrt_re_pos_iff z).mpr hz
  refine (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr
    (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
  intro v hv; unfold kummerLaplaceSaddleCore
  have hu_pos : 0 < saddleU k v := saddle_u_pos hk hv
  have hc_u : ContinuousAt (fun x : ℝ => ((saddleU k x : ℝ) : ℂ)) v :=
    (continuous_ofReal.comp
      (continuous_const.add (continuous_const.mul continuous_id))).continuousAt
  have hslit : ((saddleU k v : ℝ) : ℂ) + z ^ (1 / 2 : ℂ) / (Real.sqrt k : ℂ) ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (by rw [add_re, ofReal_re, div_ofReal_re]; positivity))
  have h1_ne : (1 + z ^ (1 / 2 : ℂ) / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))) ^ k ≠ 0 := by
    refine pow_ne_zero k fun h0 => ?_
    have hre : 0 < (1 + z ^ (1 / 2 : ℂ) / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))).re := by
      rw [add_re, one_re, ← ofReal_mul, div_ofReal_re]; positivity
    rw [h0, zero_re] at hre; linarith
  exact ((((hc_u.add continuousAt_const).cpow continuousAt_const hslit).mul
    ((continuousAt_const.mul (hc_u.sub continuousAt_const)).cexp)).mul
    (((continuousAt_const.add (continuousAt_const.div
      (continuousAt_const.mul hc_u) (mul_ne_zero (ofReal_ne_zero.mpr hsk_pos.ne')
        (ofReal_ne_zero.mpr hu_pos.ne')))).pow k).inv₀ h1_ne)).continuousWithinAt

private theorem tendsto_saddle_log_remainder (ζ : ℂ) (v : ℝ) :
    Tendsto (fun k : ℕ =>
      (k : ℂ) * (log (1 + ζ / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))) -
        logTaylor 3 (ζ / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))))) atTop (𝓝 0) := by
  set w : ℕ → ℂ := fun k => ζ / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))
  have ht_sk : Tendsto (fun k : ℕ => Real.sqrt k) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_
    (by simpa using (tendsto_inv_atTop_zero.comp ht_sk).const_mul (16 * ‖ζ‖ ^ 3 / 3))
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_saddle_u v).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    ht_sk.eventually_gt_atTop (4 * (‖ζ‖ + 1))] with k hk1 hu_half hsk_big
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk_pos
  have hw_le : ‖w k‖ ≤ 2 * ‖ζ‖ / Real.sqrt k := by
    dsimp only [w]
    rw [norm_div, norm_mul, norm_real, Real.norm_of_nonneg hsk_pos.le, norm_real,
      Real.norm_of_nonneg (by linarith), div_le_div_iff₀ (mul_pos hsk_pos (by linarith)) hsk_pos]
    calc ‖ζ‖ * Real.sqrt k = (‖ζ‖ * Real.sqrt k) * 1 := (mul_one _).symm
      _ ≤ (‖ζ‖ * Real.sqrt k) * (2 * saddleU k v) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * ‖ζ‖ * (Real.sqrt k * saddleU k v) := by ring
  have hw_half : ‖w k‖ < 1 / 2 := hw_le.trans_lt <| by
    rw [div_lt_iff₀ hsk_pos]; nlinarith [norm_nonneg ζ]
  have h1w_pos : 0 < 1 - ‖w k‖ := by linarith
  have h1w : (1 - ‖w k‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ h1w_pos two_pos]; linarith
  have hlt := norm_log_sub_logTaylor_le 2 (hw_half.trans (by norm_num))
  norm_num at hlt; rw [norm_mul, Complex.norm_natCast]
  calc (k : ℝ) * ‖log (1 + w k) - logTaylor 3 (w k)‖
      ≤ (k : ℝ) * (‖w k‖ ^ 3 * (1 - ‖w k‖)⁻¹ / 3) := by gcongr
    _ ≤ (k : ℝ) * ((2 * ‖ζ‖ / Real.sqrt k) ^ 3 * 2 / 3) := by gcongr
    _ = 16 * ‖ζ‖ ^ 3 / 3 * (Real.sqrt k)⁻¹ := by
        have hsq : (k : ℝ) = Real.sqrt k ^ 2 := (Real.sq_sqrt hk_pos.le).symm
        nth_rw 1 [hsq]; field_simp [hsk_pos.ne']; ring

private theorem tendsto_saddle_quadratic_phase (z : ℂ) (v : ℝ) :
    let ζ : ℂ := z ^ (1 / 2 : ℂ)
    Tendsto (fun k : ℕ => -(Real.sqrt k : ℂ) * ζ * ((saddleU k v : ℂ) - 2) -
        (k : ℂ) * logTaylor 3 (ζ / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))))
      atTop (𝓝 (-ζ * (v : ℂ) ^ 2 + z / 2)) := by
  intro ζ
  set u : ℕ → ℝ := fun k => saddleU k v
  set w : ℕ → ℂ := fun k => ζ / ((Real.sqrt k : ℂ) * (u k : ℂ))
  have hu_c : Tendsto (fun k : ℕ => (u k : ℂ)) atTop (𝓝 1) :=
    continuous_ofReal.continuousAt.tendsto.comp (tendsto_saddle_u v)
  have hlim : Tendsto (fun k : ℕ => -ζ * (v : ℂ) ^ 2 / (u k : ℂ) + z / (2 * (u k : ℂ) ^ 2))
      atTop (𝓝 (-ζ * (v : ℂ) ^ 2 + z / 2)) := by
    simpa using (tendsto_const_nhds.div hu_c one_ne_zero).add
      (tendsto_const_nhds.div ((hu_c.pow 2).const_mul 2) (by norm_num))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_saddle_u v).eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk1 hu0
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hsk_c : (Real.sqrt k : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hk_pos).ne'
  have hu_ne : (u k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
  have hu_sub : ((u k : ℂ) - 1) ^ 2 = ((Real.sqrt k : ℂ))⁻¹ * (v : ℂ) ^ 2 := by
    have hsq : ((k : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 = (Real.sqrt k)⁻¹ := by
      rw [rpow_neg_quarter hk_pos.le, inv_pow, rpow_quarter_sq k]
    dsimp only [u, saddleU]; push_cast
    rw [show 1 + (((k : ℝ) ^ (-1 / 4 : ℝ) : ℝ) : ℂ) * (v : ℂ) - 1 =
      (((k : ℝ) ^ (-1 / 4 : ℝ) : ℝ) : ℂ) * (v : ℂ) by ring, mul_pow, ← ofReal_pow, hsq, ofReal_inv]
  have hu_sub' : (Real.sqrt k : ℂ) * ((u k : ℂ) - 1) ^ 2 = (v : ℂ) ^ 2 := by
    rw [hu_sub, ← mul_assoc, mul_inv_cancel₀ hsk_c, one_mul]
  have hlt3 : logTaylor 3 (w k) = w k - (w k) ^ 2 / 2 := by
    simp [logTaylor_succ, logTaylor_zero]; ring
  have hsk_sq : (Real.sqrt k : ℂ) ^ 2 = (k : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hk_pos.le, ofReal_natCast]
  have hz_sq : ζ ^ 2 = z := by simp [ζ, one_div]
  have h1 : (Real.sqrt k : ℂ) ^ 2 * (ζ / ((Real.sqrt k : ℂ) * (u k : ℂ))) =
      (Real.sqrt k : ℂ) * ζ / (u k : ℂ) := by field_simp [hsk_c, hu_ne]
  have h2 : (Real.sqrt k : ℂ) ^ 2 * ((ζ / ((Real.sqrt k : ℂ) * (u k : ℂ))) ^ 2 / 2) =
      z / (2 * (u k : ℂ) ^ 2) := by rw [← hz_sq]; field_simp [hsk_c, hu_ne]
  have h3 : -(Real.sqrt k : ℂ) * ζ * ((u k : ℂ) - 2) - (Real.sqrt k : ℂ) * ζ / (u k : ℂ) =
      -ζ * (v : ℂ) ^ 2 / (u k : ℂ) := by
    rw [← hu_sub']; field_simp [hu_ne]; ring
  have h4 : (k : ℂ) * logTaylor 3 (w k) =
      (Real.sqrt k : ℂ) * ζ / (u k : ℂ) - z / (2 * (u k : ℂ) ^ 2) := by
    rw [hlt3, ← hsk_sq, mul_sub]; dsimp only [w]; rw [h1, h2]
  have hu_def : saddleU k v = u k := rfl
  have hw_def : ζ / ((Real.sqrt k : ℂ) * (u k : ℂ)) = w k := rfl
  rw [hu_def, hw_def, h4]
  linear_combination -h3

private theorem tendsto_kummerLaplaceSaddleIntegrand (a z : ℂ) (v : ℝ) :
    Tendsto (fun k : ℕ => kummerLaplaceSaddleIntegrand a z k v) atTop
      (𝓝 (cexp (-(z ^ (1 / 2 : ℂ)) * (v : ℂ) ^ 2 + z / 2))) := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  set w : ℕ → ℂ := fun k => ζ / ((Real.sqrt k : ℂ) * (saddleU k v : ℂ))
  have ht_sk : Tendsto (fun k : ℕ => Real.sqrt k) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ht_pow1 :
      Tendsto (fun k : ℕ => ((saddleU k v : ℂ) + ζ / (Real.sqrt k : ℂ)) ^ (a - 1)) atTop (𝓝 1) := by
    have hu_c := continuous_ofReal.continuousAt.tendsto.comp (tendsto_saddle_u v)
    have hbase : Tendsto (fun k : ℕ => (saddleU k v : ℂ) + ζ / (Real.sqrt k : ℂ)) atTop (𝓝 1) := by
      simpa [div_eq_mul_inv] using hu_c.add (tendsto_const_nhds.mul
        (continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp ht_sk)))
    simpa using hbase.cpow tendsto_const_nhds (by simp [slitPlane])
  have ht_exp :=
    ((tendsto_saddle_quadratic_phase z v).sub (tendsto_saddle_log_remainder ζ v)).cexp
  rw [sub_zero] at ht_exp
  have hprod := ht_pow1.mul ht_exp; rw [one_mul] at hprod
  have ht_q4 : Tendsto (fun k : ℕ => -(k : ℝ) ^ (1 / 4 : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_saddle_u v).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    ht_sk.eventually_gt_atTop (4 * (‖ζ‖ + 1)),
    ht_q4.eventually_lt_atBot v] with k hk1 hu_half hsk_big hkv
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk1)
  have hw1 : ‖w k‖ < 1 := by
    dsimp only [w]
    rw [norm_div, norm_mul, norm_real, Real.norm_of_nonneg hsk_pos.le, norm_real,
      Real.norm_of_nonneg (by linarith), div_lt_iff₀ (mul_pos hsk_pos (by linarith))]
    nlinarith [norm_nonneg ζ]
  have hpow_log : ((1 + w k) ^ k)⁻¹ = cexp (-(k : ℂ) * log (1 + w k)) := by
    nth_rw 1 [← exp_log (slitPlane_ne_zero (mem_slitPlane_of_norm_lt_one hw1))]
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg, neg_mul]
  rw [kummerLaplaceSaddleIntegrand, indicator_of_mem hkv]
  unfold kummerLaplaceSaddleCore
  dsimp only [ζ, w] at hpow_log ⊢
  rw [hpow_log, mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]
  congr 2; ring

private theorem norm_saddle_cpow_factor_le (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    {k : ℕ} (hk : 1 ≤ k) {v : ℝ} (hv : -(k : ℝ) ^ (1 / 4 : ℝ) < v) :
    let ζ : ℂ := z ^ (1 / 2 : ℂ)
    let y : ℝ := saddleY ζ.re k v
    let m : ℕ := ⌈|(a - 1).re|⌉₊
    ‖((saddleU k v : ℂ) + ζ / (Real.sqrt k : ℂ)) ^ (a - 1)‖ ≤
      Real.exp (π * |(a - 1).im|) * (‖ζ‖ / ζ.re) ^ m * ((y ^ m)⁻¹ + y ^ m) := by
  intro ζ y m
  set σ : ℝ := ζ.re
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hσ : 0 < σ := by simpa [σ, ζ, sqrt, one_div] using (sqrt_re_pos_iff z).mpr hz
  have hu : 0 < saddleU k v := saddle_u_pos hk hv
  have hy : 0 < y := by dsimp only [y, saddleY]; positivity
  set q : ℂ := (saddleU k v : ℂ) + ζ / (Real.sqrt k : ℂ)
  have hq_lo : y ≤ ‖q‖ := by
    have hre : q.re = y := by dsimp only [q, y, saddleY]; rw [add_re, ofReal_re, div_ofReal_re]
    exact hre ▸ re_le_norm q
  have hζ_ge : 1 ≤ ‖ζ‖ / σ := (one_le_div hσ).mpr (re_le_norm ζ)
  have hq_hi : ‖q‖ ≤ (‖ζ‖ / σ) * y := by
    calc ‖q‖ ≤ ‖(saddleU k v : ℂ)‖ + ‖ζ / (Real.sqrt k : ℂ)‖ := norm_add_le _ _
      _ = saddleU k v + ‖ζ‖ / Real.sqrt k := by
          rw [norm_real, Real.norm_of_nonneg hu.le, norm_div, norm_real,
            Real.norm_of_nonneg hsk_pos.le]
      _ = saddleU k v + (‖ζ‖ / σ) * (σ / Real.sqrt k) := by field_simp [hσ.ne']
      _ ≤ (‖ζ‖ / σ) * y := by dsimp only [y, saddleY]; nlinarith
  have hm_re : -(m : ℝ) ≤ (a - 1).re ∧ (a - 1).re ≤ (m : ℝ) :=
    ⟨by linarith [neg_abs_le (a - 1).re, Nat.le_ceil |(a - 1).re|],
      (le_abs_self _).trans (Nat.le_ceil _)⟩
  have hrpow : ‖q‖ ^ (a - 1).re ≤ (‖ζ‖ / σ) ^ m * ((y ^ m)⁻¹ + y ^ m) := by
    rcases le_or_gt ‖q‖ 1 with hq1 | hq1
    · have h1 : ‖q‖ ^ (a - 1).re ≤ y ^ (-(m : ℝ)) :=
        (Real.rpow_le_rpow_of_exponent_ge (hy.trans_le hq_lo) hq1 hm_re.1).trans
          (Real.rpow_le_rpow_of_nonpos hy hq_lo (neg_nonpos.mpr (Nat.cast_nonneg m)))
      rw [Real.rpow_neg hy.le, Real.rpow_natCast] at h1
      nlinarith [one_le_pow₀ (n := m) hζ_ge, pow_pos hy m, inv_pos.mpr (pow_pos hy m)]
    · have h1 : ‖q‖ ^ (a - 1).re ≤ ((‖ζ‖ / σ) * y) ^ m := by
        calc ‖q‖ ^ (a - 1).re ≤ ‖q‖ ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1.le hm_re.2
          _ = ‖q‖ ^ m := Real.rpow_natCast _ _
          _ ≤ ((‖ζ‖ / σ) * y) ^ m := pow_le_pow_left₀ (norm_nonneg _) hq_hi m
      rw [mul_pow] at h1
      nlinarith [inv_nonneg.mpr (pow_nonneg hy.le m), pow_nonneg (zero_le_one.trans hζ_ge) m]
  calc ‖q ^ (a - 1)‖ ≤ ‖q‖ ^ (a - 1).re * (Real.exp (q.arg * (a - 1).im))⁻¹ := by
        rw [← div_eq_mul_inv]; exact norm_cpow_le _ _
    _ ≤ ((‖ζ‖ / σ) ^ m * ((y ^ m)⁻¹ + y ^ m)) * Real.exp (π * |(a - 1).im|) :=
        mul_le_mul hrpow (inv_exp_arg_mul_le_exp_pi_mul_abs _ _) (by positivity) (by positivity)
    _ = Real.exp (π * |(a - 1).im|) * (‖ζ‖ / σ) ^ m * ((y ^ m)⁻¹ + y ^ m) := by ring

private theorem norm_kummerLaplaceSaddleCore_exp_bound (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    {k : ℕ} (hk : 1 ≤ k) {v : ℝ} (hv : -(k : ℝ) ^ (1 / 4 : ℝ) < v) :
    let ζ : ℂ := z ^ (1 / 2 : ℂ)
    let y : ℝ := saddleY ζ.re k v
    let m : ℕ := ⌈|(a - 1).re|⌉₊
    ‖kummerLaplaceSaddleCore a z k v‖ ≤
      (Real.exp (π * |(a - 1).im|) * (‖ζ‖ / ζ.re) ^ m * Real.exp (ζ.re ^ 2)) *
        (((y ^ m)⁻¹ + y ^ m) * Real.exp (-Real.sqrt k * ζ.re * ((y - 1) ^ 2 / y))) := by
  intro ζ y m
  set σ : ℝ := ζ.re; set u : ℝ := saddleU k v; set δ : ℝ := σ / Real.sqrt k
  have hy_eq : y = u + δ := rfl
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsk_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk_pos
  have hσ : 0 < σ := by simpa [σ, ζ, sqrt, one_div] using (sqrt_re_pos_iff z).mpr hz
  have hu : 0 < u := saddle_u_pos hk hv
  have hy : 0 < y := by rw [hy_eq]; dsimp only [δ]; positivity
  have h1w_inv : ‖((1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k)⁻¹‖ ≤
      Real.exp (-Real.sqrt k * σ / y) := by
    have hre : y / u ≤ ‖1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))‖ := by
      refine (le_of_eq ?_).trans (re_le_norm _)
      rw [add_re, one_re, ← ofReal_mul, div_ofReal_re, ← div_div, hy_eq, add_div, div_self hu.ne']
    have he1 : u / y ≤ Real.exp (-δ / y) := by
      rw [show u / y = -δ / y + 1 by rw [hy_eq, div_add_one (hy_eq ▸ hy.ne')]; ring]
      exact Real.add_one_le_exp _
    rw [norm_inv, norm_pow]
    calc (‖1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))‖ ^ k)⁻¹
        ≤ ((y / u) ^ k)⁻¹ :=
          inv_anti₀ (pow_pos (by positivity) k) (pow_le_pow_left₀ (by positivity) hre k)
      _ ≤ (Real.exp (-δ / y)) ^ k := by
          rw [← inv_pow, inv_div]; exact pow_le_pow_left₀ (by positivity) he1 k
      _ = Real.exp (-Real.sqrt k * σ / y) := by
          rw [← Real.exp_nat_mul]; congr 1; dsimp only [δ]
          field_simp [hsk_pos.ne', hy.ne']; rw [Real.sq_sqrt hk_pos.le]
  have hexp_norm : ‖cexp (-(Real.sqrt k : ℂ) * ζ * ((u : ℂ) - 2))‖ =
      Real.exp (-Real.sqrt k * σ * (u - 2)) := by
    rw [norm_exp, show -(Real.sqrt k : ℂ) * ζ * ((u : ℂ) - 2) =
      ((-Real.sqrt k * (u - 2) : ℝ) : ℂ) * ζ by push_cast; ring, re_ofReal_mul]
    congr 1; dsimp only [σ]; ring
  have hexp_comb : Real.exp (-Real.sqrt k * σ * (u - 2)) * Real.exp (-Real.sqrt k * σ / y) =
      Real.exp (σ ^ 2) * Real.exp (-Real.sqrt k * σ * ((y - 1) ^ 2 / y)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1
    have hu_eq : u = y - δ := by linarith [hy_eq]
    have hδ_mul : Real.sqrt k * δ = σ := mul_div_cancel₀ σ hsk_pos.ne'
    apply mul_right_cancel₀ hy.ne'
    have hy1 : (-Real.sqrt k * σ / y) * y = -Real.sqrt k * σ := div_mul_cancel₀ _ hy.ne'
    have hy2 : (-Real.sqrt k * σ * ((y - 1) ^ 2 / y)) * y = -Real.sqrt k * σ * (y - 1) ^ 2 := by
      rw [mul_assoc, div_mul_cancel₀ _ hy.ne']
    rw [hu_eq]; linear_combination hy1 - hy2 + σ * y * hδ_mul
  unfold kummerLaplaceSaddleCore; dsimp only; rw [norm_mul, norm_mul, hexp_norm]
  calc ‖((u : ℂ) + ζ / (Real.sqrt k : ℂ)) ^ (a - 1)‖ * Real.exp (-Real.sqrt k * σ * (u - 2)) *
        ‖((1 + ζ / ((Real.sqrt k : ℂ) * (u : ℂ))) ^ k)⁻¹‖
      ≤ (Real.exp (π * |(a - 1).im|) * (‖ζ‖ / σ) ^ m * ((y ^ m)⁻¹ + y ^ m)) *
          (Real.exp (-Real.sqrt k * σ * (u - 2)) * Real.exp (-Real.sqrt k * σ / y)) := by
        rw [mul_assoc]; exact mul_le_mul (norm_saddle_cpow_factor_le a hz hk hv)
          (mul_le_mul_of_nonneg_left h1w_inv (by positivity)) (by positivity) (by positivity)
    _ = _ := by rw [hexp_comb]; ring

private theorem saddle_poly_exp_le_of_le_two {σ : ℝ} (hσ : 0 < σ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k)
    {y : ℝ} (hy : 0 < y) (hy2 : y ≤ 2) :
    ((y ^ m)⁻¹ + y ^ m) * Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y)) ≤
      2 * max ((m ! : ℝ) / (σ / 8) ^ m) (2 ^ m) := by
  have hsk1 : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hk)
  rcases le_or_gt y (1 / 2) with hy_half | hy_half
  · have hym : (y ^ m)⁻¹ + y ^ m ≤ 2 * (y ^ m)⁻¹ := by
      have h1 : y ^ m ≤ 1 := pow_le_one₀ hy.le (by linarith)
      linarith [(one_le_inv₀ (pow_pos hy m)).mpr h1]
    have hy_sq : 1 / 4 ≤ (y - 1) ^ 2 := by nlinarith
    have hexp_y : Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y)) ≤
        Real.exp (-((σ / 8) / y)) := Real.exp_le_exp.mpr <| by
      rw [neg_mul, neg_le_neg_iff, mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ hy.le
      calc σ / 8 = (1 * σ / 2) * (1 / 4) := by ring
        _ ≤ (Real.sqrt k * σ / 2) * (y - 1) ^ 2 := by gcongr
    have hinv_le : (y ^ m)⁻¹ * Real.exp (-((σ / 8) / y)) ≤ (m ! : ℝ) / (σ / 8) ^ m := by
      simpa [inv_pow, div_eq_mul_inv, neg_mul] using
        TauCeti.pow_mul_exp_neg_mul_le (a := σ / 8) (t := y⁻¹) (by positivity) (by positivity) m
    calc ((y ^ m)⁻¹ + y ^ m) * Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y))
        ≤ (2 * (y ^ m)⁻¹) * Real.exp (-((σ / 8) / y)) :=
          mul_le_mul hym hexp_y (by positivity) (by positivity)
      _ ≤ 2 * ((m ! : ℝ) / (σ / 8) ^ m) := by linarith
      _ ≤ 2 * max ((m ! : ℝ) / (σ / 8) ^ m) (2 ^ m) := by gcongr; exact le_max_left _ _
  · have hym : (y ^ m)⁻¹ + y ^ m ≤ 2 * 2 ^ m := by
      have h1 : (y ^ m)⁻¹ ≤ 2 ^ m := by
        rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity)
          ((inv_le_comm₀ hy two_pos).mpr (by linarith)) m
      linarith [pow_le_pow_left₀ hy.le hy2 m]
    have hexp1 : Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y)) ≤ 1 :=
      Real.exp_le_one_iff.mpr <| by
        rw [neg_mul]
        exact neg_nonpos.mpr (mul_nonneg (by positivity) (div_nonneg (sq_nonneg _) hy.le))
    calc ((y ^ m)⁻¹ + y ^ m) * Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y))
        ≤ (2 * 2 ^ m) * 1 := mul_le_mul hym hexp1 (by positivity) (by positivity)
      _ ≤ 2 * max ((m ! : ℝ) / (σ / 8) ^ m) (2 ^ m) := by
          rw [mul_one]; gcongr; exact le_max_right _ _

private theorem saddle_exp_le_gaussian_of_le_two {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k)
    (hq₄ : max 1 (4 * σ) ≤ (k : ℝ) ^ (1 / 4 : ℝ)) {v : ℝ}
    (hv : -(k : ℝ) ^ (1 / 4 : ℝ) < v) (hy2 : saddleY σ k v ≤ 2) :
    Real.exp (-(Real.sqrt k * σ / 2) * ((saddleY σ k v - 1) ^ 2 / saddleY σ k v)) ≤
      Real.exp (σ / 16) * Real.exp (-(σ / 16) * v ^ 2) := by
  set y : ℝ := saddleY σ k v
  set q₄ : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsk1 : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hk)
  have hq1 : 1 ≤ q₄ := (le_max_left 1 (4 * σ)).trans hq₄
  have hqσ : 4 * σ ≤ q₄ := (le_max_right 1 (4 * σ)).trans hq₄
  have hq_sq : q₄ ^ 2 = Real.sqrt k := rpow_quarter_sq k
  have hu : 0 < saddleU k v := saddle_u_pos hk hv
  have hy : 0 < y := by dsimp only [y, saddleY]; positivity
  rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
  rcases le_or_gt |v| 1 with hv1 | hv1
  · have hv_sq : v ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg v]
    have hnn : 0 ≤ (Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y) :=
      mul_nonneg (by positivity) (div_nonneg (sq_nonneg _) hy.le)
    have : -(σ / 16) * v ^ 2 ≥ -(σ / 16) := by nlinarith
    linarith
  · have hy_sub : y - 1 = q₄⁻¹ * (v + σ / q₄) := by
      dsimp only [y, saddleY, saddleU]; rw [rpow_neg_quarter hk_pos.le, ← hq_sq]
      field_simp [(zero_lt_one.trans_le hq1).ne']; dsimp only [q₄]; ring
    have hv_shift : v ^ 2 / 4 ≤ (v + σ / q₄) ^ 2 := by
      have hδq : σ / q₄ ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      rcases le_or_gt 0 v with hv0 | hv0
      · rw [abs_of_nonneg hv0] at hv1; nlinarith [div_pos hσ (zero_lt_one.trans_le hq1)]
      · rw [abs_of_neg hv0] at hv1; nlinarith [div_pos hσ (zero_lt_one.trans_le hq1)]
    have hquad : (σ / 16) * v ^ 2 ≤ (Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y) := by
      rw [hy_sub, mul_pow, inv_pow, hq_sq]
      have hdiv2 : ((Real.sqrt k)⁻¹ * (v + σ / q₄) ^ 2) / 2 ≤
          ((Real.sqrt k)⁻¹ * (v + σ / q₄) ^ 2) / y :=
        div_le_div_of_nonneg_left (by positivity) hy hy2
      calc (σ / 16) * v ^ 2
          = (Real.sqrt k * σ / 2) * (((Real.sqrt k)⁻¹ * (v ^ 2 / 4)) / 2) := by
            field_simp [(zero_lt_one.trans_le hsk1).ne']; ring
        _ ≤ (Real.sqrt k * σ / 2) * (((Real.sqrt k)⁻¹ * (v + σ / q₄) ^ 2) / 2) := by gcongr
        _ ≤ (Real.sqrt k * σ / 2) * (((Real.sqrt k)⁻¹ * (v + σ / q₄) ^ 2) / y) := by gcongr
    linarith

private theorem saddle_majorant_le_two {σ : ℝ} (hσ : 0 < σ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hq₄ : max 1 (4 * σ) ≤ (k : ℝ) ^ (1 / 4 : ℝ)) {v : ℝ}
    (hv : -(k : ℝ) ^ (1 / 4 : ℝ) < v) (hy2 : saddleY σ k v ≤ 2) :
    ((saddleY σ k v ^ m)⁻¹ + saddleY σ k v ^ m) *
        Real.exp (-Real.sqrt k * σ * ((saddleY σ k v - 1) ^ 2 / saddleY σ k v)) ≤
      (2 * max ((m ! : ℝ) / (σ / 8) ^ m) (2 ^ m) * Real.exp (σ / 16)) *
        Real.exp (-(σ / 16) * v ^ 2) := by
  set y : ℝ := saddleY σ k v
  have hu : 0 < saddleU k v := saddle_u_pos hk hv
  have hy : 0 < y := by dsimp only [y, saddleY]; positivity
  have hsplit : Real.exp (-Real.sqrt k * σ * ((y - 1) ^ 2 / y)) =
      Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y)) *
        Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  calc (((y ^ m)⁻¹ + y ^ m) * Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y))) *
        Real.exp (-(Real.sqrt k * σ / 2) * ((y - 1) ^ 2 / y))
      ≤ (2 * max ((m ! : ℝ) / (σ / 8) ^ m) (2 ^ m)) *
          (Real.exp (σ / 16) * Real.exp (-(σ / 16) * v ^ 2)) :=
        mul_le_mul (saddle_poly_exp_le_of_le_two hσ m hk hy hy2)
          (saddle_exp_le_gaussian_of_le_two hσ hk hq₄ hv hy2) (by positivity) (by positivity)
    _ = _ := by ring

private theorem saddle_majorant_gt_two {σ : ℝ} (hσ : 0 < σ) (m : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hq₄ : max 1 (4 * σ) ≤ (k : ℝ) ^ (1 / 4 : ℝ)) {v : ℝ} (hy2 : 2 < saddleY σ k v) :
    ((saddleY σ k v ^ m)⁻¹ + saddleY σ k v ^ m) *
        Real.exp (-Real.sqrt k * σ * ((saddleY σ k v - 1) ^ 2 / saddleY σ k v)) ≤
      (2 * ((m ! : ℝ) / (σ / 8) ^ m)) *
        (Ioi (0 : ℝ)).indicator (fun x => Real.exp (-(σ / 8) * x)) v := by
  set y : ℝ := saddleY σ k v
  set q₄ : ℝ := (k : ℝ) ^ (1 / 4 : ℝ)
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsk1 : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hk)
  have hq1 : 1 ≤ q₄ := (le_max_left 1 (4 * σ)).trans hq₄
  have hqσ : 4 * σ ≤ q₄ := (le_max_right 1 (4 * σ)).trans hq₄
  have hq_sq : q₄ ^ 2 = Real.sqrt k := rpow_quarter_sq k
  have hy : 0 < y := by linarith
  have hδ_le : σ / Real.sqrt k ≤ 1 / 4 := by
    rw [← hq_sq, div_le_div_iff₀ (by positivity) (by positivity)]
    calc σ * 4 ≤ q₄ * 1 := by linarith
      _ ≤ q₄ * q₄ := mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ = 1 * q₄ ^ 2 := by ring
  have hv_pos : 0 < v := pos_of_mul_pos_right
    (by dsimp only [y, saddleY, saddleU] at hy2; linarith)
    (Real.rpow_nonneg hk_pos.le (-1 / 4 : ℝ))
  rw [indicator_of_mem (mem_Ioi.mpr hv_pos)]
  have hym : (y ^ m)⁻¹ + y ^ m ≤ 2 * y ^ m := by
    have h1 : 1 ≤ y ^ m := one_le_pow₀ (by linarith)
    linarith [inv_le_one_of_one_le₀ h1]
  have hquad_y : y / 4 ≤ (y - 1) ^ 2 / y := by
    rw [div_le_div_iff₀ (by positivity) hy]
    linarith [mul_nonneg (a := 3 * y - 2) (b := y - 2) (by linarith) (by linarith)]
  have hym_exp : y ^ m * Real.exp (-(σ / 8) * y) ≤ (m ! : ℝ) / (σ / 8) ^ m :=
    TauCeti.pow_mul_exp_neg_mul_le (by positivity) hy.le m
  have hvy : v ≤ Real.sqrt k * y := by
    have hq0 : q₄ ≠ 0 := (zero_lt_one.trans_le hq1).ne'
    have h1 : q₄ * v ≤ Real.sqrt k * y := by
      dsimp only [y, saddleY, saddleU]; rw [← hq_sq, rpow_neg_quarter hk_pos.le]
      rw [show q₄ ^ 2 * (1 + q₄⁻¹ * v + σ / q₄ ^ 2) = q₄ ^ 2 + q₄ * v + σ by field_simp [hq0]]
      linarith [sq_nonneg q₄]
    linarith [le_mul_of_one_le_left hv_pos.le hq1]
  have hexp_split : Real.exp (-Real.sqrt k * σ * ((y - 1) ^ 2 / y)) ≤
      Real.exp (-(σ / 8) * y) * Real.exp (-(σ / 8) * v) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_left hquad_y (a := Real.sqrt k * σ) (by positivity)
    have h2 :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hy.le hsk1) (a := σ / 8) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hvy (a := σ / 8) (by positivity)
    linarith
  calc ((y ^ m)⁻¹ + y ^ m) * Real.exp (-Real.sqrt k * σ * ((y - 1) ^ 2 / y))
      ≤ (2 * y ^ m) * (Real.exp (-(σ / 8) * y) * Real.exp (-(σ / 8) * v)) :=
        mul_le_mul hym hexp_split (by positivity) (by positivity)
    _ = 2 * (y ^ m * Real.exp (-(σ / 8) * y)) * Real.exp (-(σ / 8) * v) := by ring
    _ ≤ (2 * ((m ! : ℝ) / (σ / 8) ^ m)) * Real.exp (-(σ / 8) * v) := by gcongr

private theorem tendsto_integral_kummerLaplaceSaddleIntegrand (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun k : ℕ => ∫ v : ℝ, kummerLaplaceSaddleIntegrand a z k v) atTop
      (𝓝 ((Real.sqrt π : ℂ) * cexp (z / 2) * ((z ^ (1 / 2 : ℂ))⁻¹) ^ (1 / 2 : ℂ))) := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  set σ : ℝ := ζ.re
  have hσ : 0 < σ := by simpa [σ, ζ, sqrt, one_div] using (sqrt_re_pos_iff z).mpr hz
  set m : ℕ := ⌈|(a - 1).re|⌉₊
  set C₀ : ℝ := Real.exp (π * |(a - 1).im|) * (‖ζ‖ / σ) ^ m * Real.exp (σ ^ 2)
  set C₁ : ℝ := 2 * max ((m ! : ℝ) / (σ / 8) ^ m) (2 ^ m) * Real.exp (σ / 16)
  set C₂ : ℝ := 2 * ((m ! : ℝ) / (σ / 8) ^ m)
  set B : ℝ → ℝ := fun v => C₀ * (C₁ * Real.exp (-(σ / 16) * v ^ 2) +
    C₂ * (Ioi (0 : ℝ)).indicator (fun x => Real.exp (-(σ / 8) * x)) v)
  have hB_int : Integrable B volume :=
    (((integrable_exp_neg_mul_sq (by positivity)).const_mul C₁).add
      (((integrableOn_exp_mul_Ioi (by linarith) 0).integrable_indicator
        measurableSet_Ioi).const_mul C₂)).const_mul C₀
  have ht_q4 :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hgauss : (∫ v : ℝ, cexp (-ζ * (v : ℂ) ^ 2 + z / 2)) =
      (Real.sqrt π : ℂ) * cexp (z / 2) * (ζ⁻¹) ^ (1 / 2 : ℂ) := by
    have heq : (fun v : ℝ => cexp (-ζ * (v : ℂ) ^ 2 + z / 2)) =
        fun v : ℝ => cexp (z / 2) * cexp (-ζ * (v : ℂ) ^ 2) := by
      ext v; rw [← Complex.exp_add]; congr 1; ring
    rw [heq, integral_const_mul, integral_gaussian_complex hσ,
      show (π : ℂ) / ζ = (π : ℂ) * ζ⁻¹ from div_eq_mul_inv _ _,
      TauCeti.ofReal_mul_cpow Real.pi_pos.le, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; ring
  rw [← hgauss]
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hB_int
    (ae_of_all _ (tendsto_kummerLaplaceSaddleIntegrand a z))
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact aestronglyMeasurable_kummerLaplaceSaddleIntegrand a hz hk
  · filter_upwards [eventually_ge_atTop 1, ht_q4.eventually_ge_atTop (max 1 (4 * σ))] with k hk hq
    refine ae_of_all _ fun v => ?_
    unfold kummerLaplaceSaddleIntegrand
    by_cases hv : v ∈ Ioi (-(k : ℝ) ^ (1 / 4 : ℝ))
    · rw [indicator_of_mem hv]
      refine (norm_kummerLaplaceSaddleCore_exp_bound a hz hk hv).trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rcases le_or_gt (1 + (k : ℝ) ^ (-1 / 4 : ℝ) * v + σ / Real.sqrt k) 2 with hy2 | hy2
      · exact le_add_of_le_of_nonneg (saddle_majorant_le_two hσ m hk hq hv hy2)
          (mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) v))
      · exact le_add_of_nonneg_of_le (by positivity) (saddle_majorant_gt_two hσ m hk hq hy2)
    · rw [indicator_of_notMem hv, norm_zero]
      exact mul_nonneg (by positivity) (add_nonneg (by positivity)
        (mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) v)))

/-- **Saddle-point asymptotic of `kummerLaplace k (a - 1 - k) z` as `k → ∞`.**
For any `a : ℂ` and `z ∈ slitPlane`, the rotated Kummer-Laplace integral satisfies
`K(k, a - 1 - k; z) ~ √π e^{z/2} z^{-a/2 - 1/4} k^{a/2 - 1/4} e^{-2 √(kz)}` as `k → ∞`. -/
theorem kummerLaplace_isEquivalent (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (fun k : ℕ => kummerLaplace k (a - 1 - k) z) ~[atTop]
      fun k : ℕ => (Real.sqrt π : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) *
        (k : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ)
  have hζ0 : ζ ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))
  have hdct := tendsto_integral_kummerLaplaceSaddleIntegrand a hz
  have hζ_comb : (ζ⁻¹) ^ a * ((Real.sqrt π : ℂ) * cexp (z / 2) * (ζ⁻¹) ^ (1 / 2 : ℂ)) =
      (Real.sqrt π : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) := by
    have hmul : (ζ⁻¹) ^ a * (ζ⁻¹) ^ (1 / 2 : ℂ) = z ^ (-a / 2 - 1 / 4) := by
      rw [← cpow_add _ _ (inv_ne_zero hζ0), inv_cpow_half_cpow]
      congr 1; ring
    linear_combination (Real.sqrt π : ℂ) * cexp (z / 2) * hmul
  refine isEquivalent_of_tendsto_one <|
    ((hdct.const_mul ((ζ⁻¹) ^ a)).div_const
      ((Real.sqrt π : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4))).congr' ?_ |>.trans ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [Pi.div_apply]
    rw [kummerLaplace_eq_saddle_integral a hz hk]
    set C : ℂ := (k : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ))
    have hC : C ≠ 0 :=
      mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (by omega))))
        (exp_ne_zero _)
    have hnum : (k : ℂ) ^ (a / 2 - 1 / 4) * (z ^ (1 / 2 : ℂ))⁻¹ ^ a *
        cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) *
        (∫ v : ℝ, kummerLaplaceSaddleIntegrand a z k v) =
        ((ζ⁻¹) ^ a * ∫ v : ℝ, kummerLaplaceSaddleIntegrand a z k v) * C := by
      dsimp only [ζ, C]; ring
    have hden : (Real.sqrt π : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4) *
        (k : ℂ) ^ (a / 2 - 1 / 4) * cexp (-2 * ((k : ℂ) * z) ^ (1 / 2 : ℂ)) =
        ((Real.sqrt π : ℂ) * cexp (z / 2) * z ^ (-a / 2 - 1 / 4)) * C := by
      dsimp only [C]; ring
    rw [hnum, hden, mul_div_mul_right _ _ hC]
  · rw [hζ_comb, div_self]
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))
      (exp_ne_zero _)) (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz)))

/-- For any `a : ℂ` and `z ∈ slitPlane`, `kummerLaplace k (a - 1 - k) z` is eventually nonzero
as `k → ∞`. -/
theorem eventually_kummerLaplace_ne_zero (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    ∀ᶠ k : ℕ in atTop, kummerLaplace k (a - 1 - k) z ≠ 0 := by
  filter_upwards [(kummerLaplace_isEquivalent a hz).isBigO_symm.eq_zero_imp,
    eventually_ge_atTop 1] with k himp hk hzero
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)) (exp_ne_zero _))
    (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))))
    (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (by omega)))))
    (exp_ne_zero _) (himp hzero)

/-! ### Partial numerators and recurrence solution of Legendre's continued fraction -/

/-- The `n`-th partial numerator of Legendre's continued fraction for `z^{-a} e^z Γ(a, z)`:
`a₁ = z⁻¹`, `a_{2k} = (k - a) * z⁻¹` (`k ≥ 1`), and `a_{2k+1} = k * z⁻¹` (`k ≥ 1`), paired with
partial denominators `b_n = 1` and head `b₀ = 0`. -/
def upperGammaContFracPartNum (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 1 then z⁻¹
  else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹
  else ((n / 2 : ℕ) : ℂ) * z⁻¹

/-- Defining formula for `Complex.upperGammaContFracPartNum`. -/
theorem upperGammaContFracPartNum_def (a z : ℂ) (n : ℕ) :
    upperGammaContFracPartNum a z n =
      if n = 1 then z⁻¹
      else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹
      else ((n / 2 : ℕ) : ℂ) * z⁻¹ := (rfl)

/-- Zeroth index evaluation `upperGammaContFracPartNum a z 0 = -a * z⁻¹`. -/
@[simp]
theorem upperGammaContFracPartNum_zero (a z : ℂ) :
    upperGammaContFracPartNum a z 0 = -a * z⁻¹ := by
  simp [upperGammaContFracPartNum]

/-- First partial numerator `a₁ = z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperGammaContFracPartNum_one (a z : ℂ) :
    upperGammaContFracPartNum a z 1 = z⁻¹ := by
  simp [upperGammaContFracPartNum]

/-- Even partial numerator `a_{2k+2} = (k + 1 - a) * z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperGammaContFracPartNum_two_mul_add_two (a z : ℂ) (k : ℕ) :
    upperGammaContFracPartNum a z (2 * k + 2) = ((k : ℂ) + 1 - a) * z⁻¹ := by
  have h1 : 2 * k + 2 ≠ 1 := by omega
  have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
  simp only [upperGammaContFracPartNum, h1, ↓reduceIte, hev, hdiv, Nat.cast_add, Nat.cast_one]

/-- Odd partial numerator `a_{2k+3} = (k + 1) * z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperGammaContFracPartNum_two_mul_add_three (a z : ℂ) (k : ℕ) :
    upperGammaContFracPartNum a z (2 * k + 3) = ((k : ℂ) + 1) * z⁻¹ := by
  have h1 : 2 * k + 3 ≠ 1 := by omega
  have hodd : ¬Even (2 * k + 3) := by simp [parity_simps]
  have hdiv : (2 * k + 3) / 2 = k + 1 := by omega
  simp only [upperGammaContFracPartNum, h1, ↓reduceIte, hodd, hdiv, Nat.cast_add, Nat.cast_one]

/-- Exact nonvanishing characterization of `upperGammaContFracPartNum a z n`: it is nonzero
if and only if `z ≠ 0` and, when `n` is even, `a ≠ (n / 2 : ℕ)`. -/
theorem upperGammaContFracPartNum_ne_zero_iff {a z : ℂ} {n : ℕ} :
    upperGammaContFracPartNum a z n ≠ 0 ↔ z ≠ 0 ∧ (Even n → a ≠ (n / 2 : ℕ)) := by
  rcases n with _ | _ | n
  · simp [and_comm]
  · simp
  · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
      have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
      rw [upperGammaContFracPartNum_two_mul_add_two, hdiv]
      simp [hev, sub_eq_zero, eq_comm (a := a), and_comm]
    · have hodd : ¬Even (2 * k + 3) := by simp [parity_simps]
      have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [show 2 * k + 1 + 2 = 2 * k + 3 by ring, upperGammaContFracPartNum_two_mul_add_three]
      simp [hodd, hk1]

/-- Explicit Kummer-Laplace solution sequence of the three-term recurrence
`f (n + 2) = f (n + 1) + upperGammaContFracPartNum a z (n + 1) * f n` on `Complex.slitPlane`
associated with Legendre's continued fraction for `z^{-a} e^z Γ(a, z)`, normalized by `f 0 = 1`:
* `f 0 = 1`,
* `f (2k + 1) = -(1 - a)_k * z⁻¹ ^ k * kummerLaplace k (a - 1 - k) z`,
* `f (2k + 2) = (1 - a)_{k+1} * z⁻¹ ^ (k + 1) * kummerLaplace k (a - 2 - k) z`. -/
def upperGammaContFracSolution (a z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
      if Even n then
        -(ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
          kummerLaplace (n / 2) (a - 1 - (n / 2 : ℕ)) z
      else
        (ascPochhammer ℂ (n / 2 + 1)).eval (1 - a) * z⁻¹ ^ (n / 2 + 1) *
          kummerLaplace (n / 2) (a - 2 - (n / 2 : ℕ)) z

/-- Normalization `f 0 = 1` of `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_zero (a z : ℂ) :
    upperGammaContFracSolution a z 0 = 1 := by rfl

/-- Successor formula for `Complex.upperGammaContFracSolution`. -/
theorem upperGammaContFracSolution_succ (a z : ℂ) (n : ℕ) :
    upperGammaContFracSolution a z (n + 1) =
      if Even n then
        -(ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
          kummerLaplace (n / 2) (a - 1 - (n / 2 : ℕ)) z
      else
        (ascPochhammer ℂ (n / 2 + 1)).eval (1 - a) * z⁻¹ ^ (n / 2 + 1) *
          kummerLaplace (n / 2) (a - 2 - (n / 2 : ℕ)) z := (rfl)

/-- Initial value `f 1 = -kummerLaplace 0 (a - 1) z` of `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_one (a z : ℂ) :
    upperGammaContFracSolution a z 1 = -kummerLaplace 0 (a - 1) z := by
  simp [upperGammaContFracSolution]

/-- Odd-index formula for `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_two_mul_add_one (a z : ℂ) (k : ℕ) :
    upperGammaContFracSolution a z (2 * k + 1) =
      -(ascPochhammer ℂ k).eval (1 - a) * z⁻¹ ^ k * kummerLaplace k (a - 1 - k) z := by
  have hev : Even (2 * k) := ⟨k, by ring⟩
  have hdiv : (2 * k) / 2 = k := by omega
  simp only [upperGammaContFracSolution, hev, ↓reduceIte, hdiv]

/-- Even-index formula for `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_two_mul_add_two (a z : ℂ) (k : ℕ) :
    upperGammaContFracSolution a z (2 * k + 2) =
      (ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
        kummerLaplace k (a - 2 - k) z := by
  have hodd : ¬Even (2 * k + 1) := by simp [parity_simps]
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp only [upperGammaContFracSolution, hodd, ↓reduceIte, hdiv]

/-- **Three-term recurrence for Legendre's incomplete Gamma continued fraction.**
On `slitPlane`, `f := upperGammaContFracSolution a z` satisfies
`f (n + 2) = f (n + 1) + upperGammaContFracPartNum a z (n + 1) * f n` for every `n : ℕ`. -/
theorem upperGammaContFracSolution_add_two (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    upperGammaContFracSolution a z (n + 2) =
      upperGammaContFracSolution a z (n + 1) +
        upperGammaContFracPartNum a z (n + 1) * upperGammaContFracSolution a z n := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rcases eq_or_ne n 0 with rfl | hn0
  · have hibp := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_zero (a - 1) hz)
    simp only [← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_add, mul_one,
      show a - 1 - 1 = a - 2 by ring] at hibp
    have h2 : upperGammaContFracSolution a z 2 = (1 - a) * z⁻¹ * kummerLaplace 0 (a - 2) z := by
      simpa [ascPochhammer_one] using upperGammaContFracSolution_two_mul_add_two a z 0
    rw [h2, upperGammaContFracSolution_one, upperGammaContFracPartNum_one,
      upperGammaContFracSolution_zero, mul_one]
    linear_combination hibp
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
      ⟨(n - 1) / 2, by omega⟩
    · have h3 : upperGammaContFracSolution a z (2 * k + 1 + 2) =
          -(ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
            kummerLaplace (k + 1) (a - 2 - k) z := by
        simpa [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring,
          show a - 1 - ((k : ℂ) + 1) = a - 2 - k by ring] using
          upperGammaContFracSolution_two_mul_add_one a z (k + 1)
      have hdiff := kummerLaplace_sub_kummerLaplace_sub_one k (a - 1 - k) hz
      rw [show a - 1 - (k : ℂ) - 1 = a - 2 - k by ring] at hdiff
      rw [h3, show 2 * k + 1 + 1 = 2 * k + 2 from rfl,
        upperGammaContFracSolution_two_mul_add_two, upperGammaContFracPartNum_two_mul_add_two,
        upperGammaContFracSolution_two_mul_add_one, ascPochhammer_succ_eval, pow_succ]
      linear_combination (ascPochhammer ℂ k).eval (1 - a) * (1 - a + (k : ℂ)) *
        (z⁻¹ ^ k * z⁻¹) * hdiff
    · have h4 : upperGammaContFracSolution a z (2 * k + 2 + 2) =
          (ascPochhammer ℂ (k + 2)).eval (1 - a) * z⁻¹ ^ (k + 2) *
            kummerLaplace (k + 1) (a - 3 - k) z := by
        simpa [show 2 * (k + 1) + 2 = 2 * k + 2 + 2 by ring,
          show a - 2 - ((k : ℂ) + 1) = a - 3 - k by ring] using
          upperGammaContFracSolution_two_mul_add_two a z (k + 1)
      have h3 : upperGammaContFracSolution a z (2 * k + 2 + 1) =
          -(ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
            kummerLaplace (k + 1) (a - 2 - k) z := by
        simpa [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring,
          show a - 1 - ((k : ℂ) + 1) = a - 2 - k by ring] using
          upperGammaContFracSolution_two_mul_add_one a z (k + 1)
      have hibp := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_add_one k (a - 2 - k) hz)
      simp only [← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_add,
        show a - 2 - (k : ℂ) - 1 = a - 3 - k by ring] at hibp
      rw [h4, h3, show 2 * k + 2 + 1 = 2 * k + 3 from rfl,
        upperGammaContFracPartNum_two_mul_add_three, upperGammaContFracSolution_two_mul_add_two,
        show k + 2 = (k + 1) + 1 from rfl, ascPochhammer_succ_eval, Nat.cast_add, Nat.cast_one,
        pow_succ _ (k + 1)]
      linear_combination (ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) * hibp

/-- When `z ∈ slitPlane` and `a` is not a positive integer, the Kummer-Laplace recurrence
solution `upperGammaContFracSolution a z n` is eventually nonzero as `n → ∞`. -/
theorem eventually_upperGammaContFracSolution_ne_zero {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1)
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∀ᶠ n : ℕ in atTop, upperGammaContFracSolution a z n ≠ 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hp : ∀ k : ℕ, (ascPochhammer ℂ k).eval (1 - a) ≠ 0 := fun k => by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨m, _, hm⟩
    exact ha m (by linear_combination -hm)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_kummerLaplace_ne_zero a hz)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_kummerLaplace_ne_zero (a - 1) hz)
  refine eventually_atTop.mpr ⟨2 * max N₁ N₂ + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
    ⟨(n - 1) / 2, by omega⟩
  · rw [upperGammaContFracSolution_two_mul_add_one]
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (hp k)) (pow_ne_zero k (inv_ne_zero hz0)))
      (hN₁ k ?_)
    have : max N₁ N₂ ≤ k := by omega
    exact (le_max_left N₁ N₂).trans this
  · rw [upperGammaContFracSolution_two_mul_add_two]
    refine mul_ne_zero (mul_ne_zero (hp (k + 1)) (pow_ne_zero (k + 1) (inv_ne_zero hz0))) ?_
    have hk2 : N₂ ≤ k := (le_max_right N₁ N₂).trans (by omega)
    simpa [show a - 1 - 1 - (k : ℂ) = a - 2 - k by ring] using hN₂ k hk2

end Complex
