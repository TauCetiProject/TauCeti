/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf
public import TauCeti.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Inequalities for the error functions

This file proves the inequalities of DLMF §7.8 for Mills' ratio
`M(x) = e^{x²} ∫ₓ^∞ e^{−t²} dt = (√π/2) e^{x²} erfc x`, for the integral `∫₀ˣ e^{at²} dt` and for
`erf`. Mills' ratio is written out in every public statement, so that the bounds apply directly
to `erfc`.

## Main results

* `TauCeti.Real.millsRatio_eq_integral`: `(√π/2) e^{x²} erfc x = e^{x²} ∫ₓ^∞ e^{−t²} dt`
  (DLMF 7.8.1).
* `TauCeti.Real.millsRatio_bounds`: `1/(x + √(x² + 2)) < M(x) ≤ 1/(x + √(x² + 4/π))` for `x ≥ 0`
  (DLMF 7.8.2).
* `TauCeti.Real.millsRatio_bounds_affine`: `√π/(2√π x + 2) ≤ M(x) < 1/(x + 1)` for `x ≥ 0`
  (DLMF 7.8.3).
* `TauCeti.Real.millsRatio_lt_two_div`: `M(x) < 2/(3x + √(x² + 4))` for `x > −√2/2`
  (DLMF 7.8.4).
* `TauCeti.Real.mul_millsRatio_bounds`: the rational bounds for `x M(x)` (DLMF 7.8.5).
* `TauCeti.Real.integral_exp_mul_sq_lt`: `∫₀ˣ e^{at²} dt < (2e^{ax²} + ax² − 2)/(3ax)` for
  `a, x > 0` (DLMF 7.8.6).
* `TauCeti.Real.erf_lt_sqrt_one_sub_exp`: `erf x < √(1 − e^{−4x²/π})` for `x > 0` (DLMF 7.8.8).

## Implementation notes

The bounds on Mills' ratio come from a comparison principle. If a candidate `g` satisfies
`g′ − 2yg + 1 < 0` beyond `x` and `g → 0`, then `M(x) < g(x)`, and symmetrically for lower
bounds: the function `e^{−y²} g(y) − ∫_y^∞ e^{−t²} dt` is monotone and tends to `0`. Bound 7.8.8
compares `erf` with `c y e^{(1 − k) y²}`, `k = 4/π`, using convexity of `exp`. Where the
derivative of the comparison function changes sign once (the upper bound of 7.8.2, the lower
bound of 7.8.3, and 7.8.8), the sign-change lemmas
`TauCeti.nonneg_of_tendsto_atTop_of_deriv_nonpos_stable` and
`TauCeti.pos_of_tendsto_atTop_of_deriv_nonpos_stable` conclude.

DLMF 7.8.7, the bounds for Dawson's integral, is not in this file.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean`.
-/

public section

noncomputable section

open Filter Set MeasureTheory

open scoped Real Topology

namespace TauCeti.Real

/-- Mills' ratio `M(x) = (√π/2) e^{x²} erfc x` (DLMF 7.8.1), used only inside this file; the
public statements write it out. -/
private def millsRatio (x : ℝ) : ℝ :=
  Real.sqrt π / 2 * Real.exp (x ^ 2) * TauCeti.Real.erfc x

/-- **DLMF 7.8.1.** Mills' ratio as a tail integral:
`(√π/2) e^{x²} erfc x = e^{x²} ∫ₓ^∞ e^{−t²} dt`. -/
theorem millsRatio_eq_integral (x : ℝ) :
    Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x =
      Real.exp (x ^ 2) * ∫ t : ℝ in Ioi x, Real.exp (-t ^ 2) := by
  have hd (t : ℝ) : HasDerivAt (fun t => -(Real.sqrt π / 2 * TauCeti.Real.erfc t))
      (Real.exp (-t ^ 2)) t := by
    have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    convert ((TauCeti.Real.hasDerivAt_erfc t).const_mul (Real.sqrt π / 2)).neg using 1
    field_simp
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun t => -(Real.sqrt π / 2 * TauCeti.Real.erfc t))
    (m := 0) (a := x) (hd x).continuousAt.continuousWithinAt (fun t _ => hd t)
    (by simpa using (integrable_exp_neg_mul_sq one_pos).integrableOn)
    (by simpa using (TauCeti.Real.tendsto_erfc_atTop.const_mul (Real.sqrt π / 2)).neg)
  rw [hi]
  ring

/-- The defining formula of Mills' ratio. -/
private theorem millsRatio_def (x : ℝ) :
    millsRatio x = Real.sqrt π / 2 * Real.exp (x ^ 2) * TauCeti.Real.erfc x := (rfl)

/-- The comparison function of a candidate `g`, scaled by `e^{x²}`, is `g(x) − M(x)`. -/
private theorem exp_sq_mul_comparison (g : ℝ → ℝ) (x : ℝ) :
    Real.exp (x ^ 2) * (Real.exp (-x ^ 2) * g x - Real.sqrt π / 2 * TauCeti.Real.erfc x) =
      g x - millsRatio x := by
  have h1 : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by rw [← Real.exp_add]; simp
  rw [millsRatio_def]
  linear_combination (g x) * h1

/-- The comparison function `E = e^{-y²} g − ∫_y^∞ e^{-t²}` of a candidate bound `g`. -/
private theorem hasDerivAt_comparison {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y) :
    HasDerivAt (fun y => Real.exp (-y ^ 2) * g y - Real.sqrt π / 2 * TauCeti.Real.erfc y)
      (Real.exp (-y ^ 2) * (g' - 2 * y * g y + 1)) y := by
  have he : HasDerivAt (fun y => Real.exp (-y ^ 2)) (Real.exp (-y ^ 2) * (-(2 * y))) y := by
    have := (hasDerivAt_pow 2 y).neg.exp
    exact this.congr_deriv (by norm_num)
  have := (he.mul hg).sub ((TauCeti.Real.hasDerivAt_erfc y).const_mul (Real.sqrt π / 2))
  refine this.congr_deriv ?_
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- The comparison function of a candidate `g → 0` tends to `0`. -/
private theorem tendsto_comparison {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun y => Real.exp (-y ^ 2) * g y - Real.sqrt π / 2 *
        TauCeti.Real.erfc y) atTop (𝓝 0) := by
  have he : Tendsto (fun y : ℝ => Real.exp (-y ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have := (he.mul hg).sub (TauCeti.Real.tendsto_erfc_atTop.const_mul (Real.sqrt π / 2))
  simpa using this

/-- Upper bound principle: if `g' − 2yg + 1 < 0` beyond `x` and `g → 0`, then `M(x) < g(x)`. -/
private theorem millsRatio_lt {g g' : ℝ → ℝ} {x : ℝ}
    (hg : ∀ y, x ≤ y → HasDerivAt g (g' y) y)
    (hlim : Tendsto g atTop (𝓝 0)) (hP : ∀ y, x < y → g' y - 2 * y * g y + 1 < 0) :
    millsRatio x < g x := by
  have h := pos_of_tendsto_atTop_of_deriv_neg (fun y hy => hasDerivAt_comparison (hg y hy))
      (tendsto_comparison hlim)
    (fun y hy => mul_neg_of_pos_of_neg (Real.exp_pos _) (hP y hy))
  rw [← sub_pos, ← exp_sq_mul_comparison]
  exact mul_pos (Real.exp_pos _) h

/-- Lower bound principle: if `g′ − 2yg + 1 > 0` beyond `x` and `g → 0`, then
`g(x) < M(x)`. -/
private theorem lt_millsRatio {g g' : ℝ → ℝ} {x : ℝ}
    (hg : ∀ y, x ≤ y → HasDerivAt g (g' y) y)
    (hlim : Tendsto g atTop (𝓝 0)) (hP : ∀ y, x < y → 0 < g' y - 2 * y * g y + 1) :
    g x < millsRatio x := by
  have h := pos_of_tendsto_atTop_of_deriv_neg
      (f := fun y => -(Real.exp (-y ^ 2) * g y - Real.sqrt π / 2 * TauCeti.Real.erfc y))
    (fun y hy => (hasDerivAt_comparison (hg y hy)).neg)
        (by simpa using (tendsto_comparison hlim).neg)
    (fun y hy => neg_neg_of_pos (mul_pos (Real.exp_pos _) (hP y hy)))
  rw [← sub_neg, ← exp_sq_mul_comparison]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)

/-- `M(x) ≤ g(x)` as soon as the comparison function is nonnegative at `x`. -/
private theorem millsRatio_le_of {g : ℝ → ℝ} {x : ℝ}
    (h : 0 ≤ Real.exp (-x ^ 2) * g x - Real.sqrt π / 2 * TauCeti.Real.erfc x) :
    millsRatio x ≤ g x := by
  rw [← sub_nonneg, ← exp_sq_mul_comparison]
  exact mul_nonneg (Real.exp_pos _).le h

/-- `g(x) ≤ M(x)` as soon as the comparison function is nonpositive at `x`. -/
private theorem le_millsRatio_of {g : ℝ → ℝ} {x : ℝ}
    (h : Real.exp (-x ^ 2) * g x - Real.sqrt π / 2 * TauCeti.Real.erfc x ≤ 0) :
    g x ≤ millsRatio x := by
  rw [← sub_nonpos, ← exp_sq_mul_comparison]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h

/-- The derivative identity for the candidates `1/(y + √(y² + c))` of DLMF 7.8.2:
`g′ − 2yg + 1 = (c − 1 − y(√(y² + c) − y))/(√(y² + c)(y + √(y² + c)))`. -/
private theorem comparison_sqrt_candidate_eq {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    -1 * (1 + y / Real.sqrt (y ^ 2 + c)) / (1 * y + Real.sqrt (y ^ 2 + c)) ^ 2 -
        2 * y * (1 / (1 * y + Real.sqrt (y ^ 2 + c))) + 1 =
      (c - 1 - y * (Real.sqrt (y ^ 2 + c) - y)) /
        (Real.sqrt (y ^ 2 + c) * (y + Real.sqrt (y ^ 2 + c))) := by
  have h2 : y + Real.sqrt (y ^ 2 + c) ≠ 0 := by positivity
  have h3 : Real.sqrt (y ^ 2 + c) ^ 2 = y ^ 2 + c := Real.sq_sqrt (by positivity)
  rw [show c - 1 - y * (Real.sqrt (y ^ 2 + c) - y) =
      Real.sqrt (y ^ 2 + c) ^ 2 - y * Real.sqrt (y ^ 2 + c) - 1 by rw [h3]; ring]
  field_simp
  ring

/-- `1 * y + √(y² + c) ≠ 0` for `c > 0` and `y ≥ 0`. -/
private theorem one_mul_add_sqrt_ne_zero {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    1 * y + Real.sqrt (y ^ 2 + c) ≠ 0 := by
  have : 0 < Real.sqrt (y ^ 2 + c) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- The lower bound of DLMF 7.8.2: `1/(x + √(x² + 2)) < M(x)` for `x ≥ 0`. -/
private theorem one_div_add_sqrt_two_lt_millsRatio {x : ℝ} (hx : 0 ≤ x) :
    1 / (x + Real.sqrt (x ^ 2 + 2)) < millsRatio x := by
  have := lt_millsRatio (x := x) (g := fun y => 1 / (1 * y + Real.sqrt (y ^ 2 + 2)))
    (fun y hy => Real.hasDerivAt_div_mul_add_sqrt_sq_add 1 1 two_pos
      (one_mul_add_sqrt_ne_zero two_pos (hx.trans hy)))
    (Real.tendsto_div_mul_add_sqrt_sq_add_atTop 1 zero_le_one zero_le_two) fun y hy => by
      have hy0 : 0 ≤ y := hx.trans hy.le
      rw [comparison_sqrt_candidate_eq two_pos hy0]
      have h1 : 0 < Real.sqrt (y ^ 2 + 2) := Real.sqrt_pos.mpr (by positivity)
      have h3 : Real.sqrt (y ^ 2 + 2) ^ 2 = y ^ 2 + 2 := Real.sq_sqrt (by positivity)
      have hlt : y < Real.sqrt (y ^ 2 + 2) := by nlinarith
      apply div_pos _ (by positivity)
      nlinarith [sq_pos_of_pos (sub_pos.mpr hlt)]
  simpa only [one_mul] using this

/-- The upper bound of DLMF 7.8.2: `M(x) ≤ 1/(x + √(x² + 4/π))` for `x ≥ 0`. The comparison
function vanishes at `0` and at `+∞`, and its derivative changes sign at most once, from
positive to negative. -/
private theorem millsRatio_le_one_div_add_sqrt {x : ℝ} (hx : 0 ≤ x) :
    millsRatio x ≤ 1 / (x + Real.sqrt (x ^ 2 + 4 / π)) := by
  have hc : (0 : ℝ) < 4 / π := by positivity
  set c : ℝ := 4 / π with hcdef
  set N : ℝ → ℝ := fun y => c - 1 - y * (Real.sqrt (y ^ 2 + c) - y) with hN
  set q : ℝ → ℝ := fun y => Real.sqrt (y ^ 2 + c) * (y + Real.sqrt (y ^ 2 + c)) with hq
  have hq0 : ∀ y, 0 ≤ y → 0 < q y := fun y hy => by
    have : 0 < Real.sqrt (y ^ 2 + c) := Real.sqrt_pos.mpr (by positivity)
    simp only [hq]
    positivity
  have hEd : ∀ y, 0 ≤ y → HasDerivAt (fun y => Real.exp (-y ^ 2) *
      (1 / (1 * y + Real.sqrt (y ^ 2 + c))) - Real.sqrt π / 2 * TauCeti.Real.erfc y)
      (Real.exp (-y ^ 2) * (N y / q y)) y := fun y hy => by
    have := hasDerivAt_comparison
      (Real.hasDerivAt_div_mul_add_sqrt_sq_add 1 1 hc (one_mul_add_sqrt_ne_zero hc hy))
    rwa [comparison_sqrt_candidate_eq hc hy] at this
  have hs4 : Real.sqrt (4 / π) = 2 / Real.sqrt π := by
    rw [Real.sqrt_div' _ Real.pi_pos.le, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq zero_le_two]
  have hE0 := nonneg_of_tendsto_atTop_of_deriv_nonpos_stable hx hEd
    (by simp only [hcdef]; norm_num [TauCeti.Real.erfc_zero, hs4])
    (tendsto_comparison (Real.tendsto_div_mul_add_sqrt_sq_add_atTop 1 zero_le_one hc.le))
    fun y z hy hyz h => by
      have hNy : N y ≤ 0 := by
        by_contra! hpos
        exact h.not_gt (mul_pos (Real.exp_pos _) (div_pos hpos (hq0 y hy.le)))
      have hmono := Real.monotoneOn_mul_sqrt_sq_add_sub hc (mem_Ici.mpr hy.le)
        (mem_Ici.mpr (hy.le.trans hyz)) hyz
      have hNz : N z ≤ N y := by
        beta_reduce at hmono
        simp only [hN]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (div_nonpos_of_nonpos_of_nonneg (hNz.trans hNy) (hq0 z (hy.le.trans hyz)).le)
  simpa only [one_mul] using
    millsRatio_le_of (g := fun y => 1 / (1 * y + Real.sqrt (y ^ 2 + c))) hE0

/-- **DLMF 7.8.2**, with Mills' ratio written out as `(√π/2) e^{x²} erfc x`: for `x ≥ 0`,
`1/(x + √(x² + 2)) < M(x) ≤ 1/(x + √(x² + 4/π))`. -/
theorem millsRatio_bounds {x : ℝ} (hx : 0 ≤ x) :
    1 / (x + Real.sqrt (x ^ 2 + 2)) < Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x ∧
      Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x ≤ 1 / (x + Real.sqrt (x ^ 2 + 4 / π)) := by
  rw [← millsRatio_def]
  exact ⟨one_div_add_sqrt_two_lt_millsRatio hx, millsRatio_le_one_div_add_sqrt hx⟩

/-- The lower bound of DLMF 7.8.3: `√π/(2√π x + 2) ≤ M(x)` for `x ≥ 0`. The comparison function
vanishes at `0` and at `+∞`, and its derivative changes sign at most once. -/
private theorem sqrt_pi_div_le_millsRatio {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt π / (2 * Real.sqrt π * x + 2) ≤ millsRatio x := by
  set k := Real.sqrt π
  have hk0 : 0 < k := Real.sqrt_pos.mpr Real.pi_pos
  set N : ℝ → ℝ := fun y => 4 - 2 * k ^ 2 + 4 * k * y with hN
  have hg : ∀ y, 0 ≤ y → HasDerivAt (fun y => k / (2 * k * y + 2))
      (-(2 * k ^ 2) / (2 * k * y + 2) ^ 2) y := fun y hy => by
    have hD : HasDerivAt (fun y => 2 * k * y + 2) (2 * k) y := by
      simpa using ((hasDerivAt_id y).const_mul (2 * k)).add_const 2
    exact ((hasDerivAt_const y k).div hD (by positivity)).congr_deriv (by ring)
  have hFd : ∀ y, 0 ≤ y → HasDerivAt (fun y => -(Real.exp (-y ^ 2) * (k / (2 * k * y + 2)) -
      k / 2 * TauCeti.Real.erfc y)) (-(Real.exp (-y ^ 2) * (N y / (2 * k * y + 2) ^ 2))) y :=
    fun y hy => by
      refine (hasDerivAt_comparison (hg y hy)).neg.congr_deriv ?_
      have : 2 * k * y + 2 ≠ 0 := by positivity
      simp only [hN]
      field_simp
      ring
  have hlim : Tendsto (fun y => k / (2 * k * y + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 (tendsto_id.const_mul_atTop (by positivity)))
  have hF0 := nonneg_of_tendsto_atTop_of_deriv_nonpos_stable hx hFd
    (by norm_num [TauCeti.Real.erfc_zero]) (by simpa using (tendsto_comparison hlim).neg)
    fun y z hy hyz h => by
      have hz : 0 ≤ z := hy.le.trans hyz
      have hNy : 0 ≤ N y := by
        by_contra! hneg
        have : Real.exp (-y ^ 2) * (N y / (2 * k * y + 2) ^ 2) < 0 :=
          mul_neg_of_pos_of_neg (Real.exp_pos _) (div_neg_of_neg_of_pos hneg (by positivity))
        linarith
      have hNz : 0 ≤ N z := by
        simp only [hN] at hNy ⊢
        nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hyz)]
      have : 0 ≤ Real.exp (-z ^ 2) * (N z / (2 * k * z + 2) ^ 2) := by positivity
      linarith
  exact le_millsRatio_of (g := fun y => k / (2 * k * y + 2)) (by linarith)

/-- The upper bound of DLMF 7.8.3: `M(x) < 1/(x + 1)` for `x ≥ 0`. -/
private theorem millsRatio_lt_one_div_add_one {x : ℝ} (hx : 0 ≤ x) :
    millsRatio x < 1 / (x + 1) := by
  have hg : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun y : ℝ => 1 / (y + 1)) (-1 / (y + 1) ^ 2) y :=
    fun y hy => ((hasDerivAt_const y (1 : ℝ)).div ((hasDerivAt_id y).add_const 1)
      (by simp only [id]; positivity)).congr_deriv (by simp)
  refine millsRatio_lt (fun y hy => hg y (hx.trans hy))
    (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id)) fun y hy => ?_
  have hy0 : 0 < y := lt_of_le_of_lt hx hy
  have : -1 / (y + 1) ^ 2 - 2 * y * (1 / (y + 1)) + 1 = -(y ^ 2 / (y + 1) ^ 2) := by
    field_simp
    ring
  rw [this]
  have : 0 < y ^ 2 / (y + 1) ^ 2 := by positivity
  linarith

/-- **DLMF 7.8.3**, with Mills' ratio written out: for `x ≥ 0`,
`√π/(2√π x + 2) ≤ M(x) < 1/(x + 1)`. -/
theorem millsRatio_bounds_affine {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt π / (2 * Real.sqrt π * x + 2) ≤ Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x ∧
      Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x < 1 / (x + 1) := by
  rw [← millsRatio_def]
  exact ⟨sqrt_pi_div_le_millsRatio hx, millsRatio_lt_one_div_add_one hx⟩

/-- **DLMF 7.8.4**, with Mills' ratio written out: for `x > −√2/2`,
`M(x) < 2/(3x + √(x² + 4))`. -/
theorem millsRatio_lt_two_div {x : ℝ} (hx : -Real.sqrt 2 / 2 < x) :
    Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x < 2 / (3 * x + Real.sqrt (x ^ 2 + 4)) := by
  rw [← millsRatio_def]
  have hsq : ∀ y : ℝ, Real.sqrt (y ^ 2 + 4) ^ 2 = y ^ 2 + 4 := fun y => Real.sq_sqrt (by positivity)
  have hsp : ∀ y : ℝ, 0 < Real.sqrt (y ^ 2 + 4) := fun y => Real.sqrt_pos.mpr (by positivity)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < Real.sqrt 2 := by positivity
  have hD : ∀ y, x ≤ y → 0 < 3 * y + Real.sqrt (y ^ 2 + 4) := by
    intro y hy
    rcases le_or_gt 0 y with h | h
    · have := hsp y; linarith
    · nlinarith [hsq y, hsp y]
  refine millsRatio_lt (g := fun y => 2 / (3 * y + Real.sqrt (y ^ 2 + 4)))
    (fun y hy => Real.hasDerivAt_div_mul_add_sqrt_sq_add 2 3 (by norm_num) (hD y hy).ne')
    (Real.tendsto_div_mul_add_sqrt_sq_add_atTop 2 (by norm_num) (by norm_num)) ?_
  intro y hy
  have hDy := hD y hy.le
  have h1 := hsp y
  have h3 := hsq y
  set s := Real.sqrt (y ^ 2 + 4)
  have hid : -2 * (3 + y / s) / (3 * y + s) ^ 2 - 2 * y * (2 / (3 * y + s)) + 1 =
      (2 * y * (3 + y ^ 2) - 2 * s * (1 + y ^ 2)) / (s * (3 * y + s) ^ 2) := by
    field_simp
    linear_combination (2 * y + s) * h3
  rw [hid]
  apply div_neg_of_neg_of_pos _ (by positivity)
  rcases le_or_gt y 0 with hy0 | hy0
  · nlinarith [sq_nonneg y]
  · have hkey : (s * (1 + y ^ 2)) ^ 2 - (y * (3 + y ^ 2)) ^ 2 = 4 := by
      linear_combination (1 + y ^ 2) ^ 2 * h3
    nlinarith [sq_nonneg (s * (1 + y ^ 2) - y * (3 + y ^ 2)), mul_pos h1 (by positivity : (0:ℝ) <
        1 + y ^ 2),
      mul_pos hy0 (by positivity : (0:ℝ) < 3 + y ^ 2)]

/-- A function eventually between `0` and `C/y` tends to `0` at `+∞`. -/
private theorem tendsto_zero_of_nonneg_of_le_div (C : ℝ) {g : ℝ → ℝ}
    (h0 : ∀ᶠ y in atTop, 0 ≤ g y) (hC : ∀ᶠ y in atTop, g y ≤ C / y) :
    Tendsto g atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop tendsto_id) h0 hC

/-- The first inequality of DLMF 7.8.5: `x²/(2x² + 1) ≤ x²(2x² + 5)/(4x⁴ + 12x² + 3)`. -/
private theorem sq_div_le_rat (x : ℝ) :
    x ^ 2 / (2 * x ^ 2 + 1) ≤ x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]

/-- The second inequality of DLMF 7.8.5: `x²(2x² + 5)/(4x⁴ + 12x² + 3) ≤ x M(x)` for `x ≥ 0`,
from the candidate `g = y(2y² + 5)/(4y⁴ + 12y² + 3)`, for which `q²(g′ − 2yg + 1) = 24`. -/
private theorem rat_le_mul_millsRatio {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) ≤ x * millsRatio x := by
  have hq : ∀ y : ℝ, 0 < 4 * y ^ 4 + 12 * y ^ 2 + 3 := fun y => by positivity
  have hg : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3))
      (((6 * y ^ 2 + 5) * (4 * y ^ 4 + 12 * y ^ 2 + 3) -
        y * (2 * y ^ 2 + 5) * (16 * y ^ 3 + 24 * y)) / (4 * y ^ 4 + 12 * y ^ 2 + 3) ^ 2) y := by
    intro y
    have hp : HasDerivAt (fun y : ℝ => y * (2 * y ^ 2 + 5)) (6 * y ^ 2 + 5) y :=
      ((hasDerivAt_id y).mul (((hasDerivAt_pow 2 y).const_mul 2).add_const 5)).congr_deriv
        (by simp; ring)
    have hd : HasDerivAt (fun y : ℝ => 4 * y ^ 4 + 12 * y ^ 2 + 3) (16 * y ^ 3 + 24 * y) y :=
      ((((hasDerivAt_pow 4 y).const_mul 4).add
        ((hasDerivAt_pow 2 y).const_mul 12)).add_const 3).congr_deriv (by simp; ring)
    exact hp.div hd (hq y).ne'
  have hlim : Tendsto (fun y : ℝ => y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3))
      atTop (𝓝 0) := by
    refine tendsto_zero_of_nonneg_of_le_div 2 ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with y hy
      exact div_nonneg (by positivity) (hq y).le
    · filter_upwards [eventually_ge_atTop 1] with y hy
      rw [div_le_div_iff₀ (hq y) (by linarith)]
      nlinarith [pow_le_pow_left₀ zero_le_one hy 2, pow_le_pow_left₀ zero_le_one hy 3,
        pow_le_pow_left₀ zero_le_one hy 4]
  have h := lt_millsRatio (x := x) (fun y _ => hg y) hlim fun y _ => by
    have := hq y
    rw [show ((6 * y ^ 2 + 5) * (4 * y ^ 4 + 12 * y ^ 2 + 3) -
        y * (2 * y ^ 2 + 5) * (16 * y ^ 3 + 24 * y)) / (4 * y ^ 4 + 12 * y ^ 2 + 3) ^ 2 -
        2 * y * (y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3)) + 1 =
        24 / (4 * y ^ 4 + 12 * y ^ 2 + 3) ^ 2 by field_simp; ring]
    positivity
  rw [show x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) =
    x * (x * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3)) by ring]
  exact mul_le_mul_of_nonneg_left h.le hx

/-- The third inequality of DLMF 7.8.5: `x M(x) < (2x⁴ + 9x² + 4)/(4x⁴ + 20x² + 15)` for
`x ≥ 0`, from the candidate `g = (2y⁴ + 9y² + 4)/(y(4y⁴ + 20y² + 15))`, for which
`q²(g′ − 2yg + 1) = −60`. -/
private theorem mul_millsRatio_lt_rat {x : ℝ} (hx : 0 ≤ x) :
    x * millsRatio x < (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) := by
  rcases hx.eq_or_lt with rfl | hx0
  · norm_num
  have hq : ∀ y : ℝ, 0 < y → 0 < y * (4 * y ^ 4 + 20 * y ^ 2 + 15) := fun y hy => by positivity
  have hg : ∀ y : ℝ, 0 < y → HasDerivAt
      (fun y : ℝ => (2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)))
      (((8 * y ^ 3 + 18 * y) * (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) -
        (2 * y ^ 4 + 9 * y ^ 2 + 4) * (20 * y ^ 4 + 60 * y ^ 2 + 15)) /
        (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2) y := by
    intro y hy
    have hp : HasDerivAt (fun y : ℝ => 2 * y ^ 4 + 9 * y ^ 2 + 4) (8 * y ^ 3 + 18 * y) y :=
      ((((hasDerivAt_pow 4 y).const_mul 2).add
        ((hasDerivAt_pow 2 y).const_mul 9)).add_const 4).congr_deriv (by simp; ring)
    have hd : HasDerivAt (fun y : ℝ => y * (4 * y ^ 4 + 20 * y ^ 2 + 15))
        (20 * y ^ 4 + 60 * y ^ 2 + 15) y :=
      ((hasDerivAt_id y).mul ((((hasDerivAt_pow 4 y).const_mul 4).add
        ((hasDerivAt_pow 2 y).const_mul 20)).add_const 15)).congr_deriv (by simp; ring)
    exact hp.div hd (hq y hy).ne'
  have hlim : Tendsto
      (fun y : ℝ => (2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)))
      atTop (𝓝 0) := by
    refine tendsto_zero_of_nonneg_of_le_div 4 ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with y hy
      exact div_nonneg (by positivity) (hq y hy).le
    · filter_upwards [eventually_ge_atTop 1] with y hy
      rw [div_le_div_iff₀ (hq y (by linarith)) (by linarith)]
      nlinarith [pow_le_pow_left₀ zero_le_one hy 2, pow_le_pow_left₀ zero_le_one hy 3,
        pow_le_pow_left₀ zero_le_one hy 4, pow_le_pow_left₀ zero_le_one hy 5]
  have h := millsRatio_lt (x := x) (fun y hy => hg y (hx0.trans_le hy)) hlim fun y hy => by
    have hy0 : 0 < y := hx0.trans hy
    have := hq y hy0
    rw [show ((8 * y ^ 3 + 18 * y) * (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) -
        (2 * y ^ 4 + 9 * y ^ 2 + 4) * (20 * y ^ 4 + 60 * y ^ 2 + 15)) /
        (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2 -
        2 * y * ((2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15))) + 1 =
        -(60 / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2) by field_simp; ring]
    exact neg_neg_of_pos (by positivity)
  have := mul_lt_mul_of_pos_left h hx0
  rwa [show x * ((2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15))) =
    (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) by field_simp] at this

/-- The fourth inequality of DLMF 7.8.5:
`(2x⁴ + 9x² + 4)/(4x⁴ + 20x² + 15) < (x² + 1)/(2x² + 3)`. -/
private theorem rat_lt_rat (x : ℝ) :
    (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) <
      (x ^ 2 + 1) / (2 * x ^ 2 + 3) := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]

/-- **DLMF 7.8.5**, with Mills' ratio written out: for `x ≥ 0`,
`x²/(2x² + 1) ≤ x²(2x² + 5)/(4x⁴ + 12x² + 3) ≤ x M(x) < (2x⁴ + 9x² + 4)/(4x⁴ + 20x² + 15) <
(x² + 1)/(2x² + 3)`. -/
theorem mul_millsRatio_bounds {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / (2 * x ^ 2 + 1) ≤ x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) ∧
      x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) ≤
        x * (Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x) ∧
      x * (Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x) <
        (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) ∧
      (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) <
        (x ^ 2 + 1) / (2 * x ^ 2 + 3) := by
  rw [← millsRatio_def]
  exact ⟨sq_div_le_rat x, rat_le_mul_millsRatio hx, mul_millsRatio_lt_rat hx, rat_lt_rat x⟩

/-- **DLMF 7.8.6.** For `a > 0` and `x > 0`,
`∫₀ˣ e^{at²} dt < (2e^{ax²} + ax² − 2)/(3ax)`. -/
theorem integral_exp_mul_sq_lt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, Real.exp (a * t ^ 2)) <
      (2 * Real.exp (a * x ^ 2) + a * x ^ 2 - 2) / (3 * a * x) := by
  set I : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, Real.exp (a * t ^ 2) with hI
  have hId : ∀ y, HasDerivAt I (Real.exp (a * y ^ 2)) y := fun y =>
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (a * t ^ 2)).integral_hasStrictDerivAt
      0 y).hasDerivAt
  have hI0 : I 0 = 0 := by simp [hI]
  have he : ∀ y, HasDerivAt (fun y => Real.exp (a * y ^ 2))
      (Real.exp (a * y ^ 2) * (a * (2 * y))) y := fun y =>
    ((hasDerivAt_pow 2 y).const_mul a).exp.congr_deriv (by norm_num)
  -- A function vanishing at `0` with positive derivative on `(0, ∞)` is positive there.
  have hpos : ∀ {F F' : ℝ → ℝ}, (∀ y, HasDerivAt F (F' y) y) → F 0 = 0 →
      (∀ y, 0 < y → 0 < F' y) → ∀ y, 0 < y → 0 < F y := by
    intro F F' hF h0 hF' y hy
    have := strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun y _ => (hF y).continuousAt.continuousWithinAt) (fun y _ => (hF y).hasDerivWithinAt)
      (fun y hy => hF' y (by simpa using hy)) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy.le) hy
    rwa [h0] at this
  -- ψ = (x e^{ax²} + 2x)/3 − I
  have hψ : ∀ y, HasDerivAt (fun y => (y * Real.exp (a * y ^ 2) + 2 * y) / 3 - I y)
      ((2 / 3) * (1 + (a * y ^ 2 - 1) * Real.exp (a * y ^ 2))) y := fun y =>
    ((((hasDerivAt_id y).mul (he y)).add ((hasDerivAt_id y).const_mul 2)).div_const 3
      |>.sub (hId y)).congr_deriv (by simp only [id_eq]; ring)
  have hψpos : ∀ y, 0 < y → 0 < (2 / 3) * (1 + (a * y ^ 2 - 1) * Real.exp (a * y ^ 2)) := by
    intro y hy
    have hu : 0 < a * y ^ 2 := by positivity
    have hlt := Real.add_one_lt_exp (by linarith : -(a * y ^ 2) < 0).ne
    have : 1 + (a * y ^ 2 - 1) * Real.exp (a * y ^ 2) =
        Real.exp (a * y ^ 2) * (Real.exp (-(a * y ^ 2)) - (1 - a * y ^ 2)) := by
      rw [mul_sub, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      ring
    rw [this]
    exact mul_pos (by norm_num) (mul_pos (Real.exp_pos _) (by linarith))
  have hφ : ∀ y, HasDerivAt
      (fun y => (2 * Real.exp (a * y ^ 2) + a * y ^ 2 - 2) / (3 * a) - y * I y)
      ((y * Real.exp (a * y ^ 2) + 2 * y) / 3 - I y) y := fun y =>
    (((((he y).const_mul 2).add ((hasDerivAt_pow 2 y).const_mul a)).sub_const 2).div_const
      (3 * a) |>.sub ((hasDerivAt_id y).mul (hId y))).congr_deriv
      (by simp only [id_eq]; field_simp; ring)
  have hφx := hpos hφ (by simp [hI0]) (hpos hψ (by simp [hI0]) hψpos) x hx
  rw [lt_div_iff₀ (by positivity)]
  have : 2 * Real.exp (a * x ^ 2) + a * x ^ 2 - 2 =
      3 * a * ((2 * Real.exp (a * x ^ 2) + a * x ^ 2 - 2) / (3 * a)) := by
    field_simp
  nlinarith

/-- The secant bound behind DLMF 7.8.8. For `b > 0`, the function
`φ(u) = e^{−bu} − 1 + mu` is strictly convex and vanishes at `0`, so `φ(t) < (t/s) φ(s)` for
`0 < t < s`. -/
private theorem exp_neg_mul_sub_one_add_lt {b m t s : ℝ} (hb : 0 < b) (ht : 0 < t)
    (hts : t < s) :
    Real.exp (-(b * t)) - 1 + m * t < t / s * (Real.exp (-(b * s)) - 1 + m * s) := by
  have hs : 0 < s := ht.trans hts
  set θ := t / s with hθ
  have hθ0 : 0 < θ := div_pos ht hs
  have hθ1 : θ < 1 := (div_lt_one hs).mpr hts
  have h := strictConvexOn_exp.2 (mem_univ 0) (mem_univ (-(b * s)))
    (neg_neg_of_pos (mul_pos hb hs)).ne' (by linarith : 0 < 1 - θ) hθ0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have ht' : t = θ * s := by simp only [hθ]; field_simp
  rw [ht', show -(b * (θ * s)) = θ * -(b * s) by ring]
  nlinarith

/-- **Sign propagation for a secant-convex derivative.** Let `D(0) = 0` and
`D′(y) = w(y) φ(y²)` with `w > 0`, where `φ(t) < (t/s) φ(s)` for `0 < t < s`. If `D(y) ≥ 0` at
some `y > 0`, then `D > 0` on `(y, ∞)`. -/
private theorem pos_of_hasDerivAt_mul_secant {D w φ : ℝ → ℝ} (hw : ∀ y, 0 < w y)
    (hD : ∀ y, HasDerivAt D (w y * φ (y ^ 2)) y) (hD0 : D 0 = 0)
    (hsec : ∀ t s, 0 < t → t < s → φ t < t / s * φ s) {y : ℝ} (hy : 0 < y) (hDy : 0 ≤ D y)
    {t : ℝ} (hyt : y < t) : 0 < D t := by
  have hφy : 0 < φ (y ^ 2) := by
    by_contra! hcon
    have hanti : StrictAntiOn D (Icc 0 y) :=
      strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 y)
        (fun s _ => (hD s).continuousAt.continuousWithinAt)
        (fun s _ => (hD s).hasDerivWithinAt) fun s hs => by
          rw [interior_Icc] at hs
          have hs0 : 0 < s := hs.1
          have h1 := hsec _ _ (by positivity : 0 < s ^ 2) (by nlinarith [hs.2] : s ^ 2 < y ^ 2)
          have h2 : s ^ 2 / y ^ 2 * φ (y ^ 2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
          exact mul_neg_of_pos_of_neg (hw s) (by linarith)
    have := hanti ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy
    linarith
  have hpos : ∀ s, y ≤ s → 0 < w s * φ (s ^ 2) := by
    intro s hs
    rcases hs.eq_or_lt with rfl | h
    · exact mul_pos (hw _) hφy
    · have h1 := hsec _ _ (by positivity : 0 < y ^ 2) (by nlinarith : y ^ 2 < s ^ 2)
      have h2 : 0 < φ (s ^ 2) := by
        by_contra! hcon
        have : y ^ 2 / s ^ 2 * φ (s ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
        linarith
      exact mul_pos (hw s) h2
  have hmono : StrictMonoOn D (Ici y) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici y)
      (fun s _ => (hD s).continuousAt.continuousWithinAt)
      (fun s _ => (hD s).hasDerivWithinAt) fun s hs => by
        rw [interior_Ici] at hs
        exact hpos s (le_of_lt hs)
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hyt.le) hyt
  linarith

/-- The derivative of `D(y) = erf y − c y e^{(1 − k) y²}` with `c = 2/√π`. -/
private theorem hasDerivAt_erf_sub_mul_exp (k y : ℝ) :
    HasDerivAt (fun y => TauCeti.Real.erf y - 2 / Real.sqrt π * y * Real.exp ((1 - k) * y ^ 2))
      (2 / Real.sqrt π * Real.exp ((1 - k) * y ^ 2) *
        (Real.exp (-((2 - k) * y ^ 2)) - 1 + 2 * (k - 1) * y ^ 2)) y := by
  have he : HasDerivAt (fun y : ℝ => Real.exp ((1 - k) * y ^ 2))
      (Real.exp ((1 - k) * y ^ 2) * ((1 - k) * (2 * y))) y :=
    ((hasDerivAt_pow 2 y).const_mul (1 - k)).exp.congr_deriv (by norm_num)
  refine ((TauCeti.Real.hasDerivAt_erf y).sub
    (((hasDerivAt_id y).const_mul (2 / Real.sqrt π)).mul he)).congr_deriv ?_
  have hsplit : Real.exp (-y ^ 2) = Real.exp ((1 - k) * y ^ 2) * Real.exp (-((2 - k) * y ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [id]
  rw [hsplit]
  ring

/-- The derivative of `h(y) = 1 − e^{−ky²} − erf² y` is `−2c e^{−y²} D(y)`, with `c = 2/√π`,
`c² = k` and `D` as in `hasDerivAt_erf_sub_mul_exp`. -/
private theorem hasDerivAt_one_sub_exp_sub_erf_sq {k : ℝ} (hk : (2 / Real.sqrt π) ^ 2 = k)
    (y : ℝ) :
    HasDerivAt (fun y => 1 - Real.exp (-(k * y ^ 2)) - TauCeti.Real.erf y ^ 2)
      (-(2 * (2 / Real.sqrt π) * Real.exp (-y ^ 2)) *
        (TauCeti.Real.erf y - 2 / Real.sqrt π * y * Real.exp ((1 - k) * y ^ 2))) y := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(k * y ^ 2)))
      (Real.exp (-(k * y ^ 2)) * (-(k * (2 * y)))) y :=
    ((hasDerivAt_pow 2 y).const_mul k).neg.exp.congr_deriv (by norm_num)
  refine ((he.const_sub 1).sub ((TauCeti.Real.hasDerivAt_erf y).pow 2)).congr_deriv ?_
  have hsplit : Real.exp (-(k * y ^ 2)) = Real.exp (-y ^ 2) * Real.exp ((1 - k) * y ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  push_cast
  linear_combination (-(2 * y * Real.exp (-y ^ 2) * Real.exp ((1 - k) * y ^ 2))) * hk

/-- **DLMF 7.8.8.** For `x > 0`, `erf x < √(1 − e^{−4x²/π})`.

With `k = 4/π` and `c = 2/√π`, the function `h(y) = 1 − e^{−ky²} − erf² y` vanishes at `0` and at
`+∞`, and `h′ = −2c e^{−y²} D` with `D(y) = erf y − c y e^{(1 − k) y²}`. Once `D ≥ 0` at a
positive point it stays positive (`pos_of_hasDerivAt_mul_secant`), so `h′` changes sign at most
once, and `h > 0` on `(0, ∞)`. -/
theorem erf_lt_sqrt_one_sub_exp {x : ℝ} (hx : 0 < x) :
    erf x < Real.sqrt (1 - Real.exp (-4 * x ^ 2 / π)) := by
  set k : ℝ := 4 / π with hkdef
  have hπ := Real.pi_pos
  have hk0 : 0 < k := by positivity
  have hck : (2 / Real.sqrt π) ^ 2 = k := by
    rw [div_pow, Real.sq_sqrt hπ.le, hkdef]
    norm_num
  have hk2 : 0 < 2 - k := by
    have : k < 2 := by rw [hkdef, div_lt_iff₀ hπ]; linarith [Real.pi_gt_three]
    linarith
  have hD : ∀ y, 0 < y → 0 ≤ TauCeti.Real.erf y - 2 / Real.sqrt π * y *
      Real.exp ((1 - k) * y ^ 2) → ∀ t, y < t →
      0 < TauCeti.Real.erf t - 2 / Real.sqrt π * t * Real.exp ((1 - k) * t ^ 2) :=
    fun y hy hDy t hyt => pos_of_hasDerivAt_mul_secant
      (w := fun y => 2 / Real.sqrt π * Real.exp ((1 - k) * y ^ 2))
      (φ := fun u => Real.exp (-((2 - k) * u)) - 1 + 2 * (k - 1) * u)
      (fun y => by positivity) (hasDerivAt_erf_sub_mul_exp k)
      (by simp [TauCeti.Real.erf_zero]) (fun t s ht hts => exp_neg_mul_sub_one_add_lt hk2 ht hts)
      hy hDy hyt
  have hlim : Tendsto (fun y => 1 - Real.exp (-(k * y ^ 2)) - TauCeti.Real.erf y ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.exp (-(k * y ^ 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hk0))
    simpa using (h1.const_sub 1).sub (TauCeti.Real.tendsto_erf_atTop.pow 2)
  have hhx := pos_of_tendsto_atTop_of_deriv_nonpos_stable hx
    (fun y _ => hasDerivAt_one_sub_exp_sub_erf_sq hck y) (by simp [TauCeti.Real.erf_zero]) hlim
    fun y z hy hyz h => by
      have hw : ∀ s, 0 < 2 * (2 / Real.sqrt π) * Real.exp (-s ^ 2) := fun s => by positivity
      have hDy : 0 ≤ TauCeti.Real.erf y - 2 / Real.sqrt π * y * Real.exp ((1 - k) * y ^ 2) := by
        by_contra! hneg
        exact h.not_gt (mul_pos_of_neg_of_neg (neg_neg_of_pos (hw y)) hneg)
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hw z)) (hD y hy hDy z hyz)
  rw [Real.lt_sqrt (TauCeti.Real.erf_nonneg hx.le),
    show -4 * x ^ 2 / π = -(k * x ^ 2) by rw [hkdef]; ring]
  linarith

end TauCeti.Real
