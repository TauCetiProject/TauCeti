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
compares `erf` with `c y e^{(1 − k) y²}`, `k = 4/π`, using convexity of `exp`.

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

/-- **DLMF 7.8.2**, with Mills' ratio written out as `(√π/2) e^{x²} erfc x`: for `x ≥ 0`,
`1/(x + √(x² + 2)) < M(x) ≤ 1/(x + √(x² + 4/π))`. -/
theorem millsRatio_bounds {x : ℝ} (hx : 0 ≤ x) :
    1 / (x + Real.sqrt (x ^ 2 + 2)) < Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x ∧
      Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x ≤ 1 / (x + Real.sqrt (x ^ 2 + 4 / π)) := by
  rw [← millsRatio_def]
  have hsq : ∀ c y : ℝ, 0 < c → Real.sqrt (y ^ 2 + c) ^ 2 = y ^ 2 + c := fun c y hc =>
      Real.sq_sqrt (by positivity)
  have hsp : ∀ c y : ℝ, 0 < c → 0 < Real.sqrt (y ^ 2 + c) := fun c y hc =>
      Real.sqrt_pos.mpr (by positivity)
  have hD : ∀ c y : ℝ, 0 < c → 0 ≤ y → 1 * y + Real.sqrt (y ^ 2 + c) ≠ 0 := fun c y hc hy => by
    have := hsp c y hc; positivity
  -- the key identity for `P`
  have hP : ∀ c y : ℝ, 0 < c → 0 ≤ y →
      -1 * (1 + y / Real.sqrt (y ^ 2 + c)) / (1 * y + Real.sqrt (y ^ 2 + c)) ^ 2 -
          2 * y * (1 / (1 * y + Real.sqrt (y ^ 2 + c))) + 1
        = (c - 1 - y * (Real.sqrt (y ^ 2 + c) - y)) / (Real.sqrt (y ^ 2 + c) * (y +
            Real.sqrt (y ^ 2 + c))) := by
    intro c y hc hy
    have h2 : y + Real.sqrt (y ^ 2 + c) ≠ 0 := by positivity
    have h3 := hsq c y hc
    rw [show c - 1 - y * (Real.sqrt (y ^ 2 + c) - y) = Real.sqrt (y ^ 2 + c) ^ 2 - y *
        Real.sqrt (y ^ 2 + c) - 1 by
      rw [h3]; ring]
    field_simp
    ring
  constructor
  · have := lt_millsRatio (x := x) (g := fun y => 1 / (1 * y + Real.sqrt (y ^ 2 + 2)))
      (fun y hy => Real.hasDerivAt_div_mul_add_sqrt_sq_add 1 1 two_pos
          (hD 2 y two_pos (hx.trans hy)))
      (Real.tendsto_div_mul_add_sqrt_sq_add_atTop 1 zero_le_one zero_le_two) ?_
    · simpa only [one_mul] using this
    intro y hy
    have hy0 : 0 ≤ y := hx.trans hy.le
    rw [hP 2 y two_pos hy0]
    have h1 := hsp 2 y two_pos
    have h3 := hsq 2 y two_pos
    have hlt : y < Real.sqrt (y ^ 2 + 2) := by nlinarith
    apply div_pos _ (by positivity)
    nlinarith [sq_pos_of_pos (sub_pos.mpr hlt)]
  · have hc : (0:ℝ) < 4 / π := by positivity
    have hc1 : 1 < 4 / π := by rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    set c : ℝ := 4 / π with hcdef
    set N : ℝ → ℝ := fun y => c - 1 - y * (Real.sqrt (y ^ 2 + c) - y) with hN
    set E : ℝ → ℝ := fun y => Real.exp (-y ^ 2) * (1 / (1 * y + Real.sqrt (y ^ 2 + c))) -
      Real.sqrt π / 2 * TauCeti.Real.erfc y with hE
    have hEd : ∀ y, 0 ≤ y → HasDerivAt E (Real.exp (-y ^ 2) *
        (N y / (Real.sqrt (y ^ 2 + c) * (y + Real.sqrt (y ^ 2 + c))))) y := by
      intro y hy
      have := hasDerivAt_comparison
          (Real.hasDerivAt_div_mul_add_sqrt_sq_add 1 1 hc (hD c y hc hy))
      rw [hP c y hc hy] at this
      exact this
    have hEP : ∀ y, 0 ≤ y → (0 ≤ N y ↔ 0 ≤ Real.exp (-y ^ 2) *
        (N y / (Real.sqrt (y ^ 2 + c) * (y + Real.sqrt (y ^ 2 + c))))) := by
      intro y hy
      have hq : 0 < Real.sqrt (y ^ 2 + c) * (y + Real.sqrt (y ^ 2 + c)) := by positivity
      rw [mul_nonneg_iff_of_pos_left (Real.exp_pos _), div_nonneg_iff]
      constructor
      · intro h; exact Or.inl ⟨h, hq.le⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact h
        · linarith
    have hE0 : 0 ≤ E x := by
      rcases le_or_gt (N x) 0 with hNx | hNx
      · refine nonneg_of_tendsto_atTop_of_deriv_nonpos (fun y hy => hEd y (hx.trans hy)) ?_ ?_
        · exact tendsto_comparison
              (Real.tendsto_div_mul_add_sqrt_sq_add_atTop 1 zero_le_one hc.le)
        · intro y hy
          have hNy : N y ≤ 0 := by
            have := Real.monotoneOn_mul_sqrt_sq_add_sub hc (mem_Ici.mpr hx)
              (mem_Ici.mpr (hx.trans hy.le)) hy.le
            beta_reduce at this
            simp only [hN]; linarith
          have hq : 0 < Real.sqrt (y ^ 2 + c) * (y + Real.sqrt (y ^ 2 + c)) := by
            have := hx.trans hy.le; positivity
          exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
              (div_nonpos_of_nonpos_of_nonneg hNy hq.le)
      · have h := le_of_deriv_nonneg_Icc hx (fun y hy => hEd y hy.1) (fun y ⟨hy, hyx⟩ => by
          rw [← hEP y hy.le]
          have := Real.monotoneOn_mul_sqrt_sq_add_sub hc (mem_Ici.mpr hy.le) (mem_Ici.mpr hx)
            hyx.le
          beta_reduce at this
          simp only [hN] at hNx ⊢; linarith)
        have hs4 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact Real.sqrt_sq zero_le_two
        have h0 : E 0 = 0 := by
          simp only [hE, hcdef]
          norm_num [TauCeti.Real.erfc_zero, hs4]
        linarith
    have := millsRatio_le_of (g := fun y => 1 / (1 * y + Real.sqrt (y ^ 2 + c))) hE0
    simpa only [one_mul] using this

/-- **DLMF 7.8.3**, with Mills' ratio written out: for `x ≥ 0`,
`√π/(2√π x + 2) ≤ M(x) < 1/(x + 1)`. -/
theorem millsRatio_bounds_affine {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt π / (2 * Real.sqrt π * x + 2) ≤ Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x ∧
      Real.sqrt π / 2 * Real.exp (x ^ 2) * erfc x < 1 / (x + 1) := by
  rw [← millsRatio_def]
  constructor
  · set k := Real.sqrt π
    have hk0 : 0 < k := Real.sqrt_pos.mpr Real.pi_pos
    set N : ℝ → ℝ := fun y => 4 - 2 * k ^ 2 + 4 * k * y with hN
    set F : ℝ → ℝ := fun y => -(Real.exp (-y ^ 2) * (k / (2 * k * y + 2)) - k / 2 *
        TauCeti.Real.erfc y) with hF
    have hg : ∀ y, 0 ≤ y → HasDerivAt (fun y => k / (2 * k * y + 2)) (-(2 * k ^ 2) / (2 * k * y +
        2) ^ 2) y := by
      intro y hy
      have hD : HasDerivAt (fun y => 2 * k * y + 2) (2 * k) y := by
        have := ((hasDerivAt_id y).const_mul (2 * k)).add_const 2
        exact this.congr_deriv (by simp)
      have := (hasDerivAt_const y k).div hD (by positivity)
      exact this.congr_deriv (by ring)
    have hFd : ∀ y, 0 ≤ y → HasDerivAt F (-(Real.exp (-y ^ 2) * (N y / (2 * k * y + 2) ^ 2))) y :=
        by
      intro y hy
      have := (hasDerivAt_comparison (hg y hy)).neg
      refine this.congr_deriv ?_
      have : (2 * k * y + 2) ≠ 0 := by positivity
      simp only [hN]
      field_simp
      ring
    have hF0 : 0 ≤ F x := by
      rcases le_or_gt 0 (N x) with hNx | hNx
      · refine nonneg_of_tendsto_atTop_of_deriv_nonpos (fun y hy => hFd y (hx.trans hy)) ?_ ?_
        · have hlim : Tendsto (fun y => k / (2 * k * y + 2)) atTop (𝓝 0) := by
            refine tendsto_const_nhds.div_atTop ?_
            exact tendsto_atTop_add_const_right _ 2 (tendsto_id.const_mul_atTop (by positivity))
          have := (tendsto_comparison hlim).neg
          rw [neg_zero] at this
          exact this
        · intro y hy
          have hNy : 0 ≤ N y := by simp only [hN] at hNx ⊢; nlinarith
          have : 0 ≤ Real.exp (-y ^ 2) * (N y / (2 * k * y + 2) ^ 2) := by positivity
          linarith
      · have h := le_of_deriv_nonneg_Icc hx (fun y hy => hFd y hy.1) (fun y ⟨hy, hyx⟩ => by
          have hNy : N y < 0 := by simp only [hN] at hNx ⊢; nlinarith
          have : Real.exp (-y ^ 2) * (N y / (2 * k * y + 2) ^ 2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
              (div_nonpos_of_nonpos_of_nonneg hNy.le (by positivity))
          linarith)
        have h0 : F 0 = 0 := by
          simp only [hF]
          norm_num [TauCeti.Real.erfc_zero]
        linarith
    have := le_millsRatio_of (g := fun y => k / (2 * k * y + 2)) (x := x)
        (by simp only [hF] at hF0; linarith)
    exact this
  · have hg : ∀ y : ℝ, 0 ≤ y → HasDerivAt (fun y : ℝ => 1 / (y + 1)) (-1 / (y + 1) ^ 2) y := by
      intro y hy
      have := (hasDerivAt_const y (1:ℝ)).div ((hasDerivAt_id y).add_const 1)
          (by simp only [id]; positivity)
      exact this.congr_deriv (by simp)
    refine millsRatio_lt (fun y hy => hg y (hx.trans hy)) ?_ ?_
    · refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_id
    · intro y hy
      have hy0 : 0 < y := lt_of_le_of_lt hx hy
      have : -1 / (y + 1) ^ 2 - 2 * y * (1 / (y + 1)) + 1 = -(y ^ 2 / (y + 1) ^ 2) := by
        field_simp; ring
      rw [this]
      have : 0 < y ^ 2 / (y + 1) ^ 2 := by positivity
      linarith

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
  have hq1 : ∀ y : ℝ, 0 < 4 * y ^ 4 + 12 * y ^ 2 + 3 := fun y => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (hq1 x)];
        nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]
  · -- lower bound via `g₁ = y(2y² + 5) / (4y⁴ + 12y² + 3)`, with `q₁² (g₁' − 2y g₁ + 1) = 24`
    have hg : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3))
        (((6 * y ^ 2 + 5) * (4 * y ^ 4 + 12 * y ^ 2 + 3) - y * (2 * y ^ 2 + 5) * (16 * y ^ 3 + 24 *
            y)) / (4 * y ^ 4 + 12 * y ^ 2 + 3) ^ 2) y := by
      intro y
      have hp : HasDerivAt (fun y : ℝ => y * (2 * y ^ 2 + 5)) (6 * y ^ 2 + 5) y := by
        have := (hasDerivAt_id y).mul (((hasDerivAt_pow 2 y).const_mul 2).add_const 5)
        exact this.congr_deriv (by simp; ring)
      have hq : HasDerivAt (fun y : ℝ => 4 * y ^ 4 + 12 * y ^ 2 + 3) (16 * y ^ 3 + 24 * y) y := by
        have := (((hasDerivAt_pow 4 y).const_mul 4).add
            ((hasDerivAt_pow 2 y).const_mul 12)).add_const 3
        exact this.congr_deriv (by simp; ring)
      exact hp.div hq (hq1 y).ne'
    have hlim : Tendsto (fun y : ℝ => y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 +
        3)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun y : ℝ => 2 / y) atTop (𝓝 0)) ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with y hy
        exact div_nonneg (by positivity) (hq1 y).le
      · filter_upwards [eventually_ge_atTop 1] with y hy
        rw [div_le_div_iff₀ (hq1 y) (by linarith)]
        nlinarith [pow_le_pow_left₀ zero_le_one hy 2, pow_le_pow_left₀ zero_le_one hy 3,
          pow_le_pow_left₀ zero_le_one hy 4]
    have h := lt_millsRatio (x := x) (fun y _ => hg y) hlim (fun y _ => by
      have : 0 < (4 * y ^ 4 + 12 * y ^ 2 + 3) := hq1 y
      rw [show ((6 * y ^ 2 + 5) * (4 * y ^ 4 + 12 * y ^ 2 + 3) - y * (2 * y ^ 2 + 5) * (16 *
          y ^ 3 + 24 * y)) / (4 * y ^ 4 + 12 * y ^ 2 + 3) ^ 2
          - 2 * y * (y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3)) + 1 = 24 / (4 * y ^ 4 +
              12 * y ^ 2 + 3) ^ 2 by
        field_simp; ring]
      positivity)
    rw [show x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) = x * (x * (2 * x ^ 2 + 5) /
        (4 * x ^ 4 + 12 * x ^ 2 + 3)) by ring]
    exact mul_le_mul_of_nonneg_left h.le hx
  · rcases hx.eq_or_lt with h0 | hx0
    · subst h0; norm_num
    have hq2 : ∀ y : ℝ, 0 < y → 0 < y * (4 * y ^ 4 + 20 * y ^ 2 + 15) := fun y hy => by positivity
    have hg : ∀ y : ℝ, 0 < y → HasDerivAt (fun y : ℝ => (2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 *
        y ^ 4 + 20 * y ^ 2 + 15)))
        (((8 * y ^ 3 + 18 * y) * (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) - (2 * y ^ 4 + 9 * y ^ 2 +
            4) * (20 * y ^ 4 + 60 * y ^ 2 + 15))/
          (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2) y := by
      intro y hy
      have hp : HasDerivAt (fun y : ℝ => 2 * y ^ 4 + 9 * y ^ 2 + 4) (8 * y ^ 3 + 18 * y) y := by
        have := (((hasDerivAt_pow 4 y).const_mul 2).add
            ((hasDerivAt_pow 2 y).const_mul 9)).add_const 4
        exact this.congr_deriv (by simp; ring)
      have hq : HasDerivAt (fun y : ℝ => y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) (20 * y ^ 4 + 60 *
          y ^ 2 + 15) y := by
        have := (hasDerivAt_id y).mul ((((hasDerivAt_pow 4 y).const_mul 4).add
          ((hasDerivAt_pow 2 y).const_mul 20)).add_const 15)
        exact this.congr_deriv (by simp; ring)
      exact hp.div hq (hq2 y hy).ne'
    have hlim : Tendsto (fun y : ℝ => (2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 +
        15))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun y : ℝ => 4 / y) atTop (𝓝 0)) ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact div_nonneg (by positivity) (hq2 y hy).le
      · filter_upwards [eventually_ge_atTop 1] with y hy
        rw [div_le_div_iff₀ (hq2 y (by linarith)) (by linarith)]
        nlinarith [pow_le_pow_left₀ zero_le_one hy 2, pow_le_pow_left₀ zero_le_one hy 3,
          pow_le_pow_left₀ zero_le_one hy 4, pow_le_pow_left₀ zero_le_one hy 5]
    have h := millsRatio_lt (x := x) (fun y hy => hg y (hx0.trans_le hy)) hlim
        (fun y hy => by
      have hy0 : 0 < y := hx0.trans hy
      have : 0 < y * (4 * y ^ 4 + 20 * y ^ 2 + 15) := hq2 y hy0
      rw [show ((8 * y ^ 3 + 18 * y) * (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) - (2 * y ^ 4 + 9 *
          y ^ 2 + 4) * (20 * y ^ 4 + 60 * y ^ 2 + 15))/
          (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2 - 2 * y * ((2 * y ^ 4 + 9 * y ^ 2 + 4) / (y *
              (4 * y ^ 4 + 20 * y ^ 2 + 15))) + 1
          = -60 / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2 by
        field_simp; ring]
      have : 0 < 60 / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2 := by positivity
      rw [neg_div]; linarith)
    have := mul_lt_mul_of_pos_left h hx0
    rw [show x * ((2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15))) = (2 * x ^ 4 +
        9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) by
      field_simp] at this
    exact this
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)];
        nlinarith [sq_nonneg x, pow_nonneg (sq_nonneg x) 2]

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
  -- ψ = (x e^{ax²} + 2x)/3 − I
  have hψ : ∀ y, HasDerivAt (fun y => (y * Real.exp (a * y ^ 2) + 2 * y) / 3 - I y)
      ((2 / 3) * (1 + (a * y ^ 2 - 1) * Real.exp (a * y ^ 2))) y := by
    intro y
    have h1 : HasDerivAt (fun y => Real.exp (a * y ^ 2)) (Real.exp (a * y ^ 2) * (a * (2 *
        y))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul a).exp
      exact this.congr_deriv (by norm_num)
    have := (((hasDerivAt_id y).mul h1).add ((hasDerivAt_id y).const_mul 2)).div_const
        3 |>.sub (hId y)
    exact this.congr_deriv (by simp only [id_eq]; ring)
  have hψpos : ∀ y, 0 < y → 0 < (2 / 3) * (1 + (a * y ^ 2 - 1) * Real.exp (a * y ^ 2)) := by
    intro y hy
    have hu : 0 < a * y ^ 2 := by positivity
    have he := Real.add_one_lt_exp (by linarith : -(a * y ^ 2) < 0).ne
    have hE := Real.exp_pos (a * y ^ 2)
    have : 1 + (a * y ^ 2 - 1) * Real.exp (a * y ^ 2) = Real.exp (a * y ^ 2) *
        (Real.exp (-(a * y ^ 2)) - (1 - a * y ^ 2)) := by
      rw [mul_sub, ← Real.exp_add]; simp; ring
    rw [this]; have : 0 < Real.exp (-(a * y ^ 2)) - (1 - a * y ^ 2) := by linarith
    exact mul_pos (by norm_num) (mul_pos hE this)
  have hφ : ∀ y, HasDerivAt (fun y => (2 * Real.exp (a * y ^ 2) + a * y ^ 2 - 2) / (3 * a) - y *
      I y)
      ((y * Real.exp (a * y ^ 2) + 2 * y) / 3 - I y) y := by
    intro y
    have h1 : HasDerivAt (fun y => Real.exp (a * y ^ 2)) (Real.exp (a * y ^ 2) * (a * (2 *
        y))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul a).exp
      exact this.congr_deriv (by norm_num)
    have := ((((h1.const_mul 2).add ((hasDerivAt_pow 2 y).const_mul a)).sub_const
        2).div_const (3 * a)).sub
      ((hasDerivAt_id y).mul (hId y))
    exact this.congr_deriv (by simp only [id_eq]; field_simp; ring)
  have hpos := pos_of_deriv_pos_of_eq_zero (fun y _ => hφ y) (by simp [hI0])
    (fun y hy => pos_of_deriv_pos_of_eq_zero (fun y _ => hψ y) (by simp [hI0]) hψpos hy) hx
  rw [lt_div_iff₀ (by positivity)]
  have : (2 * Real.exp (a * x ^ 2) + a * x ^ 2 - 2) = 3 * a * ((2 * Real.exp (a * x ^ 2) + a *
      x ^ 2 - 2) / (3 * a)) := by
    field_simp
  nlinarith

/-- **DLMF 7.8.8.** For `x > 0`, `erf x < √(1 − e^{−4x²/π})`. -/
theorem erf_lt_sqrt_one_sub_exp {x : ℝ} (hx : 0 < x) :
    erf x < Real.sqrt (1 - Real.exp (-4 * x ^ 2 / π)) := by
  set k : ℝ := 4 / π with hk
  set c : ℝ := 2 / Real.sqrt π with hc
  have hπ := Real.pi_pos
  have hk0 : 0 < k := by positivity
  have hck : c ^ 2 = k := by
    simp only [hc, hk, div_pow, Real.sq_sqrt hπ.le]; norm_num
  set m : ℝ := 2 * (k - 1) with hm
  have hk2 : 0 < 2 - k := by
    have : k < 2 := by rw [hk, div_lt_iff₀ hπ]; linarith [Real.pi_gt_three]
    linarith
  -- Secant bound from strict convexity of `exp`: `φ(t) < (t/s) φ(s)` for `0 < t < s`, where
  -- `φ(u) = e^{-(2-k)u} - 1 + mu` vanishes at `0`.
  have hsec : ∀ t s : ℝ, 0 < t → t < s →
      Real.exp (-((2 - k) * t)) - 1 + m * t < t / s * (Real.exp (-((2 - k) * s)) - 1 + m * s) := by
    intro t s ht hts
    have hs : 0 < s := ht.trans hts
    set θ := t / s with hθ
    have hθ0 : 0 < θ := div_pos ht hs
    have hθ1 : θ < 1 := (div_lt_one hs).mpr hts
    have hne : (0 : ℝ) ≠ -((2 - k) * s) := by nlinarith
    have h := strictConvexOn_exp.2 (mem_univ 0) (mem_univ (-((2 - k) * s))) hne
      (by linarith : 0 < 1 - θ) hθ0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    have ht' : t = θ * s := by simp only [hθ]; field_simp
    rw [ht', show -((2 - k) * (θ * s)) = θ * -((2 - k) * s) by ring]
    nlinarith
  set ph : ℝ → ℝ := fun u => Real.exp (-((2 - k) * u)) - 1 + m * u with hph
  set D : ℝ → ℝ := fun y => TauCeti.Real.erf y - c * y * Real.exp ((1 - k) * y ^ 2) with hD
  have hDd : ∀ y, HasDerivAt D (c * Real.exp ((1 - k) * y ^ 2) * ph (y ^ 2)) y := by
    intro y
    have he : HasDerivAt (fun y : ℝ => Real.exp ((1 - k) * y ^ 2))
        (Real.exp ((1 - k) * y ^ 2) * ((1 - k) * (2 * y))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul (1 - k)).exp
      exact this.congr_deriv (by norm_num)
    have := (TauCeti.Real.hasDerivAt_erf y).sub (((hasDerivAt_id y).const_mul c).mul he)
    refine this.congr_deriv ?_
    simp only [hph, hm, id, ← hc]
    have : Real.exp (-y ^ 2) = Real.exp ((1 - k) * y ^ 2) * Real.exp (-((2 - k) * y ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hD0 : D 0 = 0 := by simp [hD]
  -- (P): once `D ≥ 0` at a positive point, it stays positive afterwards
  have hP : ∀ y, 0 < y → 0 ≤ D y → ∀ t, y < t → 0 < D t := by
    intro y hy hDy
    have hphy : 0 < ph (y ^ 2) := by
      by_contra hcon
      push Not at hcon
      have hneg : ∀ s, 0 < s → s < y → c * Real.exp ((1 - k) * s ^ 2) * ph (s ^ 2) < 0 := by
        intro s hs hsy
        have h1 := hsec _ _ (by positivity : 0 < s ^ 2)
          (by nlinarith : s ^ 2 < y ^ 2)
        have h2 : s ^ 2 / y ^ 2 * ph (y ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
        have : ph (s ^ 2) < 0 := by simp only [hph] at h2 ⊢; linarith
        exact mul_neg_of_pos_of_neg (by positivity) this
      have hanti : StrictAntiOn D (Icc 0 y) :=
        strictAntiOn_of_deriv_neg (convex_Icc 0 y)
            (fun s _ => (hDd s).continuousAt.continuousWithinAt)
          (fun s hs => by rw [interior_Icc] at hs; rw [(hDd s).deriv]; exact hneg s hs.1 hs.2)
      have := hanti ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy
      linarith
    have hpos : ∀ s, y ≤ s → 0 < c * Real.exp ((1 - k) * s ^ 2) * ph (s ^ 2) := by
      intro s hs
      rcases hs.eq_or_lt with h | h
      · subst h; positivity
      · have h1 := hsec _ _ (by positivity : 0 < y ^ 2)
            (by nlinarith : y ^ 2 < s ^ 2)
        have h2 : 0 < ph (s ^ 2) := by
          by_contra hcon
          push Not at hcon
          have : y ^ 2 / s ^ 2 * ph (s ^ 2) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
          simp only [hph] at this hphy h1; linarith
        positivity
    have hmono : StrictMonoOn D (Ici y) :=
      strictMonoOn_of_deriv_pos (convex_Ici y) (fun s _ => (hDd s).continuousAt.continuousWithinAt)
        (fun s hs => by rw [interior_Ici] at hs; rw [(hDd s).deriv]; exact hpos s hs.le)
    intro t ht
    have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht
    linarith
  -- `h = 1 - e^{-ky²} - erf² ` with `h' = -2c e^{-y²} D`
  set h : ℝ → ℝ := fun y => 1 - Real.exp (-(k * y ^ 2)) - TauCeti.Real.erf y ^ 2 with hh
  have hhd : ∀ y, HasDerivAt h (-(2 * c * Real.exp (-y ^ 2)) * D y) y := by
    intro y
    have he : HasDerivAt (fun y : ℝ => Real.exp (-(k * y ^ 2)))
        (Real.exp (-(k * y ^ 2)) * (-(k * (2 * y)))) y := by
      have := ((hasDerivAt_pow 2 y).const_mul k).neg.exp
      exact this.congr_deriv (by norm_num)
    have := (he.const_sub 1).sub ((TauCeti.Real.hasDerivAt_erf y).pow 2)
    refine this.congr_deriv ?_
    simp only [hD, ← hc]
    have : Real.exp (-(k * y ^ 2)) = Real.exp (-y ^ 2) * Real.exp ((1 - k) * y ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, ← hck]; norm_num; ring
  have hh0 : h 0 = 0 := by simp [hh, TauCeti.Real.erf_zero]
  have hhx : 0 < h x := by
    rcases le_or_gt 0 (D x) with hDx | hDx
    · have hlim : Tendsto h atTop (𝓝 0) := by
        have h1 : Tendsto (fun y : ℝ => Real.exp (-(k * y ^ 2))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
            ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hk0))
        have h2 := TauCeti.Real.tendsto_erf_atTop.pow 2
        have := (h1.const_sub 1).sub h2
        simpa using this
      refine pos_of_tendsto_atTop_of_deriv_neg (fun y _ => hhd y) hlim (fun y hy => ?_)
      have := hP x hx hDx y hy
      have : 0 < 2 * c * Real.exp (-y ^ 2) := by positivity
      nlinarith
    · have hneg : ∀ y, 0 < y → y < x → D y < 0 := by
        intro y hy hyx
        by_contra hcon
        push Not at hcon
        have := hP y hy hcon x hyx
        linarith
      have hmono : StrictMonoOn h (Icc 0 x) :=
        strictMonoOn_of_deriv_pos (convex_Icc 0 x)
            (fun s _ => (hhd s).continuousAt.continuousWithinAt)
          (fun s hs => by
            rw [interior_Icc] at hs; rw [(hhd s).deriv]
            have := hneg s hs.1 hs.2
            have : 0 < 2 * c * Real.exp (-s ^ 2) := by positivity
            nlinarith)
      have := hmono ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx
      linarith
  rw [Real.lt_sqrt (TauCeti.Real.erf_nonneg hx.le)]
  have : -4 * x ^ 2 / π = -(k * x ^ 2) := by rw [hk]; ring
  rw [this]
  simp only [hh] at hhx
  linarith

end TauCeti.Real
