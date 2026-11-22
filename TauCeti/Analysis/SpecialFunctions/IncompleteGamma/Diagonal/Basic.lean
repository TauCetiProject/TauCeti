/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moments

/-!
# Diagonal asymptotics of the incomplete Gamma functions

For large positive `a`, the Euler integral `Γ(a) = ∫₀^∞ t^{a - 1} e^{-t} dt` concentrates in a
window of width `O(√a)` around its saddle point `t = a`. Splitting the integral at `t = a` splits
`Γ(a)` into the lower incomplete Gamma function `γ(a, a)` and the upper tail `Γ(a) - γ(a, a)`.
After scaling `t = a (1 - x)`, both halves share the single convex phase
`ψ(x) = -x - log (1 - x)` (evaluated at `x = v ∈ (0, 1)` on the lower side and `x = -v ∈ (-∞, 0)`
on the upper side). Passing to the quadratic coordinate `u` with `u² / 2 = ψ(x)` turns the main
contribution of each half into a linear combination of Gaussian moments
`a ∫₀^∞ u^k e^{-a u² / 2} du`, with coefficients `q_k` on the lower side and `(-1)^k q_k` on the
upper side.

Subtracting `Γ(a) / 2` from `γ(a, a)` cancels every even-order moment (all half-integer powers and
`√(2π)` factors), leaving a pure series in integer powers of `a⁻¹`:
`a^{1 - a} e^a (γ(a, a) - Γ(a) / 2) = 1/3 + 4/(135 a) - 8/(2835 a²) - 16/(8505 a³) + O(a^{-4})`.

## Main results

* `TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub` and
  `TauCeti.isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub`: eight-term normalized diagonal
  expansions of `γ(a, a)` and `Γ(a) - γ(a, a)` to `O(a^{-7/2})`.
* `TauCeti.isBigO_Gamma_sub_lowerIncompleteGamma_diag` and
  `TauCeti.isBigO_lowerIncompleteGamma_diag`: six-term unnormalized diagonal expansions of
  `Γ(a) - γ(a, a)` (DLMF 8.11.12) and `γ(a, a)` to `O(a^{a - 7/2} e^{-a})`.
* `TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma`: pure integer-power expansion of
  `a^{1 - a} e^a (γ(a, a) - Γ(a) / 2)` to `O(a^{-4})`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(v)](https://dlmf.nist.gov/8.11.v),
  Eq. 8.11.12.
* E. T. Copson, *An approximation connected with $e^{-x}$*, Proc. Edinburgh Math. Soc. (2) **3**
  (1933), 201–206.
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*, Math. Z. **53**
  (1950), 136–148.
* J. D. Buckholtz, *Concerning an approximation of Copson*, Proc. Amer. Math. Soc. **14** (1963),
  564–568.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Set
open scoped Nat Topology Interval

namespace TauCeti

/-! ### Phase function and polynomial coordinate approximation -/

/-- The saddle-point phase `ψ(x) = -x - log (1 - x)` governing Euler's integral near `t = a`. -/
private def diagPhase (x : ℝ) : ℝ := -x - Real.log (1 - x)

private theorem diagPhase_zero : diagPhase 0 = 0 := by simp [diagPhase]

private theorem hasDerivAt_diagPhase {x : ℝ} (hx : x < 1) :
    HasDerivAt diagPhase (x / (1 - x)) x := by
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.ne'
  refine ((hasDerivAt_id x).neg.sub (((hasDerivAt_id x).const_sub 1).log h1)).congr_deriv ?_
  simp only [id]; field_simp; ring

private theorem continuousOn_diagPhase : ContinuousOn diagPhase (Iio 1) := fun _ hx =>
  (hasDerivAt_diagPhase hx).continuousAt.continuousWithinAt

private theorem diagPhase_lower_quad {x : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3)) :
    3 / 8 * x ^ 2 ≤ diagPhase x := by
  have hd (y : ℝ) (hy : y < 1) :
      HasDerivAt (fun z => diagPhase z - 3 / 8 * z ^ 2) (y * (1 / (1 - y) - 3 / 4)) y := by
    have h1 : 1 - y ≠ 0 := sub_ne_zero.mpr hy.ne'
    exact ((hasDerivAt_diagPhase hy).sub
      ((hasDerivAt_pow 2 y).const_mul (3 / 8 : ℝ))).congr_deriv (by field_simp; ring)
  have hmin : IsMinOn (fun z => diagPhase z - 3 / 8 * z ^ 2) (Icc (-(1 / 3)) (1 / 3)) 0 :=
    isMinOn_Icc_of_deriv (hd _ (by norm_num)).continuousAt (hd 0 (by norm_num)).continuousAt
      (hd _ (by norm_num)).continuousAt
      (fun y hy => (hd y (by linarith [hy.2])).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y (by linarith [hy.2])).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [(hd y (by linarith [hy.2])).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg hy.2.le
          (sub_nonneg.mpr (by rw [le_div_iff₀ (by linarith [hy.2])]; linarith [hy.1])))
      (fun y hy => by
        rw [(hd y (by linarith [hy.2])).deriv]
        exact mul_nonneg hy.1.le
          (sub_nonneg.mpr (by rw [le_div_iff₀ (by linarith [hy.2])]; linarith [hy.1])))
  have h0 : 0 ≤ diagPhase x - 3 / 8 * x ^ 2 := by simpa [diagPhase_zero] using hmin hx
  linarith

private theorem diagPhase_upper_quad {x : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3)) :
    diagPhase x ≤ 3 / 4 * x ^ 2 := by
  have hd (y : ℝ) (hy : y < 1) :
      HasDerivAt (fun z => 3 / 4 * z ^ 2 - diagPhase z) (y * (3 / 2 - 1 / (1 - y))) y := by
    have h1 : 1 - y ≠ 0 := sub_ne_zero.mpr hy.ne'
    exact (((hasDerivAt_pow 2 y).const_mul (3 / 4 : ℝ)).sub
      (hasDerivAt_diagPhase hy)).congr_deriv (by field_simp; ring)
  have hmin : IsMinOn (fun z => 3 / 4 * z ^ 2 - diagPhase z) (Icc (-(1 / 3)) (1 / 3)) 0 :=
    isMinOn_Icc_of_deriv (hd _ (by norm_num)).continuousAt (hd 0 (by norm_num)).continuousAt
      (hd _ (by norm_num)).continuousAt
      (fun y hy => (hd y (by linarith [hy.2])).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y (by linarith [hy.2])).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [(hd y (by linarith [hy.2])).deriv]
        exact mul_nonpos_of_nonpos_of_nonneg hy.2.le
          (sub_nonneg.mpr (by rw [div_le_iff₀ (by linarith [hy.2])]; linarith [hy.2])))
      (fun y hy => by
        rw [(hd y (by linarith [hy.2])).deriv]
        exact mul_nonneg hy.1.le
          (sub_nonneg.mpr (by rw [div_le_iff₀ (by linarith [hy.2])]; linarith [hy.2])))
  have h0 : 0 ≤ 3 / 4 * x ^ 2 - diagPhase x := by simpa [diagPhase_zero] using hmin hx
  linarith

private theorem diagPhase_lower_tail {v : ℝ} (hv1 : 1 / 3 ≤ v) (hv2 : v < 1) :
    1 / 24 ≤ diagPhase v := by
  have hmono : MonotoneOn diagPhase (Icc (1 / 3) v) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (1 / 3) v)
      (continuousOn_diagPhase.mono fun z hz => lt_of_le_of_lt hz.2 hv2)
      (fun y hy => (hasDerivAt_diagPhase
        (lt_of_le_of_lt (interior_subset hy).2 hv2)).differentiableAt.differentiableWithinAt)
      fun y hy => ?_
    rw [interior_Icc] at hy
    rw [(hasDerivAt_diagPhase (lt_trans hy.2 hv2)).deriv]
    exact div_nonneg (by linarith [hy.1]) (by linarith [hy.2])
  have h13 : 1 / 24 ≤ diagPhase (1 / 3) := by
    linarith [diagPhase_lower_quad (x := 1 / 3) ⟨by norm_num, le_rfl⟩]
  exact h13.trans (hmono (left_mem_Icc.mpr hv1) (right_mem_Icc.mpr hv1) hv1)

private theorem diagPhase_upper_tail {v : ℝ} (hv : 1 / 3 ≤ v) :
    1 / 24 + (v - 1 / 3) / 4 ≤ diagPhase (-v) := by
  have hf : ∀ y : ℝ, 0 ≤ y →
      HasDerivAt (fun z => diagPhase (-z) - (1 / 24 + (z - 1 / 3) / 4))
        (y / (1 + y) - 1 / 4) y := fun y hy => by
    have hd1 := (hasDerivAt_diagPhase (x := -y) (by linarith)).comp y (hasDerivAt_id y).neg
    have hd2 : HasDerivAt (fun z => 1 / 24 + (z - 1 / 3) / 4) (1 / 4) y := by
      simpa using (((hasDerivAt_id y).sub_const (1 / 3 : ℝ)).div_const 4).const_add (1 / 24 : ℝ)
    refine (hd1.sub hd2).congr_deriv ?_
    rw [sub_neg_eq_add]
    have : 1 + y ≠ 0 := by linarith
    field_simp
  have hmono : MonotoneOn (fun z => diagPhase (-z) - (1 / 24 + (z - 1 / 3) / 4))
      (Icc (1 / 3) v) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (1 / 3) v)
      (fun y hy => (hf y (by linarith [hy.1])).continuousAt.continuousWithinAt)
      (fun y hy => (hf y (by linarith [(interior_subset hy).1])).differentiableAt
        |>.differentiableWithinAt) fun y hy => ?_
    rw [interior_Icc] at hy
    rw [(hf y (by linarith [hy.1])).deriv]
    exact sub_nonneg.mpr (by rw [le_div_iff₀ (by linarith [hy.1])]; linarith [hy.1])
  have h13 : 1 / 24 ≤ diagPhase (-(1 / 3 : ℝ)) := by
    linarith [diagPhase_lower_quad (x := -(1 / 3 : ℝ)) ⟨le_rfl, by norm_num⟩]
  have hfv := hmono (left_mem_Icc.mpr hv) (right_mem_Icc.mpr hv) hv
  dsimp only at hfv; linarith

/-- Degree-8 Taylor polynomial of `u / x(u) = x'(u) + u` for `ψ(x(u)) = u² / 2`. -/
private def diagQ (u : ℝ) : ℝ :=
  1 + 1 / 3 * u + 1 / 12 * u ^ 2 + 2 / 135 * u ^ 3 + 1 / 864 * u ^ 4 -
    1 / 2835 * u ^ 5 - 139 / 777600 * u ^ 6 - 1 / 25515 * u ^ 7 - 571 / 261273600 * u ^ 8

/-- Coefficient sequence of `diagQ`. -/
private def diagQCoeff : ℕ → ℝ
  | 0 => 1 | 1 => 1 / 3 | 2 => 1 / 12 | 3 => 2 / 135 | 4 => 1 / 864
  | 5 => -1 / 2835 | 6 => -139 / 777600 | 7 => -1 / 25515 | 8 => -571 / 261273600 | _ => 0

private theorem diagQ_mul_eq_sum (s u : ℝ) :
    diagQ (s * u) = ∑ k ∈ Finset.range 9, (diagQCoeff k * s ^ k) * u ^ k := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, diagQ, diagQCoeff]; ring

/-- Degree-9 Taylor polynomial of the inverse phase coordinate `x(u)` with `x'(u) = diagQ u - u`. -/
private def diagU (u : ℝ) : ℝ :=
  u - 1 / 3 * u ^ 2 + 1 / 36 * u ^ 3 + 1 / 270 * u ^ 4 + 1 / 4320 * u ^ 5 -
    1 / 17010 * u ^ 6 - 139 / 5443200 * u ^ 7 - 1 / 204120 * u ^ 8 - 571 / 2351462400 * u ^ 9

/-- Quotient polynomial `(diagU u * diagQ u - u) / u ^ 10`. -/
private def diagR (u : ℝ) : ℝ :=
  -281 / 137781000 - 9571 / 27433728000 * u - 6149 / 888852787200 * u ^ 2 +
    198341 / 25395793920000 * u ^ 3 + 223 / 106662334464 * u ^ 4 +
    232969 / 799967508480000 * u ^ 5 + 9707 / 479980505088000 * u ^ 6 +
    326041 / 614375046512640000 * u ^ 7

private theorem diagU_mul_diagQ_sub (u : ℝ) :
    diagU u * diagQ u - u = u ^ 10 * diagR u := by
  simp only [diagU, diagQ, diagR]; ring

private theorem hasDerivAt_diagU (u : ℝ) : HasDerivAt diagU (diagQ u - u) u := by
  unfold diagU diagQ
  exact (((((((((hasDerivAt_id u).sub ((hasDerivAt_pow 2 u).const_mul (1 / 3 : ℝ))).add
    ((hasDerivAt_pow 3 u).const_mul (1 / 36 : ℝ))).add
    ((hasDerivAt_pow 4 u).const_mul (1 / 270 : ℝ))).add
    ((hasDerivAt_pow 5 u).const_mul (1 / 4320 : ℝ))).sub
    ((hasDerivAt_pow 6 u).const_mul (1 / 17010 : ℝ))).sub
    ((hasDerivAt_pow 7 u).const_mul (139 / 5443200 : ℝ))).sub
    ((hasDerivAt_pow 8 u).const_mul (1 / 204120 : ℝ))).sub
    ((hasDerivAt_pow 9 u).const_mul (571 / 2351462400 : ℝ))).congr_deriv (by ring)

private theorem abs_diagR_le_one {u : ℝ} (hu : |u| ≤ 1) : |diagR u| ≤ 1 := by
  have hp (k : ℕ) : -1 ≤ u ^ k ∧ u ^ k ≤ 1 :=
    abs_le.mp (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg u) hu)
  unfold diagR
  exact abs_le.mpr ⟨by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7],
    by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7]⟩

private theorem abs_diagQ_le_two {u : ℝ} (hu : |u| ≤ 1) : |diagQ u| ≤ 2 := by
  have hp (k : ℕ) : -1 ≤ u ^ k ∧ u ^ k ≤ 1 :=
    abs_le.mp (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg u) hu)
  unfold diagQ
  exact abs_le.mpr ⟨by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8],
    by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8]⟩

private theorem abs_diagU_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |diagU u - u| ≤ 1 / 5 * |u| := by
  have hp (k : ℕ) : -1 ≤ u ^ k ∧ u ^ k ≤ 1 :=
    abs_le.mp (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg u) (by linarith))
  have hB : |-1 / 3 + 1 / 36 * u + 1 / 270 * u ^ 2 + 1 / 4320 * u ^ 3 -
      1 / 17010 * u ^ 4 - 139 / 5443200 * u ^ 5 - 1 / 204120 * u ^ 6 -
      571 / 2351462400 * u ^ 7| ≤ 2 / 5 :=
    abs_le.mpr ⟨by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7],
      by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7]⟩
  have hfac : diagU u - u = u ^ 2 * (-1 / 3 + 1 / 36 * u + 1 / 270 * u ^ 2 +
      1 / 4320 * u ^ 3 - 1 / 17010 * u ^ 4 - 139 / 5443200 * u ^ 5 -
      1 / 204120 * u ^ 6 - 571 / 2351462400 * u ^ 7) := by unfold diagU; ring
  calc |diagU u - u| = |u| ^ 2 * _ := by rw [hfac, abs_mul, abs_pow]
    _ ≤ (1 / 2 * |u|) * (2 / 5) :=
        mul_le_mul (by nlinarith [abs_nonneg u]) hB (abs_nonneg _) (by positivity)
    _ = 1 / 5 * |u| := by ring

private theorem diagU_bounds {u : ℝ} (hu : |u| ≤ 1 / 2) :
    4 / 5 * |u| ≤ |diagU u| ∧ |diagU u| ≤ 3 / 5 := by
  have hd := abs_diagU_sub_le hu
  have h1 : |u| - |diagU u - u| ≤ |diagU u| := by
    simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub u (u - diagU u)
  have h2 : |diagU u| ≤ |u| + |diagU u - u| := by simpa using abs_add_le u (diagU u - u)
  exact ⟨by linarith, by linarith⟩

private theorem abs_diagPhase_diagU_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |diagPhase (diagU u) - u ^ 2 / 2| ≤ 3 * |u| ^ 11 := by
  have hg_deriv : ∀ t ∈ Icc (-|u|) |u|,
      HasDerivAt (fun s => diagPhase (diagU s) - s ^ 2 / 2)
        (t ^ 10 * diagR t / (1 - diagU t)) t := fun t ht => by
    have ht_half : |t| ≤ 1 / 2 := (abs_le.mpr ht).trans hu
    have hUt : diagU t < 1 := by linarith [(abs_le.mp (diagU_bounds ht_half).2).2]
    have h1 : 1 - diagU t ≠ 0 := sub_ne_zero.mpr hUt.ne'
    have hd1 := (hasDerivAt_diagPhase hUt).comp t (hasDerivAt_diagU t)
    refine (hd1.sub ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv ?_
    have hrel := diagU_mul_diagQ_sub t
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]; field_simp; linear_combination hrel
  have hg_bound : ∀ t ∈ Icc (-|u|) |u|,
      ‖t ^ 10 * diagR t / (1 - diagU t)‖ ≤ 3 * |u| ^ 10 := fun t ht => by
    have ht_abs : |t| ≤ |u| := abs_le.mpr ht
    have ht_half : |t| ≤ 1 / 2 := ht_abs.trans hu
    have hUt : 2 / 5 ≤ 1 - diagU t := by linarith [(abs_le.mp (diagU_bounds ht_half).2).2]
    have hRt : |diagR t| ≤ 1 := abs_diagR_le_one (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos (by linarith : 0 < 1 - diagU t)]
    calc |t| ^ 10 * |diagR t| / (1 - diagU t) ≤ |u| ^ 10 * 1 / (2 / 5) := by gcongr
      _ ≤ 3 * |u| ^ 10 := by nlinarith [pow_nonneg (abs_nonneg u) 10]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg_deriv t ht).hasDerivWithinAt) hg_bound (convex_Icc (-|u|) |u|)
    ⟨neg_nonpos.mpr (abs_nonneg u), abs_nonneg u⟩ (abs_le.mp le_rfl)
  calc |diagPhase (diagU u) - u ^ 2 / 2|
      = ‖(diagPhase (diagU u) - u ^ 2 / 2) - (diagPhase (diagU 0) - 0 ^ 2 / 2)‖ := by
          simp [diagU, diagPhase_zero]
    _ ≤ 3 * |u| ^ 10 * ‖u - 0‖ := hmvt
    _ = 3 * |u| ^ 11 := by rw [sub_zero, Real.norm_eq_abs, pow_succ]; ring

private theorem abs_sub_le_of_diagPhase_sub_le {x y r M : ℝ}
    (hr : 0 < r) (hxy : 0 < x * y) (hx : r ≤ |x| ∧ |x| ≤ 3 / 5)
    (hy : r ≤ |y| ∧ |y| ≤ 3 / 5) (hpsi : |diagPhase x - diagPhase y| ≤ M) :
    |x - y| ≤ (10 / (3 * r)) * M := by
  rcases eq_or_ne x y with rfl | h_ne
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (by positivity) (le_trans (abs_nonneg _) hpsi)
  · have hab : min x y < max x y := min_lt_max.mpr h_ne
    have hb1 : max x y < 1 := max_lt (by linarith [(abs_le.mp hx.2).2])
      (by linarith [(abs_le.mp hy.2).2])
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope diagPhase (fun z => z / (1 - z)) hab
      (continuousOn_diagPhase.mono fun z hz => lt_of_le_of_lt hz.2 hb1)
      (fun z hz => hasDerivAt_diagPhase (lt_trans hz.2 hb1))
    have hc_abs : r ≤ |c| := by
      rcases lt_or_gt_of_ne (by intro h0; subst h0; linarith : x ≠ 0) with hx_neg | hx_pos
      · have hy_neg : y < 0 := by nlinarith
        have hc_neg : c < 0 := lt_trans hc.2 (max_lt hx_neg hy_neg)
        have hb_le : max x y ≤ -r := max_le (by linarith [abs_of_neg hx_neg, hx.1])
          (by linarith [abs_of_neg hy_neg, hy.1])
        rw [abs_of_neg hc_neg]; linarith [hc.2]
      · have hy_pos : 0 < y := by nlinarith
        have ha_ge : r ≤ min x y := le_min (by linarith [abs_of_pos hx_pos, hx.1])
          (by linarith [abs_of_pos hy_pos, hy.1])
        rw [abs_of_pos (lt_of_lt_of_le hr (ha_ge.trans hc.1.le))]; linarith [hc.1]
    have ha_lb : -(3 / 5 : ℝ) ≤ min x y := le_min (abs_le.mp hx.2).1 (abs_le.mp hy.2).1
    have h1c : 0 < 1 - c ∧ 1 - c ≤ 8 / 5 := ⟨by linarith [hc.2], by linarith [hc.1, ha_lb]⟩
    have hderiv_lb : 3 / 10 * r ≤ |c / (1 - c)| := by
      rw [abs_div, abs_of_pos h1c.1, le_div_iff₀ h1c.1]; nlinarith
    have hprod : |diagPhase (max x y) - diagPhase (min x y)| = |c / (1 - c)| * |x - y| := by
      have := congr_arg abs ((eq_div_iff (sub_pos.mpr hab).ne').mp hslope)
      rwa [abs_mul, abs_of_pos (sub_pos.mpr hab), max_sub_min_eq_abs, abs_sub_comm, eq_comm] at this
    have hpsi_ab : |diagPhase (max x y) - diagPhase (min x y)| ≤ M := by
      rcases le_total x y with hle | hle <;>
        simpa [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hle, abs_sub_comm] using hpsi
    have hmul := (mul_le_mul_of_nonneg_right hderiv_lb (abs_nonneg _)).trans (hprod ▸ hpsi_ab)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 3 * r)]; linarith

private theorem abs_sub_diagU_le {x u : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3))
    (hx0 : x ≠ 0) (hu_sq : u ^ 2 = 2 * diagPhase x) (hxu : 0 < x * u)
    (hu_half : |u| ≤ 1 / 2) (hx_lower : |u| / 2 ≤ |x|) :
    |x - diagU u| ≤ 20 * |u| ^ 10 := by
  have hu_pos : 0 < |u| := abs_pos.mpr fun hu0 => hx0
    (by nlinarith [diagPhase_lower_quad hx, sq_nonneg x])
  have hU_bds := diagU_bounds hu_half
  have hU_sign : 0 < u * diagU u := by
    have : |u * (diagU u - u)| ≤ 1 / 5 * u ^ 2 := by
      rw [abs_mul, ← sq_abs]; nlinarith [abs_diagU_sub_le hu_half, abs_nonneg u]
    nlinarith [abs_le.mp this, sq_pos_of_pos hu_pos, sq_abs u]
  have hxU_sign : 0 < x * diagU u := by
    have : 0 < (x * u) * (u * diagU u) := mul_pos hxu hU_sign
    nlinarith [sq_pos_of_pos hu_pos, sq_abs u,
      show (x * u) * (u * diagU u) = u ^ 2 * (x * diagU u) by ring]
  have hdiff_psi : |diagPhase x - diagPhase (diagU u)| ≤ 3 * |u| ^ 11 := by
    rw [abs_sub_comm, show diagPhase x = u ^ 2 / 2 by linarith]
    exact abs_diagPhase_diagU_sub_le hu_half
  have hmain := abs_sub_le_of_diagPhase_sub_le (r := |u| / 2) (by positivity) hxU_sign
    ⟨hx_lower, by linarith [abs_le.mpr hx]⟩ ⟨by linarith [hU_bds.1], hU_bds.2⟩ hdiff_psi
  calc |x - diagU u| ≤ 10 / (3 * (|u| / 2)) * (3 * |u| ^ 11) := hmain
    _ = 20 * |u| ^ 10 := by
        have : |u| ≠ 0 := hu_pos.ne'
        rw [pow_succ]; field_simp; ring

private theorem abs_div_sub_diagQ_le {x u : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3))
    (hx0 : x ≠ 0) (hu_sq : u ^ 2 = 2 * diagPhase x) (hxu : 0 < x * u) :
    |u / x - diagQ u| ≤ 82 * |u| ^ 9 := by
  have hupp : u ^ 2 ≤ 3 / 2 * x ^ 2 := by linarith [diagPhase_upper_quad hx]
  have hu_half : |u| ≤ 1 / 2 :=
    abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [hx.1, hx.2] : u ^ 2 ≤ (1 / 2) ^ 2) (by norm_num))
  have hx_lower : |u| / 2 ≤ |x| := by
    have : (|u| / 2) ^ 2 ≤ |x| ^ 2 := by rw [sq_abs]; nlinarith [sq_abs u]
    nlinarith [abs_nonneg u, abs_nonneg x]
  have hxU := abs_sub_diagU_le hx hx0 hu_sq hxu hu_half hx_lower
  have hQ_le : |diagQ u| ≤ 2 := abs_diagQ_le_two (by linarith)
  have hR_le : |diagR u| ≤ 1 := abs_diagR_le_one (by linarith)
  have hnum : |u - x * diagQ u| ≤ 41 * |u| ^ 10 := by
    have hsplit : u - x * diagQ u = -(diagU u * diagQ u - u) + (diagU u - x) * diagQ u := by ring
    calc |u - x * diagQ u|
        ≤ |-(diagU u * diagQ u - u)| + |(diagU u - x) * diagQ u| := hsplit ▸ abs_add_le _ _
      _ = |u| ^ 10 * |diagR u| + |x - diagU u| * |diagQ u| := by
          rw [abs_neg, diagU_mul_diagQ_sub, abs_mul, abs_pow, abs_mul, abs_sub_comm]
      _ ≤ |u| ^ 10 * 1 + (20 * |u| ^ 10) * 2 := by gcongr
      _ = 41 * |u| ^ 10 := by ring
  rw [show u / x - diagQ u = (u - x * diagQ u) / x by field_simp, abs_div,
    div_le_iff₀ (abs_pos.mpr hx0)]
  calc |u - x * diagQ u| ≤ 41 * |u| ^ 10 := hnum
    _ = 82 * |u| ^ 9 * (|u| / 2) := by rw [pow_succ]; ring
    _ ≤ 82 * |u| ^ 9 * |x| := by gcongr

/-! ### Gaussian moments and Laplace integral reduction -/

/-- Eight-term asymptotic sum with sign `s = ±1` on odd moments (`s = 1` for `γ(a, a)`,
`s = -1` for `Γ(a) - γ(a, a)`). -/
private def diagSeries8 (s a : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + s * (1 / 3) +
    Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + s * (4 / (135 * a)) +
    Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - s * (8 / (2835 * a ^ 2)) -
    139 * Real.sqrt (2 * Real.pi) / 103680 * a ^ (-5 / 2 : ℝ) - s * (16 / (8505 * a ^ 3))

private theorem diagQ_mul_exp_eq_sum (a s : ℝ) :
    (fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) =
      fun u => ∑ k ∈ Finset.range 9,
        (diagQCoeff k * s ^ k) * (u ^ k * Real.exp (-(a / 2) * u ^ 2)) := by
  ext u; rw [diagQ_mul_eq_sum, Finset.sum_mul]; simp only [mul_assoc]

private theorem integrableOn_diagQ_mul_exp {a : ℝ} (ha : 0 < a) (s : ℝ) :
    IntegrableOn (fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) (Ioi 0) := by
  rw [diagQ_mul_exp_eq_sum]
  exact integrable_finsetSum _ fun k _ =>
    ((integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff k).mpr (half_pos ha)).const_mul _

private theorem integral_diagQ_mul_exp_eq {a s : ℝ} (ha : 0 < a) (hs : |s| = 1) :
    (a * ∫ u in Ioi (0 : ℝ), diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) =
      diagSeries8 s a - 571 * Real.sqrt (2 * Real.pi) / 4976640 * a ^ (-7 / 2 : ℝ) := by
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hs_even (k : ℕ) : s ^ (2 * k) = 1 := by rw [pow_mul, hs2, one_pow]
  have hs_odd (k : ℕ) : s ^ (2 * k + 1) = s := by rw [pow_succ, hs_even, one_mul]
  have heven (m : ℕ) : (a * ∫ u in Ioi (0 : ℝ), u ^ (2 * m) * Real.exp (-(a / 2) * u ^ 2)) =
      ((2 * m)! : ℝ) * Real.sqrt (2 * Real.pi) / (2 ^ (m + 1) * (m ! : ℝ)) *
        a ^ ((1 / 2 : ℝ) - m) := by
    rw [integral_Ioi_pow_two_mul_mul_exp_neg_mul_sq (a / 2) m]
    have hsqrt : Real.sqrt (Real.pi / (a / 2)) = Real.sqrt (2 * Real.pi) / Real.sqrt a := by
      rw [div_div_eq_mul_div, mul_comm Real.pi 2, Real.sqrt_div (by positivity)]
    have hrpow : a ^ ((1 / 2 : ℝ) - m) = Real.sqrt a / a ^ m := by
      rw [Real.rpow_sub ha, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    have hpow2 : (2 : ℝ) ^ (2 * m + 1) = 2 ^ m * 2 ^ (m + 1) := by
      rw [← pow_add]; congr 1; omega
    have hfact : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    rw [hsqrt, hrpow, div_pow, hpow2]
    field_simp [hfact, (Real.sqrt_pos.mpr ha).ne', ha.ne']
    rw [Real.sq_sqrt ha.le]
  have hodd (m : ℕ) : (a * ∫ u in Ioi (0 : ℝ), u ^ (2 * m + 1) * Real.exp (-(a / 2) * u ^ 2)) =
      2 ^ m * (m ! : ℝ) / a ^ m := by
    rw [integral_Ioi_pow_two_mul_add_one_mul_exp_neg_mul_sq (half_pos ha) m, div_pow, pow_succ,
      pow_succ]
    field_simp [ha.ne']
  rw [diagQ_mul_exp_eq_sum, integral_finsetSum _ fun k _ =>
    ((integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff k).mpr (half_pos ha)).const_mul _,
    Finset.mul_sum]
  have hterm (k : ℕ) : a * (∫ u in Ioi (0 : ℝ),
      (diagQCoeff k * s ^ k) * (u ^ k * Real.exp (-(a / 2) * u ^ 2))) =
      (diagQCoeff k * s ^ k) * (a * ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(a / 2) * u ^ 2)) := by
    rw [integral_const_mul]; ring
  simp_rw [hterm]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, diagQCoeff]
  rw [heven 0, hodd 0, heven 1, hodd 1, heven 2, hodd 2, heven 3, hodd 3, heven 4]
  simp only [diagSeries8, pow_zero, pow_one, hs2, hs_odd 1, hs_even 2, hs_odd 2, hs_even 3,
    hs_odd 3, hs_even 4, Nat.factorial]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_one, zero_add]
  have hpi : Real.sqrt (2 * Real.pi) / 2 = Real.sqrt (Real.pi / 2) := by
    rw [Real.sqrt_mul zero_le_two, Real.sqrt_div Real.pi_pos.le]
    field_simp [(Real.sqrt_pos.mpr two_pos).ne']
    rw [Real.sq_sqrt zero_le_two]
  linear_combination a ^ (1 / 2 : ℝ) * hpi

private theorem abs_diagQ_le_sum {u : ℝ} (hu : 0 ≤ u) (s : ℝ) (hs : |s| = 1) :
    |diagQ (s * u)| ≤ ∑ k ∈ Finset.range 9, u ^ k := by
  have hp (k : ℕ) : -(u ^ k) ≤ (s * u) ^ k ∧ (s * u) ^ k ≤ u ^ k :=
    abs_le.mp (by rw [abs_pow, abs_mul, hs, one_mul, abs_of_nonneg hu])
  unfold diagQ
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero]
  exact abs_le.mpr ⟨by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8],
    by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8]⟩

private theorem isBigO_gauss_tail {c s : ℝ} (hc : 0 < c) (hs : |s| = 1) :
    (fun a : ℝ => a * ∫ u in Ioi c, diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hdom : IntegrableOn (fun u : ℝ => (∑ k ∈ Finset.range 9, u ^ k) *
      Real.exp (-u ^ 2)) (Ioi c) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun k _ =>
      (((integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff k).mpr one_pos).mono_set
        (Ioi_subset_Ioi hc.le)).congr_fun
        (fun u _ => by simp only [neg_one_mul]) measurableSet_Ioi
  have hbound : (fun a : ℝ => ∫ u in Ioi c, diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2))
      =O[atTop] fun a : ℝ => Real.exp (-(c ^ 2 / 4) * a) := by
    refine IsBigO.of_bound |∫ u in Ioi c, (∑ k ∈ Finset.range 9, u ^ k) * Real.exp (-u ^ 2)| ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with a ha
    have hpt : ∀ᵐ u ∂(volume.restrict (Ioi c)),
        ‖diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)‖ ≤
          Real.exp (-(c ^ 2 / 4) * a) * ((∑ k ∈ Finset.range 9, u ^ k) * Real.exp (-u ^ 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := (lt_trans hc hu).le
      have hexp_le : Real.exp (-(a / 2) * u ^ 2) ≤
          Real.exp (-(c ^ 2 / 4) * a) * Real.exp (-u ^ 2) := by
        rw [← Real.exp_add]
        have h1 : 0 ≤ (a - 4) * u ^ 2 := mul_nonneg (by linarith) (sq_nonneg u)
        have h2 : 0 ≤ a * ((u - c) * (u + c)) :=
          mul_nonneg (by linarith) (mul_nonneg (by linarith [mem_Ioi.mp hu]) (by linarith))
        exact Real.exp_le_exp.mpr (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |diagQ (s * u)| * Real.exp (-(a / 2) * u ^ 2)
          ≤ (∑ k ∈ Finset.range 9, u ^ k) * (Real.exp (-(c ^ 2 / 4) * a) * Real.exp (-u ^ 2)) :=
            mul_le_mul (abs_diagQ_le_sum hu0 s hs) hexp_le (Real.exp_pos _).le
              (Finset.sum_nonneg fun k _ => pow_nonneg hu0 k)
        _ = _ := by ring
    have hint := norm_integral_le_of_norm_le (hdom.const_mul _) hpt
    rw [integral_const_mul] at hint
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hint.trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  exact ((isBigO_refl (fun a : ℝ => a) atTop).congr_right fun a => (Real.rpow_one a).symm)
    |>.mul_atTop_rpow_of_isBigO_rpow 1 (-5) (-4)
      (hbound.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) (-5)).isBigO) (by norm_num)

/-- Coordinate `u_-(v) = √(2 ψ(v))` for `v ∈ [0, 1/3]` and `u_+(v) = √(2 ψ(-v))` for `s = -1`. -/
private def diagCoord (s v : ℝ) : ℝ := Real.sqrt (2 * diagPhase (s * v))

private theorem mem_Icc_third_of_abs_eq_one {s v : ℝ} (hs : |s| = 1)
    (hv : v ∈ Icc (0 : ℝ) (1 / 3)) : s * v ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) :=
  abs_le.mp (by rw [abs_mul, hs, one_mul, abs_of_nonneg hv.1]; exact hv.2)

private theorem diagCoord_pos {s v : ℝ} (hs : |s| = 1) (hv : v ∈ Ioc (0 : ℝ) (1 / 3)) :
    0 < diagCoord s v := by
  refine Real.sqrt_pos.mpr ?_
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hq := diagPhase_lower_quad (mem_Icc_third_of_abs_eq_one hs ⟨hv.1.le, hv.2⟩)
  have hsq : (s * v) ^ 2 = v ^ 2 := by rw [mul_pow, hs2, one_mul]
  nlinarith [sq_pos_of_pos hv.1]

private theorem continuousOn_diagCoord {s : ℝ} (hs : |s| = 1) :
    ContinuousOn (diagCoord s) [[0, (1 / 3 : ℝ)]] := by
  rw [uIcc_of_le (by norm_num)]
  refine Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul ?_)
  exact continuousOn_diagPhase.comp ((continuous_const.mul continuous_id).continuousOn)
    fun v hv => mem_Iio.mpr (by linarith [(mem_Icc_third_of_abs_eq_one hs hv).2])

private theorem hasDerivAt_diagCoord {s v : ℝ} (hs : |s| = 1) (hv : v ∈ Ioo (0 : ℝ) (1 / 3)) :
    HasDerivAt (diagCoord s) (v / ((1 - s * v) * diagCoord s v)) v := by
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hsv_mem := mem_Icc_third_of_abs_eq_one hs ⟨hv.1.le, hv.2.le⟩
  have hu_pos : 0 < diagCoord s v := diagCoord_pos hs ⟨hv.1, hv.2.le⟩
  have hpsi_pos : 0 < 2 * diagPhase (s * v) := Real.sqrt_pos.mp hu_pos
  have hd_inner : HasDerivAt (fun w => 2 * diagPhase (s * w))
      (2 * ((s * v / (1 - s * v)) * (s * 1))) v :=
    ((hasDerivAt_diagPhase (x := s * v) (by linarith [hsv_mem.2])).comp v
      ((hasDerivAt_id v).const_mul s)).const_mul 2
  refine (HasDerivAt.sqrt hd_inner hpsi_pos.ne').congr_deriv ?_
  unfold diagCoord
  have h1 : 1 - s * v ≠ 0 := by linarith [hsv_mem.2]
  have h2 : Real.sqrt (2 * diagPhase (s * v)) ≠ 0 := hu_pos.ne'
  field_simp; linear_combination v * hs2

private theorem integral_comp_diagCoord {s : ℝ} (hs : |s| = 1) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ v in (0 : ℝ)..(1 / 3),
      (g ∘ diagCoord s) v * (v / ((1 - s * v) * diagCoord s v))) =
      ∫ u in (0 : ℝ)..diagCoord s (1 / 3), g u ∧
    IntervalIntegrable (fun v => (g ∘ diagCoord s) v * (v / ((1 - s * v) * diagCoord s v)))
      volume 0 (1 / 3) := by
  have hc0 : diagCoord s 0 = 0 := by simp [diagCoord, diagPhase_zero]
  have hderiv_nn : ∀ v ∈ Ioo (min (0 : ℝ) (1 / 3)) (max 0 (1 / 3)),
      0 ≤ v / ((1 - s * v) * diagCoord s v) := fun v hv => by
    have hv' : v ∈ Ioo (0 : ℝ) (1 / 3) := by simpa using hv
    have hsv := mem_Icc_third_of_abs_eq_one hs ⟨hv'.1.le, hv'.2.le⟩
    exact div_nonneg hv'.1.le (mul_nonneg (by linarith [hsv.2]) (Real.sqrt_nonneg _))
  refine ⟨?_, ?_⟩
  · conv_rhs => rw [← hc0]
    exact intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (continuousOn_diagCoord hs)
      (fun v hv => hasDerivAt_diagCoord hs (by simpa using hv)) hderiv_nn
  · exact (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (continuousOn_diagCoord hs) (fun v hv => hasDerivAt_diagCoord hs (by simpa using hv))
      hderiv_nn).mpr (hg.intervalIntegrable _ _)

private theorem norm_main_integrand_sub_le {a s v : ℝ} (hs : |s| = 1)
    (hv : v ∈ Ioc (0 : ℝ) (1 / 3)) :
    ‖(1 - s * v)⁻¹ * Real.exp (-a * diagPhase (s * v)) -
      ((fun u => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) ∘ diagCoord s) v *
        (v / ((1 - s * v) * diagCoord s v))‖ ≤
    ((fun u => 82 * u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) ∘ diagCoord s) v *
      (v / ((1 - s * v) * diagCoord s v)) := by
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hsv_mem := mem_Icc_third_of_abs_eq_one hs ⟨hv.1.le, hv.2⟩
  have hu_pos : 0 < diagCoord s v := diagCoord_pos hs hv
  have hu_sq : (diagCoord s v) ^ 2 = 2 * diagPhase (s * v) :=
    Real.sq_sqrt (Real.sqrt_pos.mp hu_pos).le
  have h1 : 0 < 1 - s * v := by linarith [hsv_mem.2]
  have hexp_eq : Real.exp (-(a / 2) * (diagCoord s v) ^ 2) =
      Real.exp (-a * diagPhase (s * v)) := by rw [hu_sq]; congr 1; ring
  have hs0 : s ≠ 0 := abs_pos.mp (by linarith)
  have hid : (1 - s * v)⁻¹ = ((s * diagCoord s v) / (s * v)) *
      (v / ((1 - s * v) * diagCoord s v)) := by
    have hv0 : v ≠ 0 := hv.1.ne'; field_simp [h1.ne', hu_pos.ne']
  have hqb := abs_div_sub_diagQ_le (x := s * v) (u := s * diagCoord s v) hsv_mem
    (mul_ne_zero hs0 hv.1.ne') (by rw [mul_pow, hs2, one_mul, hu_sq])
    (by rw [show (s * v) * (s * diagCoord s v) = s ^ 2 * (v * diagCoord s v) by ring, hs2, one_mul];
        exact mul_pos hv.1 hu_pos)
  rw [show |s * diagCoord s v| = diagCoord s v by
    rw [abs_mul, hs, one_mul, abs_of_pos hu_pos] ] at hqb
  have hw_nn :
      0 ≤ Real.exp (-a * diagPhase (s * v)) * (v / ((1 - s * v) * diagCoord s v)) :=
    mul_nonneg (Real.exp_pos _).le (div_nonneg hv.1.le (mul_nonneg h1.le hu_pos.le))
  dsimp only [Function.comp_apply]
  rw [hexp_eq, hid, Real.norm_eq_abs,
    show (s * diagCoord s v) / (s * v) * (v / ((1 - s * v) * diagCoord s v)) *
        Real.exp (-a * diagPhase (s * v)) -
      diagQ (s * diagCoord s v) * Real.exp (-a * diagPhase (s * v)) *
        (v / ((1 - s * v) * diagCoord s v)) =
      ((s * diagCoord s v) / (s * v) - diagQ (s * diagCoord s v)) *
        (Real.exp (-a * diagPhase (s * v)) * (v / ((1 - s * v) * diagCoord s v))) by ring,
    abs_mul, abs_of_nonneg hw_nn]
  calc |(s * diagCoord s v) / (s * v) - diagQ (s * diagCoord s v)| * _
      ≤ (82 * (diagCoord s v) ^ 9) * _ := mul_le_mul_of_nonneg_right hqb hw_nn
    _ = _ := by ring

private theorem isBigO_main_interval_err {s : ℝ} (hs : |s| = 1) :
    (fun a : ℝ => a * ((∫ v in (0 : ℝ)..(1 / 3),
        (1 - s * v)⁻¹ * Real.exp (-a * diagPhase (s * v))) -
      ∫ u in (0 : ℝ)..diagCoord s (1 / 3), diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  refine IsBigO.of_bound (82 * 384) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hQ_sub := integral_comp_diagCoord hs
    (g := fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) (by unfold diagQ; fun_prop)
  have h9_sub := integral_comp_diagCoord hs
    (g := fun u : ℝ => 82 * u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) (by fun_prop)
  have hcont_lhs : IntervalIntegrable
      (fun v => (1 - s * v)⁻¹ * Real.exp (-a * diagPhase (s * v))) volume 0 (1 / 3) := by
    refine ContinuousOn.intervalIntegrable ?_; rw [uIcc_of_le (by norm_num)]
    exact (ContinuousOn.inv₀ (by fun_prop) fun v hv =>
        (sub_pos.mpr (by linarith [(mem_Icc_third_of_abs_eq_one hs hv).2])).ne').mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
        (continuousOn_diagPhase.comp (by fun_prop) fun v hv =>
          mem_Iio.mpr (by linarith [(mem_Icc_third_of_abs_eq_one hs hv).2]))))
  rw [← hQ_sub.1, ← intervalIntegral.integral_sub hcont_lhs hQ_sub.2]
  have hle1 := intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun v hv => norm_main_integrand_sub_le hs hv) h9_sub.2
  rw [h9_sub.1, intervalIntegral.integral_of_le (diagCoord_pos hs ⟨by norm_num, le_rfl⟩).le] at hle1
  have hle2 : (∫ u in Ioc 0 (diagCoord s (1 / 3)), 82 * u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) ≤
      82 * ∫ u in Ioi (0 : ℝ), u ^ 9 * Real.exp (-(a / 2) * u ^ 2) := by
    have hint9 : IntegrableOn (fun u : ℝ => u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) (Ioi 0) :=
      (integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff 9).mpr (half_pos ha)
    simp_rw [mul_assoc]; rw [← integral_const_mul]
    exact setIntegral_mono_set (hint9.const_mul 82)
      ((ae_restrict_mem measurableSet_Ioi).mono fun u hu => by have : 0 < u := hu; positivity)
      (Eventually.of_forall fun _ hu => hu.1)
  have hmom9 : a * ∫ u in Ioi (0 : ℝ), u ^ 9 * Real.exp (-(a / 2) * u ^ 2) =
      384 * a ^ (-4 : ℝ) := by
    have h4 : a ^ (-4 : ℝ) = (a ^ 4)⁻¹ := by
      have hneg : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num
      rw [hneg, Real.rpow_neg ha.le, Real.rpow_natCast]
    rw [integral_Ioi_pow_two_mul_add_one_mul_exp_neg_mul_sq (half_pos ha) 4, h4]
    norm_num [Nat.factorial]; field_simp [ha.ne']; ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ha, ← Real.norm_eq_abs]
  calc a * ‖_‖ ≤ a * (82 * ∫ u in Ioi (0 : ℝ), u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left (hle1.trans hle2) ha.le
    _ = 82 * 384 * ‖a ^ (-4 : ℝ)‖ := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg ha.le _)]; linear_combination 82 * hmom9

private theorem isBigO_main_interval {s : ℝ} (hs : |s| = 1) :
    (fun a : ℝ => a * (∫ v in (0 : ℝ)..(1 / 3),
        (1 - s * v)⁻¹ * Real.exp (-a * diagPhase (s * v))) -
      (diagSeries8 s a - 571 * Real.sqrt (2 * Real.pi) / 4976640 * a ^ (-7 / 2 : ℝ)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hc_pos : 0 < diagCoord s (1 / 3) := diagCoord_pos hs ⟨by norm_num, le_rfl⟩
  refine ((isBigO_main_interval_err hs).sub (isBigO_gauss_tail hc_pos hs)).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_diagQ_mul_exp ha s) hc_pos.le
  rw [← hsplit]
  linear_combination -(integral_diagQ_mul_exp_eq ha hs)

/-! ### Lower and upper integral decomposition at `t = a` -/

private theorem rpow_exp_cancel {a : ℝ} (ha : 0 < a) :
    a ^ (1 - a) * Real.exp a * (a ^ a * Real.exp (-a)) = a ∧
    a ^ (a - 1) * Real.exp (-a) * (a ^ (1 - a) * Real.exp a) = 1 ∧
    a * a ^ (a - 1) = a ^ a := by
  have ha1 : a ^ (1 - a) * a ^ a = a := by
    rw [← Real.rpow_add ha, show 1 - a + a = 1 by ring, Real.rpow_one]
  have ha0 : a ^ (a - 1) * a ^ (1 - a) = 1 := by
    rw [← Real.rpow_add ha, show a - 1 + (1 - a) = 0 by ring, Real.rpow_zero]
  have haa : a * a ^ (a - 1) = a ^ a := by
    conv_lhs => arg 1; rw [← Real.rpow_one a]
    rw [← Real.rpow_add ha]; congr 1; ring
  have he1 : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact ⟨by linear_combination Real.exp a * Real.exp (-a) * ha1 + a * he1,
    by linear_combination Real.exp a * Real.exp (-a) * ha0 + he1, haa⟩

private theorem lower_scaled_integral {a : ℝ} (ha : 2 ≤ a) :
    a ^ (1 - a) * Real.exp a * lowerIncompleteGamma a a =
      a * (∫ v in (0 : ℝ)..(1 / 3), (1 - v)⁻¹ * Real.exp (-a * diagPhase v)) +
        a * ∫ v in (1 / 3 : ℝ)..1, (1 - v) ^ (a - 1) * Real.exp (a * v) := by
  have ha0 : 0 < a := by linarith
  rw [lowerIncompleteGamma_eq_integral ha0.le]
  have hmul := intervalIntegral.integral_comp_mul_left
    (fun t => t ^ (a - 1) * Real.exp (-t)) ha0.ne' (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hmul
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun s => (a * s) ^ (a - 1) * Real.exp (-(a * s))) 1 (a := 0) (b := 1)
  simp only [sub_zero, sub_self] at hsub
  have hint_eq : (∫ t in (0 : ℝ)..a, t ^ (a - 1) * Real.exp (-t)) =
      a ^ a * Real.exp (-a) * ∫ v in (0 : ℝ)..1, (1 - v) ^ (a - 1) * Real.exp (a * v) := by
    rw [show (∫ t in (0 : ℝ)..a, t ^ (a - 1) * Real.exp (-t)) =
        a * ∫ s in (0 : ℝ)..1, (a * s) ^ (a - 1) * Real.exp (-(a * s)) by
      rw [hmul, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul],
      ← hsub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le zero_le_one] at hv
    rw [Real.mul_rpow ha0.le (sub_nonneg.mpr hv.2),
      show -(a * (1 - v)) = -a + a * v by ring, Real.exp_add]
    linear_combination Real.exp (-a) * ((1 - v) ^ (a - 1) * Real.exp (a * v)) *
      (rpow_exp_cancel ha0).2.2
  have hcont : Continuous fun v : ℝ => (1 - v) ^ (a - 1) * Real.exp (a * v) :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ a - 1)).comp
      (continuous_const.sub continuous_id)).mul (Real.continuous_exp.comp (by fun_prop))
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 (1 / 3))
    (hcont.intervalIntegrable (μ := volume) (1 / 3) 1)
  have hmain : (∫ v in (0 : ℝ)..(1 / 3), (1 - v) ^ (a - 1) * Real.exp (a * v)) =
      ∫ v in (0 : ℝ)..(1 / 3), (1 - v)⁻¹ * Real.exp (-a * diagPhase v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (by norm_num)] at hv
    have h1 : 0 < 1 - v := by linarith [hv.2]
    rw [Real.rpow_def_of_pos h1, ← Real.exp_add,
      show Real.log (1 - v) * (a - 1) + a * v = -Real.log (1 - v) + (-a * diagPhase v) by
        unfold diagPhase; ring,
      Real.exp_add, Real.exp_neg, Real.exp_log h1]
  rw [hint_eq, ← mul_assoc, (rpow_exp_cancel ha0).1, ← hadj, hmain, mul_add]

private theorem isBigO_lower_tail :
    (fun a : ℝ => a * ∫ v in (1 / 3 : ℝ)..1, (1 - v) ^ (a - 1) * Real.exp (a * v))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hbound : (fun a : ℝ => ∫ v in (1 / 3 : ℝ)..1, (1 - v) ^ (a - 1) * Real.exp (a * v))
      =O[atTop] fun a : ℝ => Real.exp (-(1 / 48) * a) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (50 : ℝ)] with a ha
    have hpt : ∀ v ∈ Ι (1 / 3 : ℝ) 1,
        ‖(1 - v) ^ (a - 1) * Real.exp (a * v)‖ ≤ Real.exp (-(1 / 48) * a) := fun v hv => by
      rw [uIoc_of_le (by norm_num)] at hv
      rcases eq_or_lt_of_le hv.2 with rfl | hv1
      · rw [sub_self, Real.zero_rpow (by linarith : a - 1 ≠ 0), zero_mul, norm_zero]
        exact (Real.exp_pos _).le
      · have h1 : 0 < 1 - v := sub_pos.mpr hv1
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg h1.le _) (Real.exp_pos _).le),
          Real.rpow_def_of_pos h1, ← Real.exp_add]
        have hpsi := diagPhase_lower_tail hv.1.le hv1
        unfold diagPhase at hpsi
        exact Real.exp_le_exp.mpr (by nlinarith [hv.2])
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    calc ‖∫ v in (1 / 3 : ℝ)..1, (1 - v) ^ (a - 1) * Real.exp (a * v)‖
        ≤ Real.exp (-(1 / 48) * a) * |(1 : ℝ) - 1 / 3| := hle
      _ ≤ Real.exp (-(1 / 48) * a) := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 - 1 / 3)]
          linarith [Real.exp_pos (-(1 / 48) * a)]
  exact ((isBigO_refl (fun a : ℝ => a) atTop).congr_right fun a => (Real.rpow_one a).symm)
    |>.mul_atTop_rpow_of_isBigO_rpow 1 (-5) (-4)
      (hbound.trans (isLittleO_exp_neg_mul_rpow_atTop (by norm_num) (-5)).isBigO) (by norm_num)

private theorem upper_integrand_eq {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (a * s) ^ (a - 1) * Real.exp (-(a * s)) =
      a ^ (a - 1) * Real.exp (-a) * (s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) := by
  rw [Real.mul_rpow ha.le hs.le, Real.rpow_def_of_pos hs, mul_assoc (a ^ (a - 1)), ← Real.exp_add,
    show Real.log s * (a - 1) + -(a * s) = -Real.log s + (-a + (-a * diagPhase (-(s - 1)))) by
      unfold diagPhase; simp [sub_eq_add_neg]; ring,
    Real.exp_add, Real.exp_add, Real.exp_neg s.log, Real.exp_log hs]
  ring

private theorem integrableOn_upper_scaled {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) (Ioi 1) := by
  have hint_G : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioi 0) :=
    (Real.GammaIntegral_convergent ha).congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  have h2 : IntegrableOn (fun s : ℝ => (a * s) ^ (a - 1) * Real.exp (-(a * s))) (Ioi 1) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun t => t ^ (a - 1) * Real.exp (-t)) 1 ha).mpr
      (by simpa using hint_G.mono_set (Ioi_subset_Ioi ha.le))
  have h3 : IntegrableOn
      (fun s : ℝ => a ^ (1 - a) * Real.exp a * ((a * s) ^ (a - 1) * Real.exp (-(a * s))))
      (Ioi 1) := h2.const_mul _
  refine h3.congr_fun (fun s hs => ?_) measurableSet_Ioi
  dsimp only
  rw [upper_integrand_eq ha (lt_trans zero_lt_one hs)]
  linear_combination (s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) * (rpow_exp_cancel ha).2.1

private theorem upper_scaled_integral {a : ℝ} (ha : 2 ≤ a) :
    a ^ (1 - a) * Real.exp a * (Real.Gamma a - lowerIncompleteGamma a a) =
      a * (∫ v in (0 : ℝ)..(1 / 3), (1 + v)⁻¹ * Real.exp (-a * diagPhase (-v))) +
        a * ∫ s in Ioi (4 / 3 : ℝ), s⁻¹ * Real.exp (-a * diagPhase (-(s - 1))) := by
  have ha0 : 0 < a := by linarith
  have hint_G : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioi 0) :=
    (Real.GammaIntegral_convergent ha0).congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hGamma : Real.Gamma a - lowerIncompleteGamma a a =
      ∫ t in Ioi a, t ^ (a - 1) * Real.exp (-t) := by
    rw [Real.Gamma_eq_integral ha0,
      setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _,
      lowerIncompleteGamma_eq_integral ha0.le,
      ← intervalIntegral.integral_Ioi_sub_Ioi hint_G ha0.le]; ring
  have hscale : (∫ t in Ioi a, t ^ (a - 1) * Real.exp (-t)) =
      a ^ a * Real.exp (-a) * ∫ s in Ioi (1 : ℝ), s⁻¹ * Real.exp (-a * diagPhase (-(s - 1))) := by
    have hm := integral_comp_mul_left_Ioi' (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) 1 ha0
    simp only [mul_one, smul_eq_mul] at hm
    rw [← hm, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [upper_integrand_eq ha0 (lt_trans zero_lt_one hs)]
    linear_combination Real.exp (-a) * (s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) *
      (rpow_exp_cancel ha0).2.2
  have hint_s := integrableOn_upper_scaled ha0
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint_s
    (hint_s.mono_set (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 4 / 3)))
  have hshift : (∫ s in (1 : ℝ)..(4 / 3), s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) =
      ∫ v in (0 : ℝ)..(1 / 3), (1 + v)⁻¹ * Real.exp (-a * diagPhase (-v)) := by
    have := intervalIntegral.integral_comp_add_right
      (fun s => s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) 1 (a := 0) (b := 1 / 3)
    rw [show (0 : ℝ) + 1 = 1 by ring, show (1 / 3 : ℝ) + 1 = 4 / 3 by ring] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun v _ => by rw [add_sub_cancel_right, add_comm v 1]
  rw [hGamma, hscale, ← mul_assoc, (rpow_exp_cancel ha0).1, ← hsplit, hshift, mul_add]

private theorem isBigO_upper_tail :
    (fun a : ℝ => a * ∫ s in Ioi (4 / 3 : ℝ), s⁻¹ * Real.exp (-a * diagPhase (-(s - 1))))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hdom : IntegrableOn (fun s : ℝ => Real.exp (4 / 3 : ℝ) * Real.exp (-1 * s)) (Ioi (4 / 3)) :=
    (exp_neg_integrableOn_Ioi (4 / 3) one_pos).const_mul _
  have hbound : (fun a : ℝ => ∫ s in Ioi (4 / 3 : ℝ), s⁻¹ * Real.exp (-a * diagPhase (-(s - 1))))
      =O[atTop] fun a : ℝ => Real.exp (-(1 / 24) * a) := by
    refine IsBigO.of_bound |∫ s in Ioi (4 / 3 : ℝ), Real.exp (4 / 3 : ℝ) * Real.exp (-1 * s)| ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with a ha
    have hpt : ∀ᵐ s ∂(volume.restrict (Ioi (4 / 3 : ℝ))),
        ‖s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))‖ ≤
          Real.exp (-(1 / 24) * a) * (Real.exp (4 / 3 : ℝ) * Real.exp (-1 * s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs4 : 4 / 3 < s := hs
      have hpsi := diagPhase_upper_tail (v := s - 1) (by linarith)
      have hs_inv : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hexp_le : Real.exp (-a * diagPhase (-(s - 1))) ≤
          Real.exp (-(1 / 24) * a) * (Real.exp (4 / 3 : ℝ) * Real.exp (-1 * s)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      rw [Real.norm_of_nonneg (by positivity)]
      exact (mul_le_of_le_one_left (Real.exp_pos _).le hs_inv).trans hexp_le
    have hint := norm_integral_le_of_norm_le (hdom.const_mul _) hpt
    rw [integral_const_mul] at hint
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hint.trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  exact ((isBigO_refl (fun a : ℝ => a) atTop).congr_right fun a => (Real.rpow_one a).symm)
    |>.mul_atTop_rpow_of_isBigO_rpow 1 (-5) (-4)
      (hbound.trans (isLittleO_exp_neg_mul_rpow_atTop (by norm_num) (-5)).isBigO) (by norm_num)

private theorem isBigO_lower_sharp :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * lowerIncompleteGamma a a -
      (diagSeries8 1 a - 571 * Real.sqrt (2 * Real.pi) / 4976640 * a ^ (-7 / 2 : ℝ)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hm := isBigO_main_interval (s := 1) (by norm_num)
  refine (hm.add isBigO_lower_tail).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
  have hsc := lower_scaled_integral ha
  simp only [one_mul]; linarith

private theorem isBigO_upper_sharp :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * (Real.Gamma a - lowerIncompleteGamma a a) -
      (diagSeries8 (-1) a - 571 * Real.sqrt (2 * Real.pi) / 4976640 * a ^ (-7 / 2 : ℝ)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hm := isBigO_main_interval (s := -1) (by norm_num)
  refine (hm.add isBigO_upper_tail).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
  have hsc := upper_scaled_integral ha
  have hmain_eq : (∫ v in (0 : ℝ)..(1 / 3), (1 - -1 * v)⁻¹ * Real.exp (-a * diagPhase (-1 * v))) =
      ∫ v in (0 : ℝ)..(1 / 3), (1 + v)⁻¹ * Real.exp (-a * diagPhase (-v)) :=
    intervalIntegral.integral_congr fun v _ => by simp [sub_neg_eq_add]
  rw [hmain_eq]; linarith

/-! ### Diagonal incomplete Gamma expansions -/

/-- Eight-term normalized diagonal asymptotic expansion of `TauCeti.lowerIncompleteGamma a a` as
`a → +∞`. -/
theorem isBigO_mul_lowerIncompleteGamma_diag_sub :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * lowerIncompleteGamma a a -
      (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + 1 / 3 +
        Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + 4 / (135 * a) +
        Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - 8 / (2835 * a ^ 2) -
        139 * Real.sqrt (2 * Real.pi) / 103680 * a ^ (-5 / 2 : ℝ) - 16 / (8505 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-7 / 2 : ℝ) := by
  have h1 := (isBigO_lower_sharp.mul_atTop_rpow_of_isBigO_rpow (-4) 0 (-7 / 2)
    ((isBigO_refl (fun _ : ℝ => (1 : ℝ)) atTop).congr_right fun _ => (Real.rpow_zero _).symm)
    (by norm_num)).congr_left fun _ => mul_one _
  have h2 := (isBigO_refl (fun a : ℝ => a ^ (-7 / 2 : ℝ)) atTop).const_mul_left
    (571 * Real.sqrt (2 * Real.pi) / 4976640)
  exact (h1.sub h2).congr' (Eventually.of_forall fun a => by unfold diagSeries8; ring) .rfl

/-- Eight-term normalized diagonal asymptotic expansion of the upper incomplete Gamma tail
`Real.Gamma a - TauCeti.lowerIncompleteGamma a a` as `a → +∞` (DLMF 8.11.12 to `O(a^{-7/2})`). -/
theorem isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * (Real.Gamma a - lowerIncompleteGamma a a) -
      (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) - 1 / 3 +
        Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) - 4 / (135 * a) +
        Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) + 8 / (2835 * a ^ 2) -
        139 * Real.sqrt (2 * Real.pi) / 103680 * a ^ (-5 / 2 : ℝ) + 16 / (8505 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-7 / 2 : ℝ) := by
  have h1 := (isBigO_upper_sharp.mul_atTop_rpow_of_isBigO_rpow (-4) 0 (-7 / 2)
    ((isBigO_refl (fun _ : ℝ => (1 : ℝ)) atTop).congr_right fun _ => (Real.rpow_zero _).symm)
    (by norm_num)).congr_left fun _ => mul_one _
  have h2 := (isBigO_refl (fun a : ℝ => a ^ (-7 / 2 : ℝ)) atTop).const_mul_left
    (571 * Real.sqrt (2 * Real.pi) / 4976640)
  exact (h1.sub h2).congr' (Eventually.of_forall fun a => by unfold diagSeries8; ring) .rfl

private theorem isBigO_unnormalized_six {f : ℝ → ℝ} (s : ℝ)
    (hf : (fun a : ℝ => a ^ (1 - a) * Real.exp a * f a - diagSeries8 s a)
      =O[atTop] fun a : ℝ => a ^ (-7 / 2 : ℝ)) :
    (fun a : ℝ => f a - a ^ (a - 1) * Real.exp (-a) *
      (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + s * (1 / 3) +
        Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + s * (4 / (135 * a)) +
        Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - s * (8 / (2835 * a ^ 2))))
      =O[atTop] fun a : ℝ => a ^ (a - 7 / 2) * Real.exp (-a) := by
  have h1 : (fun _ : ℝ => (1 : ℝ)) =O[atTop] fun a : ℝ => a ^ (0 : ℝ) :=
    (isBigO_refl (fun _ : ℝ => (1 : ℝ)) atTop).congr_right fun _ => (Real.rpow_zero _).symm
  have h8 := (hf.mul_atTop_rpow_of_isBigO_rpow (-7 / 2) 0 (-5 / 2) h1 (by norm_num)).congr_left
    fun _ => mul_one _
  have h6 := (isBigO_refl (fun a : ℝ => a ^ (-5 / 2 : ℝ)) atTop).const_mul_left
    (-139 * Real.sqrt (2 * Real.pi) / 103680)
  have h7 : (fun a : ℝ => -(s * 16 / 8505) / a ^ 3) =O[atTop] fun a : ℝ => a ^ (-5 / 2 : ℝ) := by
    refine (((isBigO_refl (fun a : ℝ => a ^ (-3 : ℝ)) atTop).mul_atTop_rpow_of_isBigO_rpow
      (-3) 0 (-5 / 2) h1 (by norm_num)).const_mul_left (-(s * 16 / 8505))).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [Pi.mul_apply, mul_one, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le,
      Real.rpow_natCast]
    ring
  refine ((isBigO_refl (fun a : ℝ => a ^ (a - 1) * Real.exp (-a)) atTop).mul
    ((h8.add h6).add h7)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have hc := (rpow_exp_cancel ha).2.1
    unfold diagSeries8; linear_combination f a * hc
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [mul_right_comm, ← Real.rpow_add ha]; congr 2; ring

/-- **DLMF 8.11.12** on `(0, ∞)`: six-term diagonal asymptotic expansion of the upper incomplete
Gamma tail `Γ(a, a) = Real.Gamma a - TauCeti.lowerIncompleteGamma a a` as `a → +∞`. -/
theorem isBigO_Gamma_sub_lowerIncompleteGamma_diag :
    (fun a : ℝ => (Real.Gamma a - lowerIncompleteGamma a a) -
      a ^ (a - 1) * Real.exp (-a) *
        (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) - 1 / 3 +
          Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) - 4 / (135 * a) +
          Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) + 8 / (2835 * a ^ 2)))
      =O[atTop] fun a : ℝ => a ^ (a - 7 / 2) * Real.exp (-a) :=
  (isBigO_unnormalized_six (f := fun a => Real.Gamma a - lowerIncompleteGamma a a) (-1)
    (isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub.congr_left fun a => by
      unfold diagSeries8; ring)).congr_left fun a => by ring

/-- Six-term diagonal asymptotic expansion of `TauCeti.lowerIncompleteGamma a a` as `a → +∞`
(the lower-tail companion to `TauCeti.isBigO_Gamma_sub_lowerIncompleteGamma_diag`). -/
theorem isBigO_lowerIncompleteGamma_diag :
    (fun a : ℝ => lowerIncompleteGamma a a -
      a ^ (a - 1) * Real.exp (-a) *
        (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + 1 / 3 +
          Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + 4 / (135 * a) +
          Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - 8 / (2835 * a ^ 2)))
      =O[atTop] fun a : ℝ => a ^ (a - 7 / 2) * Real.exp (-a) :=
  (isBigO_unnormalized_six (f := fun a => lowerIncompleteGamma a a) 1
    (isBigO_mul_lowerIncompleteGamma_diag_sub.congr_left fun a => by
      unfold diagSeries8; ring)).congr_left fun a => by ring

/-- All even-order Gaussian moments cancel in `γ(a, a) - Γ(a) / 2`, yielding a pure integer-power
expansion to `O(a^{-4})`. -/
theorem isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * (lowerIncompleteGamma a a - Real.Gamma a / 2) -
      (1 / 3 + 4 / (135 * a) - 8 / (2835 * a ^ 2) - 16 / (8505 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
  ((isBigO_lower_sharp.sub isBigO_upper_sharp).const_mul_left (1 / 2 : ℝ)).congr'
    (Eventually.of_forall fun a => by unfold diagSeries8; ring) .rfl

end TauCeti

end
