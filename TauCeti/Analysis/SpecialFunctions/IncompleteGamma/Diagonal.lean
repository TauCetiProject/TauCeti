/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Diagonal asymptotics of the incomplete Gamma functions and exponential partial sums

For large positive `a`, the Euler integral `Γ(a) = ∫₀^∞ t^{a - 1} e^{-t} dt` concentrates in a
window of width `O(√a)` around its saddle point `t = a`. Splitting the integral at `t = a` splits
`Γ(a)` into the lower incomplete Gamma function `γ(a, a)` and the upper tail `Γ(a) - γ(a, a)`.
After scaling `t = a (1 - x)`, both halves share the single convex phase
`ψ(x) = -x - log (1 - x)` (evaluated at `x = v ∈ (0, 1)` on the lower side and `x = -v ∈ (-∞, 0)`
on the upper side). Passing to the quadratic coordinate `u` with `u² / 2 = ψ(x)` turns the main
contribution of each half into a linear combination of Gaussian moments
`a ∫₀^∞ u^k e^{-a u² / 2} du`, with coefficients `q_k` on the lower side and `(-1)^k q_k` on the
upper side.

Two algebraic cancellations govern the consequences:

* Adding the two halves doubles the even-order moments and cancels every odd-order moment,
  recovering the four-term Stirling expansion of `Γ(a)`.
* Subtracting `Γ(a) / 2` from `γ(a, a)` cancels every even-order moment (all half-integer powers
  and `√(2π)` factors), leaving a pure series in integer powers of `a⁻¹`:
  `a^{1 - a} e^a (γ(a, a) - Γ(a) / 2) = 1/3 + 4/(135 a) - 8/(2835 a²) - 16/(8505 a³) + O(a^{-4})`.

Specializing to positive integers `a = n` via the Erlang formula `TauCeti.regularizedGamma_natCast`
identifies the left-hand side directly with Ramanujan's remainder `θ(n)` in
`∑_{k < n} n^k / k! + (n^n / n!) θ(n) = e^n / 2`, yielding Ramanujan's four-term asymptotic
expansion of `θ(n)` and the companion expansions of the central exponential partial sums
`e^{-n} ∑_{k ≤ n} n^k / k!` and `e^{-n} ∑_{k < n} n^k / k!`.

## Main definitions

* `TauCeti.ramanujanTheta`: Ramanujan's remainder function `θ(n)` determined for every `n : ℕ` by
  `∑_{k < n} n^k / k! + (n^n / n!) θ(n) = e^n / 2`.

## Main results

* `TauCeti.isBigO_Gamma_sub_lowerIncompleteGamma_diag` and
  `TauCeti.isBigO_lowerIncompleteGamma_diag`: six-term diagonal expansions of `Γ(a) - γ(a, a)`
  (DLMF 8.11.12) and `γ(a, a)`, from `TauCeti.isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub`
  and `TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub`.
* `TauCeti.isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma`: pure integer-power expansion of
  `a^{1 - a} e^a (γ(a, a) - Γ(a) / 2)` to `O(a^{-4})`.
* `TauCeti.isBigO_regularizedGamma_diag_sub` and `TauCeti.isBigO_regularizedGamma_add_one_diag_sub`:
  four-term expansions of `P(a, a)` and `P(a + 1, a)` to `O(a^{-9/2})`, with diagonal limits
  `TauCeti.tendsto_regularizedGamma_diag_atTop`, `TauCeti.tendsto_sub_regularizedGamma_diag_atTop`,
  and `TauCeti.tendsto_regularizedGamma_add_one_diag_atTop` (DLMF 8.11.13).
* `TauCeti.sum_range_add_ramanujanTheta`, `TauCeti.isBigO_ramanujanTheta_sub`,
  `TauCeti.isBigO_exp_neg_mul_sum_range_succ_sub`, and `TauCeti.isBigO_exp_neg_mul_sum_range_sub`:
  identities and four-term expansions for `θ(n)` and exponential sums (DLMF 8.11.14–8.11.17).

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(v)](https://dlmf.nist.gov/8.11.v),
  Eqs. 8.11.12–8.11.17.
* S. Ramanujan, *Question 294*, J. Indian Math. Soc. **3** (1911), 128; *Collected Papers of
  Srinivasa Ramanujan*, Cambridge Univ. Press (1927), 46–48 and 323–324.
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

private theorem diagPhase_nonneg {x : ℝ} (hx : x < 1) : 0 ≤ diagPhase x := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hx)
  unfold diagPhase; linarith

private theorem nonneg_of_hasDerivAt_mul_nonneg {f g : ℝ → ℝ} (hf0 : f 0 = 0)
    (hd : ∀ y ∈ Icc (-(1 / 3 : ℝ)) (1 / 3), HasDerivAt f (y * g y) y)
    (hg : ∀ y ∈ Icc (-(1 / 3 : ℝ)) (1 / 3), 0 ≤ g y)
    {x : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3)) : 0 ≤ f x := by
  rcases le_or_gt 0 x with hx0 | hx0
  · have hmono : MonotoneOn f (Icc 0 (1 / 3)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 3))
        (fun y hy => (hd y ⟨by linarith [hy.1], hy.2⟩).continuousAt.continuousWithinAt)
        (fun y hy => (hd y ⟨by linarith [(interior_subset hy).1], (interior_subset hy).2⟩)
          |>.differentiableAt.differentiableWithinAt) fun y hy => ?_
      rw [interior_Icc] at hy
      have hy' : y ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) := ⟨by linarith [hy.1], hy.2.le⟩
      rw [(hd y hy').deriv]
      exact mul_nonneg hy.1.le (hg y hy')
    simpa [hf0] using hmono (left_mem_Icc.mpr (by norm_num)) ⟨hx0, hx.2⟩ hx0
  · have hanti : AntitoneOn f (Icc (-(1 / 3 : ℝ)) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (-(1 / 3)) 0)
        (fun y hy => (hd y ⟨hy.1, by linarith [hy.2]⟩).continuousAt.continuousWithinAt)
        (fun y hy => (hd y ⟨(interior_subset hy).1, by linarith [(interior_subset hy).2]⟩)
          |>.differentiableAt.differentiableWithinAt) fun y hy => ?_
      rw [interior_Icc] at hy
      have hy' : y ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) := ⟨hy.1.le, by linarith [hy.2]⟩
      rw [(hd y hy').deriv]
      exact mul_nonpos_of_nonpos_of_nonneg hy.2.le (hg y hy')
    simpa [hf0] using hanti ⟨hx.1, hx0.le⟩ (right_mem_Icc.mpr (by norm_num)) hx0.le

private theorem diagPhase_lower_quad {x : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3)) :
    3 / 8 * x ^ 2 ≤ diagPhase x := by
  suffices 0 ≤ diagPhase x - 3 / 8 * x ^ 2 by linarith
  refine nonneg_of_hasDerivAt_mul_nonneg (f := fun z => diagPhase z - 3 / 8 * z ^ 2)
    (g := fun z => 1 / (1 - z) - 3 / 4) (by simp [diagPhase_zero])
    (fun y hy => ?_) (fun y hy => ?_) hx
  · have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    refine ((hasDerivAt_diagPhase (by linarith [hy.2])).sub
      ((hasDerivAt_pow 2 y).const_mul (3 / 8 : ℝ))).congr_deriv (by field_simp; ring)
  · exact sub_nonneg.mpr (by rw [le_div_iff₀ (by linarith [hy.2])]; linarith [hy.1])

private theorem diagPhase_upper_quad {x : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3)) :
    diagPhase x ≤ 3 / 4 * x ^ 2 := by
  suffices 0 ≤ 3 / 4 * x ^ 2 - diagPhase x by linarith
  refine nonneg_of_hasDerivAt_mul_nonneg (f := fun z => 3 / 4 * z ^ 2 - diagPhase z)
    (g := fun z => 3 / 2 - 1 / (1 - z)) (by simp [diagPhase_zero])
    (fun y hy => ?_) (fun y hy => ?_) hx
  · have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    refine (((hasDerivAt_pow 2 y).const_mul (3 / 4 : ℝ)).sub
      (hasDerivAt_diagPhase (by linarith [hy.2]))).congr_deriv (by field_simp; ring)
  · exact sub_nonneg.mpr (by rw [div_le_iff₀ (by linarith [hy.2])]; linarith [hy.2])

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
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 3 * r)]
    linarith

private theorem abs_sub_diagU_le {x u : ℝ} (hx : x ∈ Icc (-(1 / 3 : ℝ)) (1 / 3))
    (hx0 : x ≠ 0) (hu_sq : u ^ 2 = 2 * diagPhase x) (hxu : 0 < x * u) :
    |x - diagU u| ≤ 20 * |u| ^ 10 := by
  have hupp : u ^ 2 ≤ 3 / 2 * x ^ 2 := by linarith [diagPhase_upper_quad hx]
  have hu_pos : 0 < |u| := abs_pos.mpr fun hu0 => hx0
    (by nlinarith [diagPhase_lower_quad hx, sq_nonneg x])
  have hu_half : |u| ≤ 1 / 2 :=
    abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [hx.1, hx.2] : u ^ 2 ≤ (1 / 2) ^ 2) (by norm_num))
  have hx_lower : |u| / 2 ≤ |x| := by
    have : (|u| / 2) ^ 2 ≤ |x| ^ 2 := by rw [sq_abs]; nlinarith [sq_abs u]
    nlinarith [abs_nonneg u, abs_nonneg x]
  have hU_bds := diagU_bounds hu_half
  have hU_sign : 0 < u * diagU u := by
    have : |u * (diagU u - u)| ≤ 1 / 5 * u ^ 2 := by
      rw [abs_mul, ← sq_abs]; nlinarith [abs_diagU_sub_le hu_half, abs_nonneg u]
    nlinarith [abs_le.mp this, sq_pos_of_pos hu_pos]
  have hxU_sign : 0 < x * diagU u := by
    have : 0 < (x * u) * (u * diagU u) := mul_pos hxu hU_sign
    nlinarith [sq_pos_of_pos hu_pos, show (x * u) * (u * diagU u) = u ^ 2 * (x * diagU u) by ring]
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
  have hxU := abs_sub_diagU_le hx hx0 hu_sq hxu
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

private theorem integrableOn_pow_mul_exp_half_sq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-(a / 2) * u ^ 2)) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_sq (by positivity : 0 < a / 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) k] : (-1 : ℝ) < k)).congr_fun
    (fun u _ => by dsimp only; rw [Real.rpow_natCast]) measurableSet_Ioi

private theorem gaussMoment_eq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (a * ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(a / 2) * u ^ 2)) =
      2 ^ (((k : ℝ) - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2) *
        a ^ ((1 - (k : ℝ)) / 2) := by
  have hint : ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(a / 2) * u ^ 2) =
      ∫ u in Ioi (0 : ℝ), u ^ (k : ℝ) * Real.exp (-(a / 2) * u ^ (2 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ => by rw [Real.rpow_natCast, Real.rpow_two]
  rw [hint, integral_rpow_mul_exp_neg_mul_rpow two_pos
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)]
  have hdiv : (a / 2) ^ (-((k : ℝ) + 1) / 2) =
      a ^ (-((k : ℝ) + 1) / 2) * 2 ^ (((k : ℝ) + 1) / 2) := by
    rw [div_eq_mul_inv, Real.mul_rpow ha.le (by positivity), ← Real.rpow_neg_one 2,
      ← Real.rpow_mul zero_le_two]
    congr 2; ring
  have ha_pow : a * a ^ (-((k : ℝ) + 1) / 2) = a ^ ((1 - (k : ℝ)) / 2) :=
    calc a * a ^ (-((k : ℝ) + 1) / 2)
        = a ^ (1 : ℝ) * a ^ (-((k : ℝ) + 1) / 2) := by rw [Real.rpow_one]
      _ = a ^ ((1 - (k : ℝ)) / 2) := by rw [← Real.rpow_add ha]; congr 1; ring
  have h2_pow : (2 : ℝ) ^ (((k : ℝ) + 1) / 2) * (1 / 2) = 2 ^ (((k : ℝ) - 1) / 2) := by
    rw [one_div, ← Real.rpow_neg_one 2, ← Real.rpow_add two_pos]; congr 1; ring
  calc a * ((a / 2) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2))
      = (2 ^ (((k : ℝ) + 1) / 2) * (1 / 2)) * Real.Gamma (((k : ℝ) + 1) / 2) *
          (a * a ^ (-((k : ℝ) + 1) / 2)) := by rw [hdiv]; ring
    _ = 2 ^ (((k : ℝ) - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2) *
          a ^ ((1 - (k : ℝ)) / 2) := by rw [h2_pow, ha_pow]

private theorem gaussMoment_odd {a : ℝ} (ha : 0 < a) (m : ℕ) :
    (a * ∫ u in Ioi (0 : ℝ), u ^ (2 * m + 1) * Real.exp (-(a / 2) * u ^ 2)) =
      2 ^ m * (m ! : ℝ) / a ^ m := by
  rw [gaussMoment_eq ha (2 * m + 1)]
  push_cast
  rw [show (2 * (m : ℝ) + 1 - 1) / 2 = (m : ℝ) by ring,
    show (2 * (m : ℝ) + 1 + 1) / 2 = (m : ℝ) + 1 by ring,
    show (1 - (2 * (m : ℝ) + 1)) / 2 = -(m : ℝ) by ring,
    Real.rpow_natCast, Real.Gamma_nat_eq_factorial, Real.rpow_neg ha.le, Real.rpow_natCast,
    div_eq_mul_inv]

private theorem even_gaussMoment_coeffs :
    2 ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) = Real.sqrt (Real.pi / 2) ∧
    1 / 12 * (2 ^ (1 / 2 : ℝ) * Real.Gamma (3 / 2)) = Real.sqrt (2 * Real.pi) / 24 ∧
    1 / 864 * (2 ^ (3 / 2 : ℝ) * Real.Gamma (5 / 2)) = Real.sqrt (2 * Real.pi) / 576 ∧
    139 / 777600 * (2 ^ (5 / 2 : ℝ) * Real.Gamma (7 / 2)) =
      139 * Real.sqrt (2 * Real.pi) / 103680 := by
  have hG3 : Real.Gamma (3 / 2) = 1 / 2 * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
  have hG5 : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num), hG3]; ring
  have hG7 : Real.Gamma (7 / 2) = 15 / 8 * Real.sqrt Real.pi := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num), hG5]; ring
  have h2_half : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  have h2_neg : (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.rpow_neg zero_le_two, h2_half]
  have h2_3 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add two_pos, Real.rpow_one, h2_half]
  have h2_5 : (2 : ℝ) ^ (5 / 2 : ℝ) = 4 * Real.sqrt 2 := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by ring, Real.rpow_add two_pos,
      show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num, h2_half]
  have hmul : Real.sqrt 2 * Real.sqrt Real.pi = Real.sqrt (2 * Real.pi) :=
    (Real.sqrt_mul zero_le_two Real.pi).symm
  exact ⟨by rw [Real.Gamma_one_half_eq, h2_neg, Real.sqrt_div Real.pi_pos.le, inv_mul_eq_div],
    by rw [hG3, h2_half]; linear_combination 1 / 24 * hmul,
    by rw [hG5, h2_3]; linear_combination 1 / 576 * hmul,
    by rw [hG7, h2_5]; linear_combination 139 / 103680 * hmul⟩

/-- Eight-term asymptotic sum with sign `s = ±1` on odd moments (`s = 1` for `γ(a, a)`,
`s = -1` for `Γ(a) - γ(a, a)`). -/
private def diagSeries8 (s a : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + s * (1 / 3) +
    Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + s * (4 / (135 * a)) +
    Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - s * (8 / (2835 * a ^ 2)) -
    139 * Real.sqrt (2 * Real.pi) / 103680 * a ^ (-5 / 2 : ℝ) - s * (16 / (8505 * a ^ 3))

private theorem integrableOn_diagQ_mul_exp {a : ℝ} (ha : 0 < a) (s : ℝ) :
    IntegrableOn (fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) (Ioi 0) := by
  have h : (fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) =
      fun u => ∑ k ∈ Finset.range 9,
        (diagQCoeff k * s ^ k) * (u ^ k * Real.exp (-(a / 2) * u ^ 2)) := by
    ext u; rw [diagQ_mul_eq_sum, Finset.sum_mul]; simp only [mul_assoc]
  rw [h]
  exact integrable_finsetSum _ fun k _ => (integrableOn_pow_mul_exp_half_sq ha k).const_mul _

private theorem integral_diagQ_mul_exp_eq {a s : ℝ} (ha : 0 < a) (hs : |s| = 1) :
    (a * ∫ u in Ioi (0 : ℝ), diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) =
      diagSeries8 s a -
        571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2)) * a ^ (-7 / 2 : ℝ) := by
  have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have hs4 : s ^ 4 = 1 := by linear_combination (s ^ 2 + 1) * hs2
  have hs6 : s ^ 6 = 1 := by linear_combination (s ^ 4 + s ^ 2 + 1) * hs2
  have hs8 : s ^ 8 = 1 := by linear_combination (s ^ 6 + s ^ 4 + s ^ 2 + 1) * hs2
  have hs3 : s ^ 3 = s := by linear_combination s * hs2
  have hs5 : s ^ 5 = s := by linear_combination (s ^ 3 + s) * hs2
  have hs7 : s ^ 7 = s := by linear_combination (s ^ 5 + s ^ 3 + s) * hs2
  have hfun : (fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) =
      fun u => ∑ k ∈ Finset.range 9,
        (diagQCoeff k * s ^ k) * (u ^ k * Real.exp (-(a / 2) * u ^ 2)) := by
    ext u; rw [diagQ_mul_eq_sum, Finset.sum_mul]; simp only [mul_assoc]
  rw [hfun, integral_finsetSum _ fun k _ =>
    (integrableOn_pow_mul_exp_half_sq ha k).const_mul _, Finset.mul_sum]
  have hterm (k : ℕ) : a * (∫ u in Ioi (0 : ℝ),
      (diagQCoeff k * s ^ k) * (u ^ k * Real.exp (-(a / 2) * u ^ 2))) =
      (diagQCoeff k * s ^ k) * (a * ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-(a / 2) * u ^ 2)) := by
    rw [integral_const_mul]; ring
  simp_rw [hterm]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, diagQCoeff]
  rw [gaussMoment_eq ha 0, gaussMoment_odd ha (m := 0), gaussMoment_eq ha 2,
    gaussMoment_odd ha (m := 1), gaussMoment_eq ha 4, gaussMoment_odd ha (m := 2),
    gaussMoment_eq ha 6, gaussMoment_odd ha (m := 3), gaussMoment_eq ha 8]
  simp only [diagSeries8, pow_zero, pow_one, hs2, hs3, hs4, hs5, hs6, hs7, hs8, Nat.factorial]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_one, zero_add]
  obtain ⟨he0, he2, he4, he6⟩ := even_gaussMoment_coeffs
  linear_combination
    a ^ (1 / 2 : ℝ) * he0 + a ^ (-(1 / 2 : ℝ)) * he2 +
      a ^ (-(3 / 2 : ℝ)) * he4 - a ^ (-(5 / 2 : ℝ)) * he6

private theorem abs_diagQ_le_sum {u : ℝ} (hu : 0 ≤ u) (s : ℝ) (hs : |s| = 1) :
    |diagQ (s * u)| ≤ ∑ k ∈ Finset.range 9, u ^ k := by
  have hp (k : ℕ) : -(u ^ k) ≤ (s * u) ^ k ∧ (s * u) ^ k ≤ u ^ k :=
    abs_le.mp (by rw [abs_pow, abs_mul, hs, one_mul, abs_of_nonneg hu])
  unfold diagQ
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero]
  exact abs_le.mpr ⟨by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8],
    by linarith [hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8]⟩

private theorem isBigO_mul_self_rpow_neg_four_of_exp {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : f =O[atTop] fun a : ℝ => Real.exp (-c * a)) :
    (fun a : ℝ => a * f a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hrpow := hf.trans (isLittleO_exp_neg_mul_rpow_atTop hc (-5)).isBigO
  refine ((isBigO_refl (fun a : ℝ => a) atTop).mul hrpow).congr' .rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  calc a * a ^ (-5 : ℝ) = a ^ (1 : ℝ) * a ^ (-5 : ℝ) := by rw [Real.rpow_one]
    _ = a ^ (-4 : ℝ) := by rw [← Real.rpow_add ha]; norm_num

private theorem isBigO_gauss_tail {c s : ℝ} (hc : 0 < c) (hs : |s| = 1) :
    (fun a : ℝ => a * ∫ u in Ioi c, diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hdom : IntegrableOn (fun u : ℝ => (∑ k ∈ Finset.range 9, u ^ k) *
      Real.exp (-u ^ 2)) (Ioi c) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun k _ =>
      ((integrableOn_pow_mul_exp_half_sq two_pos k).mono_set (Ioi_subset_Ioi hc.le)).congr_fun
        (fun u _ => by dsimp only; congr 2; ring) measurableSet_Ioi
  refine isBigO_mul_self_rpow_neg_four_of_exp (c := c ^ 2 / 4) (by positivity) ?_
  refine IsBigO.of_bound (|∫ u in Ioi c, (∑ k ∈ Finset.range 9, u ^ k) * Real.exp (-u ^ 2)|) ?_
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
      have huc : a * ((u - c) * (u + c)) = a * u ^ 2 - a * c ^ 2 := by ring
      exact Real.exp_le_exp.mpr (by linarith [huc])
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

/-- Coordinate `u_-(v) = √(2 ψ(v))` for `v ∈ [0, 1/3]` and `u_+(v) = √(2 ψ(-v))` for `s = -1`. -/
private def diagCoord (s v : ℝ) : ℝ := Real.sqrt (2 * diagPhase (s * v))

private theorem mem_Icc_third_of_abs_eq_one {s v : ℝ} (hs : |s| = 1)
    (hv : v ∈ Icc (0 : ℝ) (1 / 3)) : s * v ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) :=
  abs_le.mp (by rw [abs_mul, hs, one_mul, abs_of_nonneg hv.1]; exact hv.2)

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
  have hpsi_pos : 0 < 2 * diagPhase (s * v) := by
    have hq := diagPhase_lower_quad hsv_mem
    have hsv_sq : (s * v) ^ 2 = v ^ 2 := by rw [mul_pow, hs2, one_mul]
    nlinarith [sq_pos_of_pos hv.1]
  have hd_inner : HasDerivAt (fun w => 2 * diagPhase (s * w))
      (2 * ((s * v / (1 - s * v)) * (s * 1))) v :=
    ((hasDerivAt_diagPhase (x := s * v) (by linarith [hsv_mem.2])).comp v
      ((hasDerivAt_id v).const_mul s)).const_mul 2
  refine (HasDerivAt.sqrt hd_inner hpsi_pos.ne').congr_deriv ?_
  unfold diagCoord
  have h1 : 1 - s * v ≠ 0 := by linarith [hsv_mem.2]
  have h2 : Real.sqrt (2 * diagPhase (s * v)) ≠ 0 := (Real.sqrt_pos.mpr hpsi_pos).ne'
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
  have hu_pos : 0 < diagCoord s v := by
    refine Real.sqrt_pos.mpr ?_
    have hq := diagPhase_lower_quad hsv_mem
    have : (s * v) ^ 2 = v ^ 2 := by rw [mul_pow, hs2, one_mul]
    nlinarith [sq_pos_of_pos hv.1]
  have hu_sq : (diagCoord s v) ^ 2 = 2 * diagPhase (s * v) :=
    Real.sq_sqrt (mul_nonneg zero_le_two (diagPhase_nonneg (by linarith [hsv_mem.2])))
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
  have hc_nn : 0 ≤ diagCoord s (1 / 3) := Real.sqrt_nonneg _
  refine IsBigO.of_bound (82 * (2 ^ 4 * (4 ! : ℝ))) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hQ_sub := integral_comp_diagCoord hs
    (g := fun u : ℝ => diagQ (s * u) * Real.exp (-(a / 2) * u ^ 2)) (by unfold diagQ; fun_prop)
  have h9_sub := integral_comp_diagCoord hs
    (g := fun u : ℝ => 82 * u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) (by fun_prop)
  have hcont_lhs : IntervalIntegrable
      (fun v => (1 - s * v)⁻¹ * Real.exp (-a * diagPhase (s * v))) volume 0 (1 / 3) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.mul (ContinuousOn.inv₀ (by fun_prop) fun v hv => ?_) ?_
    · exact (sub_pos.mpr (by linarith [(mem_Icc_third_of_abs_eq_one hs hv).2])).ne'
    · refine Real.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
      exact continuousOn_diagPhase.comp ((continuous_const.mul continuous_id).continuousOn)
        fun v hv => mem_Iio.mpr (by linarith [(mem_Icc_third_of_abs_eq_one hs hv).2])
  rw [← hQ_sub.1, ← intervalIntegral.integral_sub hcont_lhs hQ_sub.2]
  have hle1 := intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun v hv => norm_main_integrand_sub_le hs hv) h9_sub.2
  rw [h9_sub.1, intervalIntegral.integral_of_le hc_nn] at hle1
  have hle2 : (∫ u in Ioc 0 (diagCoord s (1 / 3)), 82 * u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) ≤
      82 * ∫ u in Ioi (0 : ℝ), u ^ 9 * Real.exp (-(a / 2) * u ^ 2) := by
    simp_rw [mul_assoc]
    rw [← integral_const_mul]
    exact setIntegral_mono_set ((integrableOn_pow_mul_exp_half_sq ha 9).const_mul 82)
      ((ae_restrict_mem measurableSet_Ioi).mono fun u hu => by have : 0 < u := hu; positivity)
      (Eventually.of_forall fun _ hu => hu.1)
  have ha4 : (a ^ 4)⁻¹ = a ^ (-4 : ℝ) := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ha, ← Real.norm_eq_abs]
  calc a * ‖_‖ ≤ a * (82 * ∫ u in Ioi (0 : ℝ), u ^ 9 * Real.exp (-(a / 2) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left (hle1.trans hle2) ha.le
    _ = 82 * (a * ∫ u in Ioi (0 : ℝ), u ^ (2 * 4 + 1) * Real.exp (-(a / 2) * u ^ 2)) := by ring_nf
    _ = 82 * (2 ^ 4 * (4 ! : ℝ)) * a ^ (-4 : ℝ) := by
        rw [gaussMoment_odd ha 4, div_eq_mul_inv, ha4]; ring
    _ ≤ 82 * (2 ^ 4 * (4 ! : ℝ)) * ‖a ^ (-4 : ℝ)‖ := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg ha.le _)]

private theorem isBigO_main_interval {s : ℝ} (hs : |s| = 1) :
    (fun a : ℝ => a * (∫ v in (0 : ℝ)..(1 / 3),
        (1 - s * v)⁻¹ * Real.exp (-a * diagPhase (s * v))) -
      (diagSeries8 s a -
        571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2)) * a ^ (-7 / 2 : ℝ)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hc_pos : 0 < diagCoord s (1 / 3) := by
    refine Real.sqrt_pos.mpr ?_
    have hsv := mem_Icc_third_of_abs_eq_one hs ⟨by norm_num, le_rfl⟩
    have hq := diagPhase_lower_quad hsv
    have hsq : (s * (1 / 3)) ^ 2 = 1 / 9 := by rw [mul_pow, ← sq_abs, hs]; norm_num
    linarith [hsq]
  refine ((isBigO_main_interval_err hs).sub (isBigO_gauss_tail hc_pos hs)).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_diagQ_mul_exp ha s) hc_pos.le
  rw [← hsplit]
  linear_combination -(integral_diagQ_mul_exp_eq ha hs)

/-! ### Lower and upper integral decomposition at `t = a` -/

private theorem rpow_exp_cancel {a : ℝ} (ha : 0 < a) :
    a ^ (1 - a) * Real.exp a * (a ^ a * Real.exp (-a)) = a ∧
    a ^ (a - 1) * Real.exp (-a) * (a ^ (1 - a) * Real.exp a) = 1 := by
  have ha1 : a ^ (1 - a) * a ^ a = a := by
    rw [← Real.rpow_add ha, show 1 - a + a = 1 by ring, Real.rpow_one]
  have ha0 : a ^ (a - 1) * a ^ (1 - a) = 1 := by
    rw [← Real.rpow_add ha, show a - 1 + (1 - a) = 0 by ring, Real.rpow_zero]
  have he1 : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact ⟨calc a ^ (1 - a) * Real.exp a * (a ^ a * Real.exp (-a))
        = (a ^ (1 - a) * a ^ a) * (Real.exp a * Real.exp (-a)) := by ring
      _ = a := by rw [ha1, he1, mul_one],
    calc a ^ (a - 1) * Real.exp (-a) * (a ^ (1 - a) * Real.exp a)
        = (a ^ (a - 1) * a ^ (1 - a)) * (Real.exp a * Real.exp (-a)) := by ring
      _ = 1 := by rw [ha0, he1, mul_one]⟩

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
    have ha_a : a * a ^ (a - 1) = a ^ a :=
      calc a * a ^ (a - 1) = a ^ (1 : ℝ) * a ^ (a - 1) := by rw [Real.rpow_one]
        _ = a ^ a := by rw [← Real.rpow_add ha0]; congr 1; ring
    calc a * (a ^ (a - 1) * (1 - v) ^ (a - 1) * (Real.exp (-a) * Real.exp (a * v)))
        = (a * a ^ (a - 1)) * Real.exp (-a) * ((1 - v) ^ (a - 1) * Real.exp (a * v)) := by ring
      _ = a ^ a * Real.exp (-a) * ((1 - v) ^ (a - 1) * Real.exp (a * v)) := by rw [ha_a]
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
  refine isBigO_mul_self_rpow_neg_four_of_exp (by norm_num : (0 : ℝ) < 1 / 48) ?_
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
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  rw [Real.mul_rpow ha.le hs0.le, Real.rpow_def_of_pos hs0, mul_assoc (a ^ (a - 1)),
    ← Real.exp_add, show Real.log s * (a - 1) + -(a * s) =
      -Real.log s + (-a + (-a * diagPhase (-(s - 1)))) by
        unfold diagPhase; simp [sub_eq_add_neg]; ring,
    Real.exp_add, Real.exp_add, Real.exp_neg s.log, Real.exp_log hs0]
  calc a ^ (1 - a) * Real.exp a *
        (a ^ (a - 1) * (s⁻¹ * (Real.exp (-a) * Real.exp (-a * diagPhase (-(s - 1))))))
      = (a ^ (a - 1) * Real.exp (-a) * (a ^ (1 - a) * Real.exp a)) *
          (s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) := by ring
    _ = s⁻¹ * Real.exp (-a * diagPhase (-(s - 1))) := by rw [(rpow_exp_cancel ha).2, one_mul]

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
    have hs0 : 0 < s := lt_trans zero_lt_one hs
    have ha_c : a * a ^ (a - 1) = a ^ a :=
      calc a * a ^ (a - 1) = a ^ (1 : ℝ) * a ^ (a - 1) := by rw [Real.rpow_one]
        _ = a ^ a := by rw [← Real.rpow_add ha0]; congr 1; ring
    rw [Real.mul_rpow ha0.le hs0.le, Real.rpow_def_of_pos hs0, mul_assoc (a ^ (a - 1)),
      ← Real.exp_add, show Real.log s * (a - 1) + -(a * s) =
        -Real.log s + (-a + (-a * diagPhase (-(s - 1)))) by
          unfold diagPhase; simp [sub_eq_add_neg]; ring,
      Real.exp_add, Real.exp_add, Real.exp_neg s.log, Real.exp_log hs0]
    calc a * (a ^ (a - 1) * (s⁻¹ * (Real.exp (-a) * Real.exp (-a * diagPhase (-(s - 1))))))
        = (a * a ^ (a - 1)) * Real.exp (-a) *
            (s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) := by ring
      _ = a ^ a * Real.exp (-a) *
            (s⁻¹ * Real.exp (-a * diagPhase (-(s - 1)))) := by rw [ha_c]
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
  refine isBigO_mul_self_rpow_neg_four_of_exp (by norm_num : (0 : ℝ) < 1 / 24) ?_
  refine IsBigO.of_bound (|∫ s in Ioi (4 / 3 : ℝ), Real.exp (4 / 3 : ℝ) * Real.exp (-1 * s)|) ?_
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

private theorem isBigO_lower_sharp :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * lowerIncompleteGamma a a -
      (diagSeries8 1 a -
        571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2)) * a ^ (-7 / 2 : ℝ)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hm := isBigO_main_interval (s := 1) (by norm_num)
  refine (hm.add isBigO_lower_tail).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
  have hsc := lower_scaled_integral ha
  simp only [one_mul]; linarith

private theorem isBigO_upper_sharp :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * (Real.Gamma a - lowerIncompleteGamma a a) -
      (diagSeries8 (-1) a -
        571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2)) * a ^ (-7 / 2 : ℝ)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hm := isBigO_main_interval (s := -1) (by norm_num)
  refine (hm.add isBigO_upper_tail).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
  have hsc := upper_scaled_integral ha
  have hmain_eq : (∫ v in (0 : ℝ)..(1 / 3), (1 - -1 * v)⁻¹ * Real.exp (-a * diagPhase (-1 * v))) =
      ∫ v in (0 : ℝ)..(1 / 3), (1 + v)⁻¹ * Real.exp (-a * diagPhase (-v)) :=
    intervalIntegral.integral_congr fun v _ => by simp [sub_neg_eq_add]
  rw [hmain_eq]; linarith

private theorem isBigO_rpow_le {p q : ℝ} (hpq : p ≤ q) :
    (fun a : ℝ => a ^ p) =O[atTop] fun a : ℝ => a ^ q := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha0 : 0 < a := by linarith
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg ha0.le p),
    Real.norm_of_nonneg (Real.rpow_nonneg ha0.le q)]
  exact Real.rpow_le_rpow_of_exponent_le ha hpq

private theorem isBigO_div_pow (k m : ℕ) (hkm : m ≤ k) (c : ℝ) :
    (fun a : ℝ => c / a ^ k) =O[atTop] fun a : ℝ => a ^ (-(m : ℝ)) := by
  have hle : -(k : ℝ) ≤ -(m : ℝ) := neg_le_neg (Nat.cast_le.mpr hkm)
  refine ((isBigO_rpow_le hle).const_mul_left c).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [Real.rpow_neg ha.le, Real.rpow_natCast, div_eq_mul_inv]

private theorem isBigO_div_pow_one (k : ℕ) (c : ℝ) :
    (fun a : ℝ => c / a ^ k) =O[atTop] fun _ : ℝ => (1 : ℝ) :=
  (isBigO_div_pow k 0 (Nat.zero_le k) c).congr_right fun _ => by simp

/-! ### Diagonal incomplete Gamma expansions and limits -/

/-- Eight-term normalized diagonal asymptotic expansion of `TauCeti.lowerIncompleteGamma a a` as
`a → +∞`. -/
theorem isBigO_mul_lowerIncompleteGamma_diag_sub :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * lowerIncompleteGamma a a -
      (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + 1 / 3 +
        Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + 4 / (135 * a) +
        Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - 8 / (2835 * a ^ 2) -
        139 * Real.sqrt (2 * Real.pi) / 103680 * a ^ (-5 / 2 : ℝ) - 16 / (8505 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-7 / 2 : ℝ) := by
  have h2 := (isBigO_refl (fun a : ℝ => a ^ (-7 / 2 : ℝ)) atTop).const_mul_left
    (571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2)))
  refine ((isBigO_lower_sharp.trans (isBigO_rpow_le (by norm_num))).sub h2).congr' ?_ .rfl
  exact Eventually.of_forall fun a => by unfold diagSeries8; ring

/-- Eight-term normalized diagonal asymptotic expansion of the upper incomplete Gamma tail
`Real.Gamma a - TauCeti.lowerIncompleteGamma a a` as `a → +∞` (DLMF 8.11.12 to `O(a^{-7/2})`). -/
theorem isBigO_mul_Gamma_sub_lowerIncompleteGamma_diag_sub :
    (fun a : ℝ => a ^ (1 - a) * Real.exp a * (Real.Gamma a - lowerIncompleteGamma a a) -
      (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) - 1 / 3 +
        Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) - 4 / (135 * a) +
        Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) + 8 / (2835 * a ^ 2) -
        139 * Real.sqrt (2 * Real.pi) / 103680 * a ^ (-5 / 2 : ℝ) + 16 / (8505 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-7 / 2 : ℝ) := by
  have h2 := (isBigO_refl (fun a : ℝ => a ^ (-7 / 2 : ℝ)) atTop).const_mul_left
    (571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2)))
  refine ((isBigO_upper_sharp.trans (isBigO_rpow_le (by norm_num))).sub h2).congr' ?_ .rfl
  exact Eventually.of_forall fun a => by unfold diagSeries8; ring

private theorem isBigO_unnormalized_six {f : ℝ → ℝ} (s : ℝ)
    (hf : (fun a : ℝ => a ^ (1 - a) * Real.exp a * f a - diagSeries8 s a)
      =O[atTop] fun a : ℝ => a ^ (-7 / 2 : ℝ)) :
    (fun a : ℝ => f a - a ^ (a - 1) * Real.exp (-a) *
      (Real.sqrt (Real.pi / 2) * a ^ (1 / 2 : ℝ) + s * (1 / 3) +
        Real.sqrt (2 * Real.pi) / 24 * a ^ (-1 / 2 : ℝ) + s * (4 / (135 * a)) +
        Real.sqrt (2 * Real.pi) / 576 * a ^ (-3 / 2 : ℝ) - s * (8 / (2835 * a ^ 2))))
      =O[atTop] fun a : ℝ => a ^ (a - 7 / 2) * Real.exp (-a) := by
  have h8 := hf.trans (isBigO_rpow_le (by norm_num : (-7 / 2 : ℝ) ≤ -5 / 2))
  have h6 := (isBigO_refl (fun a : ℝ => a ^ (-5 / 2 : ℝ)) atTop).const_mul_left
    (-139 * Real.sqrt (2 * Real.pi) / 103680)
  have h7 : (fun a : ℝ => -(s * 16 / 8505) / a ^ 3) =O[atTop] fun a : ℝ => a ^ (-5 / 2 : ℝ) :=
    (isBigO_div_pow 3 3 le_rfl _).trans (isBigO_rpow_le (by norm_num : (-(3 : ℝ)) ≤ -5 / 2))
  refine ((isBigO_refl (fun a : ℝ => a ^ (a - 1) * Real.exp (-a)) atTop).mul
    ((h8.add h6).add h7)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have hc := (rpow_exp_cancel ha).2
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

/-- Four-term Stirling expansion of `a^{1/2 - a} e^a Γ(a)` obtained by adding the lower and upper
diagonal expansions. -/
private theorem isBigO_stirling_four :
    (fun a : ℝ => a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a -
      Real.sqrt (2 * Real.pi) * (1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  have hsum := isBigO_lower_sharp.add isBigO_upper_sharp
  have h8 := (isBigO_refl (fun a : ℝ => a ^ (-7 / 2 : ℝ)) atTop).const_mul_left
    (-2 * (571 / 261273600 * (2 ^ (7 / 2 : ℝ) * Real.Gamma (9 / 2))))
  have htot := (hsum.trans (isBigO_rpow_le (by norm_num : (-4 : ℝ) ≤ -7 / 2))).add h8
  refine ((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul htot).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have hp (p : ℝ) : a ^ (-1 / 2 : ℝ) * a ^ p = a ^ (p - 1 / 2) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    have hn (k : ℕ) : a ^ (-(k : ℝ)) = 1 / a ^ k := by
      rw [Real.rpow_neg ha.le, Real.rpow_natCast, one_div]
    have hp0 := hp (1 - a)
    have hp1 : a ^ (-1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = 1 := by rw [hp]; norm_num
    have hp2 : a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = 1 / a := by
      rw [hp, show (-1 / 2 : ℝ) - 1 / 2 = -((1 : ℕ) : ℝ) by norm_num, hn 1, pow_one]
    have hp3 : a ^ (-1 / 2 : ℝ) * a ^ (-3 / 2 : ℝ) = 1 / a ^ 2 := by
      rw [hp, show (-3 / 2 : ℝ) - 1 / 2 = -((2 : ℕ) : ℝ) by norm_num, hn 2]
    have hp4 : a ^ (-1 / 2 : ℝ) * a ^ (-5 / 2 : ℝ) = 1 / a ^ 3 := by
      rw [hp, show (-5 / 2 : ℝ) - 1 / 2 = -((3 : ℕ) : ℝ) by norm_num, hn 3]
    have hpi : 2 * Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul zero_le_two]
      have : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
        rw [div_eq_iff (Real.sqrt_pos.mpr two_pos).ne', Real.mul_self_sqrt zero_le_two]
      linear_combination Real.sqrt Real.pi * this
    rw [show (1 - a) - 1 / 2 = 1 / 2 - a by ring] at hp0
    unfold diagSeries8
    linear_combination
      Real.exp a * Real.Gamma a * hp0 - Real.sqrt (2 * Real.pi) * hp1 - hpi * (a ^ (-1 / 2 : ℝ) *
        a ^ (1 / 2 : ℝ)) - (Real.sqrt (2 * Real.pi) / 12) * hp2 -
        (Real.sqrt (2 * Real.pi) / 288) * hp3 + (139 * Real.sqrt (2 * Real.pi) / 51840) * hp4
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [← Real.rpow_add ha]; congr 1; ring

private theorem eventually_one_le_stirling :
    ∀ᶠ a : ℝ in atTop, 1 ≤ a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a := by
  obtain ⟨C, hC⟩ := isBigO_stirling_four.bound
  filter_upwards [eventually_ge_atTop (max 2 (2 * |C| + 1)), hC] with a ha hCa
  have ha2 : 2 ≤ a := le_trans (le_max_left _ _) ha
  have haC : 2 * |C| + 1 ≤ a := le_trans (le_max_right _ _) ha
  have hA : 3 / 4 ≤ 1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3) := by
    have h1 : 0 ≤ 1 / (12 * a) := by positivity
    have h2 : 0 ≤ 1 / (288 * a ^ 2) := by positivity
    have h3 : 139 / (51840 * a ^ 3) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg a]
    linarith
  have hpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq zero_le_two).symm
      _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have ha4 : a ^ (-4 : ℝ) ≤ (2 * |C| + 1)⁻¹ :=
    calc a ^ (-4 : ℝ) ≤ a ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = a⁻¹ := Real.rpow_neg_one a
      _ ≤ (2 * |C| + 1)⁻¹ := inv_anti₀ (by positivity) haC
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hCa
  have herr : |a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a - Real.sqrt (2 * Real.pi) *
      (1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3))| ≤ 1 / 2 :=
    calc _ ≤ C * a ^ (-4 : ℝ) := hCa
      _ ≤ |C| * (2 * |C| + 1)⁻¹ := mul_le_mul (le_abs_self C) ha4 (by positivity) (abs_nonneg C)
      _ ≤ 1 / 2 := by rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [abs_nonneg C]
  nlinarith [(abs_le.mp herr).1]

private theorem isBigO_cubic_inv_one (c0 c1 c2 c3 : ℝ) :
    (fun a : ℝ => c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3) =O[atTop] fun _ : ℝ => (1 : ℝ) :=
  ((((isBigO_div_pow_one 0 c0).add (isBigO_div_pow_one 1 c1)).add
    (isBigO_div_pow_one 2 c2)).add (isBigO_div_pow_one 3 c3)).congr_left fun a => by ring

private theorem rpow_neg_half_mul_inv_sqrt_two_pi {a : ℝ} (ha : 0 < a) :
    a ^ (-1 / 2 : ℝ) * (Real.sqrt (2 * Real.pi))⁻¹ = (Real.sqrt (2 * Real.pi * a))⁻¹ := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi) a, mul_inv, mul_comm,
    show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]

private theorem isBigO_inv_stirling_four :
    (fun a : ℝ => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ -
      (Real.sqrt (2 * Real.pi))⁻¹ * (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
  let S : ℝ → ℝ := fun a => a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a
  let A : ℝ → ℝ := fun a => 1 + 1 / (12 * a) + 1 / (288 * a ^ 2) - 139 / (51840 * a ^ 3)
  let B : ℝ → ℝ := fun a => 1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)
  have hinvS : (fun a : ℝ => (S a)⁻¹) =O[atTop] fun _ : ℝ => (1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_one_le_stirling] with a ha
    rw [Real.norm_of_nonneg (by positivity), norm_one, one_mul]
    exact inv_le_one_of_one_le₀ ha
  have hB_bdd : B =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    (isBigO_cubic_inv_one 1 (-1 / 12) (1 / 288) (139 / 51840)).congr_left fun a => by
      dsimp only [B]; ring
  have hAB : (fun a : ℝ => 1 - A a * B a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    refine ((isBigO_div_pow 4 4 le_rfl (-571 / 1244160)).add
      (isBigO_div_pow 6 4 (by omega) (19321 / 2687385600))).congr' ?_
      (Eventually.of_forall fun _ => by norm_num)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have : a ≠ 0 := ha.ne'; dsimp only [A, B]; field_simp; ring
  have h1 : (fun a : ℝ => -(Real.sqrt (2 * Real.pi))⁻¹ * ((S a)⁻¹ *
      ((S a - Real.sqrt (2 * Real.pi) * A a) * B a))) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    ((hinvS.mul (isBigO_stirling_four.mul hB_bdd)).const_mul_left _).congr_right fun _ => by ring
  have h2 : (fun a : ℝ => (S a)⁻¹ * (1 - A a * B a)) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    (hinvS.mul hAB).congr_right fun _ => by ring
  refine (h1.add h2).congr' ?_ .rfl
  filter_upwards [eventually_one_le_stirling] with a ha
  have hS0 : S a ≠ 0 := by dsimp only [S]; linarith
  have hpi0 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  change _ = (S a)⁻¹ - (Real.sqrt (2 * Real.pi))⁻¹ * B a
  field_simp [hS0, hpi0]; ring

/-- Four-term asymptotic expansion of the diagonal regularized lower incomplete Gamma function
`TauCeti.regularizedGamma a a` as `a → +∞`, with remainder `O(a^{-9/2})`. -/
theorem isBigO_regularizedGamma_diag_sub :
    (fun a : ℝ => regularizedGamma a a -
      (1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3))))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
  let D : ℝ → ℝ := fun a => a ^ (1 - a) * Real.exp a * (lowerIncompleteGamma a a - Real.Gamma a / 2)
  let P_D : ℝ → ℝ := fun a => 1 / 3 + 4 / (135 * a) - 8 / (2835 * a ^ 2) - 16 / (8505 * a ^ 3)
  let S_inv : ℝ → ℝ := fun a => (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹
  let P_S : ℝ → ℝ := fun a => (Real.sqrt (2 * Real.pi))⁻¹ *
    (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3))
  let P_out : ℝ → ℝ := fun a => (Real.sqrt (2 * Real.pi))⁻¹ *
    (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3))
  have hPD : P_D =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    (isBigO_cubic_inv_one (1 / 3) (4 / 135) (-8 / 2835) (-16 / 8505)).congr_left fun a => by
      dsimp only [P_D]; ring
  have hPS : P_S =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    ((isBigO_cubic_inv_one 1 (-1 / 12) (1 / 288) (139 / 51840)).const_mul_left
      (Real.sqrt (2 * Real.pi))⁻¹).congr_left fun a => by dsimp only [P_S]; ring
  have hSinv : S_inv =O[atTop] fun _ : ℝ => (1 : ℝ) :=
    ((isBigO_inv_stirling_four.trans (isBigO_rpow_le (by norm_num : (-4 : ℝ) ≤ 0)) |>.congr_right
      fun a => Real.rpow_zero a).add hPS).congr_left fun a => by ring
  have hpoly : (fun a : ℝ => P_D a * P_S a - P_out a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) := by
    refine ((((isBigO_div_pow 4 4 le_rfl (2773 / 12247200)).sub
      (isBigO_div_pow 5 4 (by omega) (37 / 2624400))).sub
      (isBigO_div_pow 6 4 (by omega) (139 / 27556200))).const_mul_left
      (Real.sqrt (2 * Real.pi))⁻¹).congr' ?_ (Eventually.of_forall fun _ => by norm_num)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have : a ≠ 0 := ha.ne'; dsimp only [P_D, P_S, P_out]; field_simp; ring
  have hprod : (fun a : ℝ => D a * S_inv a - P_out a) =O[atTop] fun a : ℝ => a ^ (-4 : ℝ) :=
    ((((isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma.mul hSinv).congr_right
      fun _ => mul_one _).add ((hPD.mul isBigO_inv_stirling_four).congr_right
      fun _ => one_mul _)).add hpoly).congr_left fun a => by ring
  refine ((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul hprod).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [regularizedGamma_eq_div]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have he : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
    have hp : a ^ (-1 / 2 : ℝ) * a ^ (1 - a) = a ^ (1 / 2 - a) := by
      rw [← Real.rpow_add ha]; congr 1; ring
    have hrel : a ^ (-1 / 2 : ℝ) * D a * S_inv a =
        lowerIncompleteGamma a a / Real.Gamma a - 1 / 2 := by
      dsimp only [D, S_inv]; rw [← mul_assoc, ← mul_assoc, hp]
      field_simp [hG, he, (Real.rpow_pos_of_pos ha (1 / 2 - a)).ne']
    dsimp only [P_out]
    linear_combination hrel -
      (1 / 3 + 1 / (540 * a) - 25 / (6048 * a ^ 2) - 101 / (155520 * a ^ 3)) *
        rpow_neg_half_mul_inv_sqrt_two_pi ha
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [← Real.rpow_add ha]; congr 1; ring

/-- Four-term asymptotic expansion of `TauCeti.regularizedGamma (a + 1) a` as `a → +∞`, with
remainder `O(a^{-9/2})`. -/
theorem isBigO_regularizedGamma_add_one_diag_sub :
    (fun a : ℝ => regularizedGamma (a + 1) a -
      (1 / 2 - (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (2 / 3 - 23 / (270 * a) + 23 / (3024 * a ^ 2) + 259 / (77760 * a ^ 3))))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
  have hterm : (fun a : ℝ => -(a ^ a * Real.exp (-a) / Real.Gamma (a + 1)) +
      (Real.sqrt (2 * Real.pi * a))⁻¹ *
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)))
      =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ) := by
    refine (((isBigO_refl (fun a : ℝ => a ^ (-1 / 2 : ℝ)) atTop).mul
      isBigO_inv_stirling_four).neg_left).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [Real.Gamma_add_one ha.ne']
      have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      have hp : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹ = a ^ a / a := by
        rw [← Real.rpow_neg ha.le, ← Real.rpow_add ha,
          show (-1 / 2 : ℝ) + -(1 / 2 - a) = a + (-1) by ring,
          Real.rpow_add ha, Real.rpow_neg_one, div_eq_mul_inv]
      have hid : a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹ =
          a ^ a * Real.exp (-a) / (a * Real.Gamma a) :=
        calc a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a) * Real.exp a * Real.Gamma a)⁻¹
            = (a ^ (-1 / 2 : ℝ) * (a ^ (1 / 2 - a))⁻¹) * Real.exp (-a) * (Real.Gamma a)⁻¹ := by
                rw [Real.exp_neg, mul_inv, mul_inv]; ring
          _ = a ^ a * Real.exp (-a) / (a * Real.Gamma a) := by rw [hp]; field_simp [ha.ne', hG]
      linear_combination -hid +
        (1 - 1 / (12 * a) + 1 / (288 * a ^ 2) + 139 / (51840 * a ^ 3)) *
          rpow_neg_half_mul_inv_sqrt_two_pi ha
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      rw [← Real.rpow_add ha]; congr 1; ring
  refine (isBigO_regularizedGamma_diag_sub.add hterm).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [regularizedGamma_add_one ha ha.le]; ring

private theorem tendsto_of_sub_regularized_isBigO {f : ℝ → ℝ} (c0 c1 c2 c3 : ℝ)
    (hf : (fun a : ℝ => f a - (1 / 2 + (Real.sqrt (2 * Real.pi * a))⁻¹ *
      (c0 + c1 / a + c2 / a ^ 2 + c3 / a ^ 3))) =O[atTop] fun a : ℝ => a ^ (-9 / 2 : ℝ)) :
    Tendsto f atTop (𝓝 (1 / 2)) := by
  have hb := isBigO_cubic_inv_one c0 c1 c2 c3
  have hsq : (fun a : ℝ => (Real.sqrt (2 * Real.pi * a))⁻¹) =O[atTop]
      fun a : ℝ => a ^ (-(1 / 2 : ℝ)) := by
    refine ((isBigO_refl (fun a : ℝ => a ^ (-(1 / 2 : ℝ))) atTop).const_mul_left
      (Real.sqrt (2 * Real.pi))⁻¹).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [← rpow_neg_half_mul_inv_sqrt_two_pi ha, show (-1 / 2 : ℝ) = -(1 / 2) by ring, mul_comm]
  have hdiff : (fun a : ℝ => f a - 1 / 2) =O[atTop] fun a : ℝ => a ^ (-(1 / 2 : ℝ)) :=
    ((hf.trans (isBigO_rpow_le (by norm_num : (-9 / 2 : ℝ) ≤ -(1 / 2)))).add
      ((hsq.mul hb).congr_right fun _ => mul_one _)).congr_left fun a => by ring
  simpa using (hdiff.trans_tendsto
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))).add_const (1 / 2 : ℝ)

/-- **DLMF 8.11.13** on `(0, ∞)`: `P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma a a) atTop (𝓝 (1 / 2)) :=
  tendsto_of_sub_regularized_isBigO (1 / 3) (1 / 540) (-25 / 6048) (-101 / 155520)
    (isBigO_regularizedGamma_diag_sub.congr_left fun a => by ring)

/-- **DLMF 8.11.13** on `(0, ∞)`: `1 - P(a, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_sub_regularizedGamma_diag_atTop :
    Tendsto (fun a : ℝ => 1 - regularizedGamma a a) atTop (𝓝 (1 / 2)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_regularizedGamma_diag_atTop
  norm_num at h; exact h

/-- `P(a + 1, a) → 1 / 2` as `a → +∞`. -/
theorem tendsto_regularizedGamma_add_one_diag_atTop :
    Tendsto (fun a : ℝ => regularizedGamma (a + 1) a) atTop (𝓝 (1 / 2)) :=
  tendsto_of_sub_regularized_isBigO (-2 / 3) (23 / 270) (-23 / 3024) (-259 / 77760)
    (isBigO_regularizedGamma_add_one_diag_sub.congr_left fun a => by ring)

/-! ### Ramanujan's `θ(n)` and central exponential partial sums -/

/-- Ramanujan's remainder function `θ(n)` for the central partial sum of the exponential series
(Ramanujan 1911; DLMF 8.11.14–8.11.15), uniquely determined for every `n : ℕ` by
`∑ k < n, n ^ k / k! + (n ^ n / n!) * θ(n) = exp n / 2`. -/
def ramanujanTheta (n : ℕ) : ℝ :=
  (n ! : ℝ) / (n : ℝ) ^ n * (Real.exp n / 2 - ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ))

/-- Explicit formula unfolding `TauCeti.ramanujanTheta`. -/
theorem ramanujanTheta_def (n : ℕ) :
    ramanujanTheta n = (n ! : ℝ) / (n : ℝ) ^ n *
      (Real.exp n / 2 - ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) := by rfl

private theorem natCast_pow_self_pos (n : ℕ) : 0 < (n : ℝ) ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) n

/-- At `n = 0`, `θ(0) = 1 / 2` under the convention `0 ^ 0 = 1`. -/
@[simp]
theorem ramanujanTheta_zero : ramanujanTheta 0 = 1 / 2 := by simp [ramanujanTheta_def]

/-- At `n = 1`, `θ(1) = e / 2 - 1`. -/
@[simp]
theorem ramanujanTheta_one : ramanujanTheta 1 = Real.exp 1 / 2 - 1 := by simp [ramanujanTheta_def]

/-- **DLMF 8.11.14 / Ramanujan's defining equation**: for every `n : ℕ`,
`∑_{k < n} n^k / k! + (n^n / n!) θ(n) = e^n / 2`. -/
theorem sum_range_add_ramanujanTheta (n : ℕ) :
    (∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) +
      (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n = Real.exp n / 2 := by
  rw [ramanujanTheta_def]
  have hf : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp : (n : ℝ) ^ n ≠ 0 := (natCast_pow_self_pos n).ne'
  field_simp [hf, hp]; ring

/-- Normalized form of DLMF 8.11.14 for the strict partial sum `k < n`, valid for every `n : ℕ`. -/
theorem exp_neg_mul_sum_range_eq_sub_ramanujanTheta (n : ℕ) :
    Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) =
      1 / 2 - Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n := by
  have h := congr_arg (Real.exp (-(n : ℝ)) * ·) (sum_range_add_ramanujanTheta n)
  have he : Real.exp (-(n : ℝ)) * Real.exp (n : ℝ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination h + 1 / 2 * he

/-- Normalized form of DLMF 8.11.14 for the inclusive partial sum `k ≤ n`, valid for every
`n : ℕ`. -/
theorem exp_neg_mul_sum_range_succ_eq_add_sub_ramanujanTheta (n : ℕ) :
    Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k ! : ℝ)) =
      1 / 2 + Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * (1 - ramanujanTheta n) := by
  rw [Finset.sum_range_succ, mul_add, exp_neg_mul_sum_range_eq_sub_ramanujanTheta]; ring

/-- **DLMF 8.11.15**: for `n ≠ 0`, `P(n, n) = 1 / 2 + e^{-n} (n^n / n!) θ(n)`.
The hypothesis `n ≠ 0` is necessary because `TauCeti.regularizedGamma 0 0 = 0`, whereas the
right-hand side evaluates to `1` at `n = 0`. -/
theorem regularizedGamma_diag_natCast_eq_add_ramanujanTheta {n : ℕ} (hn : n ≠ 0) :
    regularizedGamma n n =
      1 / 2 + Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n := by
  rw [regularizedGamma_natCast hn (Nat.cast_nonneg n), exp_neg_mul_sum_range_eq_sub_ramanujanTheta]
  ring

/-- Exact incomplete-Gamma representation of `θ(n)` for `n ≠ 0`:
`θ(n) = n^{1 - n} e^n (γ(n, n) - Γ(n) / 2)`.
The hypothesis `n ≠ 0` is necessary because at `n = 0` the right-hand side is `0`, whereas
`θ(0) = 1 / 2`. -/
theorem ramanujanTheta_eq_mul_lowerIncompleteGamma_sub_half_Gamma {n : ℕ} (hn : n ≠ 0) :
    ramanujanTheta n =
      (n : ℝ) ^ (1 - (n : ℝ)) * Real.exp n * (lowerIncompleteGamma n n - Real.Gamma n / 2) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hP := regularizedGamma_diag_natCast_eq_add_ramanujanTheta hn
  rw [regularizedGamma_eq_div] at hP
  have hG_pos : 0 < Real.Gamma n := Real.Gamma_pos_of_pos hn_pos
  have hfact : (n ! : ℝ) = (n : ℝ) * Real.Gamma n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.Gamma_nat_eq_factorial]
  have hrpow : (n : ℝ) ^ (1 - (n : ℝ)) * (n : ℝ) ^ n = (n : ℝ) := by
    rw [← Real.rpow_natCast (n : ℝ) n, ← Real.rpow_add hn_pos,
      show 1 - (n : ℝ) + (n : ℝ) = 1 by ring, Real.rpow_one]
  have hexp : Real.exp n * Real.exp (-(n : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsub : lowerIncompleteGamma n n - Real.Gamma n / 2 =
      Real.Gamma n * (Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n ! : ℝ) * ramanujanTheta n) := by
    have hG_ne := hG_pos.ne'; field_simp [hG_ne] at hP ⊢; linarith
  symm
  calc (n : ℝ) ^ (1 - (n : ℝ)) * Real.exp n * (lowerIncompleteGamma n n - Real.Gamma n / 2)
      = ((n : ℝ) ^ (1 - (n : ℝ)) * (n : ℝ) ^ n) * (Real.exp n * Real.exp (-(n : ℝ))) *
          (Real.Gamma n / ((n : ℝ) * Real.Gamma n)) * ramanujanTheta n := by
            rw [hsub, hfact]; ring
    _ = ramanujanTheta n := by rw [hrpow, hexp, mul_one]; field_simp [hn_pos.ne', hG_pos.ne']

/-- **DLMF 8.11.17 (Ramanujan's asymptotic expansion)**: four-term asymptotic expansion of
`TauCeti.ramanujanTheta n` as `n → ∞`, with sharp remainder `O(n^{-4})`. -/
theorem isBigO_ramanujanTheta_sub :
    (fun n : ℕ => ramanujanTheta n -
      (1 / 3 + 4 / (135 * (n : ℝ)) - 8 / (2835 * (n : ℝ) ^ 2) - 16 / (8505 * (n : ℝ) ^ 3)))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (-4 : ℝ) := by
  refine (isBigO_mul_lowerIncompleteGamma_diag_sub_half_Gamma.comp_tendsto
    tendsto_natCast_atTop_atTop).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply,
    ramanujanTheta_eq_mul_lowerIncompleteGamma_sub_half_Gamma (Nat.one_le_iff_ne_zero.mp hn)]

/-- Ramanujan's limit `θ(n) → 1 / 3` as `n → ∞`. -/
theorem tendsto_ramanujanTheta_atTop :
    Tendsto ramanujanTheta atTop (𝓝 (1 / 3)) := by
  have h1 : (fun a : ℝ => 4 / (135 * a) - 8 / (2835 * a ^ 2) - 16 / (8505 * a ^ 3))
      =O[atTop] fun a : ℝ => a ^ (-(1 : ℝ)) :=
    ((((isBigO_div_pow 1 1 le_rfl (4 / 135)).sub
      (isBigO_div_pow 2 1 (by omega) (8 / 2835))).sub
      (isBigO_div_pow 3 1 (by omega) (16 / 8505))).congr_left fun a => by ring).congr_right
      fun _ => by norm_num
  have hdiff : (fun n : ℕ => ramanujanTheta n - 1 / 3) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ)) :=
    ((isBigO_ramanujanTheta_sub.trans
      ((isBigO_rpow_le (by norm_num : (-4 : ℝ) ≤ -(1 : ℝ))).comp_tendsto
        tendsto_natCast_atTop_atTop)).add
      (h1.comp_tendsto tendsto_natCast_atTop_atTop)).congr_left fun n => by
        simp only [Function.comp_apply]; ring
  simpa using (hdiff.trans_tendsto
    ((tendsto_rpow_neg_atTop one_pos).comp tendsto_natCast_atTop_atTop)).add_const (1 / 3 : ℝ)

/-- **DLMF 8.11.16**: four-term asymptotic expansion of the central exponential partial sum
`e^{-n} ∑_{k ≤ n} n^k / k!` as `n → ∞`, with remainder `O(n^{-9/2})`. -/
theorem isBigO_exp_neg_mul_sum_range_succ_sub :
    (fun n : ℕ => Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k ! : ℝ)) -
      (1 / 2 + (Real.sqrt (2 * Real.pi * n))⁻¹ *
        (2 / 3 - 23 / (270 * (n : ℝ)) + 23 / (3024 * (n : ℝ) ^ 2) +
          259 / (77760 * (n : ℝ) ^ 3))))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (-9 / 2 : ℝ) := by
  refine ((isBigO_regularizedGamma_add_one_diag_sub.comp_tendsto
    tendsto_natCast_atTop_atTop).neg_left).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n _
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [Function.comp_apply, hcast,
    regularizedGamma_natCast (Nat.succ_ne_zero n) (Nat.cast_nonneg n)]; ring

/-- Four-term asymptotic expansion of the strict central exponential partial sum
`e^{-n} ∑_{k < n} n^k / k!` as `n → ∞`, with remainder `O(n^{-9/2})`. -/
theorem isBigO_exp_neg_mul_sum_range_sub :
    (fun n : ℕ => Real.exp (-(n : ℝ)) * (∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ)) -
      (1 / 2 - (Real.sqrt (2 * Real.pi * n))⁻¹ *
        (1 / 3 + 1 / (540 * (n : ℝ)) - 25 / (6048 * (n : ℝ) ^ 2) -
          101 / (155520 * (n : ℝ) ^ 3))))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (-9 / 2 : ℝ) := by
  refine ((isBigO_regularizedGamma_diag_sub.comp_tendsto
    tendsto_natCast_atTop_atTop).neg_left).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply,
    regularizedGamma_natCast (Nat.one_le_iff_ne_zero.mp hn) (Nat.cast_nonneg n)]; ring

/-- Limit `e^{-n} ∑_{k < n} n^k / k! → 1 / 2` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_range_atTop :
    Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)) * ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k ! : ℝ))
      atTop (𝓝 (1 / 2)) := by
  refine (tendsto_sub_regularizedGamma_diag_atTop.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply,
    regularizedGamma_natCast (Nat.one_le_iff_ne_zero.mp hn) (Nat.cast_nonneg n)]; ring

/-- Limit `e^{-n} ∑_{k ≤ n} n^k / k! → 1 / 2` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_range_succ_atTop :
    Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k ! : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    tendsto_regularizedGamma_add_one_diag_atTop).comp tendsto_natCast_atTop_atTop
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n _
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [Function.comp_apply, hcast,
    regularizedGamma_natCast (Nat.succ_ne_zero n) (Nat.cast_nonneg n)]; ring

end TauCeti

end
