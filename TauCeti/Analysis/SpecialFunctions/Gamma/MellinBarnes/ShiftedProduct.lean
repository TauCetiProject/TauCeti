/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.Contour.Residue.VerticalLineShift
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Mellin–Barnes integral of `Γ(s) Γ(s + p)`

For `c ∈ Complex.slitPlane`, `p ∉ ℤ`, and any abscissa `σ > max 0 (-Re p)`, the vertical
Mellin–Barnes integral of the shifted Gamma product `Γ(s) Γ(s + p)` evaluates to the linear
combination of regularized hypergeometric functions `₀F₁`:

`(1 / 2π) ∫ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p) dy`
`  = (π / sin (π p)) (₀F₁(; 1 - p; c) - c ^ p · ₀F₁(; 1 + p; c))`.

This is the classical Mellin–Barnes representation of the modified Bessel function `2 c^{p/2}
K_p(2 √c)` (DLMF 10.32.13, written via DLMF 10.27.4 in terms of `I_{±p}` and hence `₀F₁`),
and on positive real arguments `c > 0` it evaluates the inverse Mellin transform
`mellinInv σ (fun s ↦ Γ(s) Γ(s + p)) c`. Together with the Mellin transform of Macdonald's
integral, this yields the integral representation of generalized Airy functions.

## Proof outline

1. **Exponential decay on vertical strips.** Stirling's vertical-strip formula
   (`TauCeti.exists_norm_Gamma_add_vertical_strip_le`) gives `‖Γ(s) Γ(s + p)‖` decaying like
   `(1 + |Im s|)^K e^{-π |Im s|}` uniformly on `Re s ∈ [a, b]`, while `‖c^{-s}‖` grows at most
   like `e^{|arg c| |Im s|}` (`TauCeti.exists_norm_cpow_strip_le`) with `|arg c| < π` on
   `Complex.slitPlane`. Hence the integrand decays exponentially in `|Im s|` on every vertical
   strip, giving vanishing horizontal rectangle caps, while vertical-line Stirling bounds give
   integrability.
2. **Simple-pole residues.** For `p ∉ ℤ`, the poles of `c^{-s} Γ(s) Γ(s + p)` form two disjoint
   simple-pole lattices `-k` and `-p - k` (`k ∈ ℕ`). Euler's reflection formula converts their
   residues into `(π / sin (π p))` times the terms of `₀F₁(; 1 - p; c)` and
   `-c ^ p · ₀F₁(; 1 + p; c)`.
3. **Contour shifting.** `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue` shifts
   the vertical line from `σ₂` to any pole-avoiding abscissa `σ₁ ≤ σ₂`, picking up the finite sum
   of residues over the union of the pole sets in `(σ₁, σ₂)` (valid for all `p : ℂ`, including
   coincident double poles when `p ∈ ℤ`).
4. **Left-tail decay.** Choosing a pole-avoiding offset `δ ∈ (0, 1)` via
   `TauCeti.exists_mem_Ioo_zero_one_sub_ne_intCast` and applying the left-shift Gamma estimate
   `TauCeti.exists_norm_Gamma_sub_natCast_le` at `σ_N = -N - δ` bounds the shifted vertical
   integral by `O(‖c‖ ^ N / N!) → 0` as `N → ∞`, so the partial residue sums converge to the full
   `₀F₁` series.

## Main results

* `Complex.exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_le`: uniform vertical-strip decay
  `O((1 + |T|)^K e^{-(π - |arg c|) |T|})` of `c ^ (-s) * (Γ(s) * Γ(s + p))` on `Re s ∈ [a, b]`
  for `c ≠ 0`.
* `Complex.integrable_cpow_neg_mul_Gamma_mul_Gamma_add`: vertical-line integrability of
  `y ↦ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p)` for `c ∈ slitPlane` and pole-avoiding `σ`.
* `Complex.residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat` and
  `Complex.residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat`: the residues at `-k` and
  `-p - k`, together with their Euler-reflection forms matching `regularizedHGFunCoeff`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral_eq_sum_residue`: the raw
  finite contour-shift residue-sum identity between any two pole-avoiding vertical lines `σ₁ ≤ σ₂`,
  valid for arbitrary `p : ℂ` (including integer `p` with double poles).
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral`: the `regularizedHGFunCoeff`
  form of the contour-shift identity for `p ∉ ℤ`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add`: evaluation of the vertical integral on
  `Complex.slitPlane` for `σ > max 0 (-Re p)` and `p ∉ ℤ`.
* `Complex.mellinInv_Gamma_mul_Gamma_add_eq_regularizedHGFun`: the `mellinInv` form for real
  `c > 0`.

## References

* NIST Digital Library of Mathematical Functions, §§5.5, 5.11, 10.27, 10.32 (equations 10.27.4
  and 10.32.13).
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, §6.5.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology Nat
open Complex hiding exp continuous_exp log

namespace Complex

/-! ### Regularity and vertical-strip decay -/

/-- For `c ≠ 0`, `z ↦ c ^ (-z)` is entire. -/
private lemma differentiable_cpow_neg {c : ℂ} (hc : c ≠ 0) :
    Differentiable ℂ fun z : ℂ ↦ c ^ (-z) :=
  differentiable_neg.const_cpow (Or.inl hc)

/-- For `c ≠ 0`, the Mellin–Barnes integrand `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` is meromorphic
at every point of `ℂ`. -/
private lemma meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add {c p : ℂ} (hc : c ≠ 0) (s : ℂ) :
    MeromorphicAt (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s :=
  ((differentiable_cpow_neg hc).analyticAt s).meromorphicAt.mul
    ((Meromorphic.Gamma s).mul ((Meromorphic.Gamma _).comp_analyticAt
      (g := fun w : ℂ ↦ w + p) (by fun_prop)))

/-- For `c ≠ 0`, the Mellin–Barnes integrand `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` is complex
differentiable at every `s` avoiding `-ℕ` and `-p - ℕ`. -/
private lemma differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add {c p s : ℂ} (hc : c ≠ 0)
    (hs : ∀ n : ℕ, s ≠ -n) (hsp : ∀ n : ℕ, s + p ≠ -n) :
    DifferentiableAt ℂ (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s :=
  (differentiable_cpow_neg hc s).mul ((differentiableAt_Gamma s hs).mul
    ((differentiableAt_Gamma (s + p) hsp).comp s (differentiableAt_id.add_const p)))

/-- Combines a vertical-line `c ^ (-s)` bound with two Stirling vertical Gamma bounds. -/
private lemma norm_cpow_neg_mul_Gamma_mul_Gamma_add_le {c p s : ℂ} {A C₁ C₂ K₁ K₂ y : ℝ}
    (hcpow : ‖c ^ (-s)‖ ≤ A * Real.exp (|c.arg| * |y|))
    (hG₁ : ‖Gamma s‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y| / 2)))
    (hG₂ : ‖Gamma (s + p)‖ ≤ C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y| / 2))) :
    ‖c ^ (-s) * (Gamma s * Gamma (s + p))‖ ≤
      A * C₁ * C₂ * ((1 + |y|) ^ (K₁ + K₂) * Real.exp (-((π - |c.arg|) * |y|))) := by
  have h0 : 0 ≤ ‖Gamma s‖ * ‖Gamma (s + p)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h1 : 0 ≤ A * Real.exp (|c.arg| * |y|) := (norm_nonneg _).trans hcpow
  have h2 : 0 ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y| / 2)) := (norm_nonneg _).trans hG₁
  have hexp : Real.exp (|c.arg| * |y|) * Real.exp (-(π * |y| / 2)) * Real.exp (-(π * |y| / 2)) =
      Real.exp (-((π - |c.arg|) * |y|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact congrArg Real.exp (by ring)
  rw [norm_mul, norm_mul]
  calc ‖c ^ (-s)‖ * (‖Gamma s‖ * ‖Gamma (s + p)‖)
      ≤ (A * Real.exp (|c.arg| * |y|)) *
          ((C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y| / 2))) *
            (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y| / 2)))) :=
          mul_le_mul hcpow (mul_le_mul hG₁ hG₂ (norm_nonneg _) h2) h0 h1
    _ = A * C₁ * C₂ * (((1 + |y|) ^ K₁ * (1 + |y|) ^ K₂) *
          (Real.exp (|c.arg| * |y|) * Real.exp (-(π * |y| / 2)) *
            Real.exp (-(π * |y| / 2)))) := by ring
    _ = A * C₁ * C₂ * ((1 + |y|) ^ (K₁ + K₂) * Real.exp (-((π - |c.arg|) * |y|))) := by
        rw [← Real.rpow_add (by positivity), hexp]

/-- On any vertical strip `x ∈ [a, b]` and for `c ≠ 0`, the integrand
`c ^ (-s) * (Γ(s) * Γ(s + p))` at `s = x + i T` is `O((1 + |T|)^K exp (-(π - |arg c|) |T|))`
once `|T| ≥ T₀`. -/
theorem exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_le {c p : ℂ} (hc : c ≠ 0) (a b : ℝ) :
    ∃ C K T₀ : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ T : ℝ, T₀ ≤ |T| →
      ‖c ^ (-((x : ℂ) + T * I)) * (Gamma (x + T * I) * Gamma (x + T * I + p))‖ ≤
        C * ((1 + |T|) ^ K * Real.exp (-((π - |c.arg|) * |T|))) := by
  obtain ⟨C₁, hC₁, K₁, T₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_vertical_strip_le 0 a b
  obtain ⟨C₂, hC₂, K₂, T₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_vertical_strip_le p a b
  obtain ⟨Cz, hzb⟩ := TauCeti.exists_norm_cpow_strip_le hc (-b) (-a)
  refine ⟨max Cz 0 * C₁ * C₂, K₁ + K₂, max T₁ T₂, by positivity, fun x hx T hT ↦ ?_⟩
  have hG₁ := h₁ x hx T ((le_max_left T₁ T₂).trans hT)
  have hG₂ := h₂ x hx T ((le_max_right T₁ T₂).trans hT)
  have hcpow := hzb (-x) ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ (-T)
  rw [zero_add] at hG₁
  rw [add_comm p] at hG₂
  -- Rewrite `(-x : ℂ) + (-T : ℂ) * I` as `-(x + T * I)` to match the target norm bound.
  have hneg : ((-x : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I = -((x : ℂ) + T * I) := by push_cast; ring
  rw [hneg, abs_neg] at hcpow
  have hcpow' : ‖c ^ (-((x : ℂ) + T * I))‖ ≤ max Cz 0 * Real.exp (|c.arg| * |T|) :=
    hcpow.trans (mul_le_mul_of_nonneg_right (le_max_left Cz 0) (Real.exp_pos _).le)
  exact norm_cpow_neg_mul_Gamma_mul_Gamma_add_le hcpow' hG₁ hG₂

/-- For `c ∈ Complex.slitPlane` and any abscissa `σ` avoiding the poles of `Γ(s)` and `Γ(s + p)`,
the vertical Mellin–Barnes integrand `y ↦ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p)` is
integrable on `ℝ`. -/
theorem integrable_cpow_neg_mul_Gamma_mul_Gamma_add {c p : ℂ} (hc : c ∈ slitPlane)
    {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) (hσp : ∀ n : ℕ, σ + p.re ≠ -n) :
    Integrable fun y : ℝ ↦
      c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p)) := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  have hα : 0 < π - |c.arg| := sub_pos.mpr (abs_arg_lt_pi_of_mem_slitPlane hc)
  have hcont : Continuous fun y : ℝ ↦
      c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p)) := by
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    exact (differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add hc0
      (fun n h ↦ hσ n (by simpa using congrArg re h))
      (fun n h ↦ hσp n (by simpa using congrArg re h))).continuousAt.comp (by fun_prop)
  obtain ⟨C₁, _, hG₁⟩ := TauCeti.exists_norm_Gamma_vertical_line_le hσ
  obtain ⟨C₂, _, hG₂⟩ :=
    TauCeti.exists_norm_Gamma_add_I_le (w := (σ : ℂ) + p) (by simpa using hσp)
  set K : ℝ := (σ - 1 / 2) + (σ + p.re - 1 / 2)
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs K hα).const_mul
    (‖c‖ ^ (-σ) * C₁ * C₂)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have hcpow : ‖c ^ (-((σ : ℂ) + y * I))‖ ≤ ‖c‖ ^ (-σ) * Real.exp (|c.arg| * |y|) := by
    simpa using norm_cpow_le_mul_exp_arg c (-((σ : ℂ) + y * I))
  have hb₁ := hG₁ y
  have hb₂ := hG₂ y
  rw [add_right_comm, add_re, ofReal_re] at hb₂
  exact norm_cpow_neg_mul_Gamma_mul_Gamma_add_le hcpow hb₁ hb₂

/-! ### Residues at the two simple-pole lattices -/

/-- The residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at the pole `s = -k` (`k : ℕ`) is
`(-1) ^ k / k! * c ^ k * Γ(p - k)`, whenever `c ≠ 0` and `p - k` is not a nonpositive integer. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat {c p : ℂ} (hc : c ≠ 0) (k : ℕ)
    (hp : ∀ m : ℕ, p - k ≠ -m) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-(k : ℂ)) =
      (-1) ^ k / (k ! : ℂ) * c ^ k * Gamma (p - k) := by
  have hw : AnalyticAt ℂ (fun s ↦ c ^ (-s) * Gamma (s + p)) (-(k : ℂ)) :=
    ((differentiable_cpow_neg hc).analyticAt _).mul
      ((analyticAt_Gamma (fun m h ↦ hp m (by linear_combination h))).comp
        (f := fun s : ℂ ↦ s + p) (by fun_prop))
  have hfun : (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) =
      fun s ↦ Gamma s * (c ^ (-s) * Gamma (s + p)) := funext fun s ↦ by ring
  rw [hfun, residue_Gamma_mul_neg_nat k hw, neg_neg, cpow_natCast, neg_add_eq_sub]
  ring

/-- The residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at the pole `s = -p - k` (`k : ℕ`) is
`(-1) ^ k / k! * c ^ (p + k) * Γ(-p - k)`, whenever `-p - k` is not a nonpositive integer. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat {c p : ℂ} (k : ℕ)
    (hp : ∀ m : ℕ, -p - k ≠ -m) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-p - k) =
      (-1) ^ k / (k ! : ℂ) * c ^ (p + k) * Gamma (-p - k) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hne : -p - k ≠ 0 := by simpa using hp 0
    have hpk : p + k ≠ 0 := fun h ↦ hne (by linear_combination -h)
    have hzero : (fun s : ℂ ↦ (0 : ℂ) ^ (-s) * (Gamma s * Gamma (s + p))) =ᶠ[𝓝[≠] (-p - k)]
        fun _ ↦ 0 := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne)] with s hs
      simp [zero_cpow (neg_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs))]
    rw [TauCeti.Contour.residue_congr_nhdsNE hzero,
      TauCeti.Contour.residue_eq_zero_of_analyticAt analyticAt_const, zero_cpow hpk]
    simp
  have hw : AnalyticAt ℂ (fun w : ℂ ↦ c ^ (-(w - p)) * Gamma (w - p)) (-(k : ℂ)) :=
    (((differentiable_cpow_neg hc).analyticAt _).comp (f := fun w : ℂ ↦ w - p) (by fun_prop)).mul
      ((analyticAt_Gamma (fun m h ↦ hp m (by linear_combination h))).comp
        (f := fun w : ℂ ↦ w - p) (by fun_prop))
  have hfun : (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) =
      fun s ↦ Gamma (s + p) * (c ^ (-(s + p - p)) * Gamma (s + p - p)) :=
    funext fun s ↦ by rw [add_sub_cancel_right]; ring
  -- Align the shifted argument `-p - k + p` and exponent `-(-(k : ℂ) - p)`.
  have harg : -p - k + p = -(k : ℂ) := by ring
  have hpow : -(-(k : ℂ) - p) = p + k := by ring
  have hsub : -(k : ℂ) - p = -p - k := by ring
  rw [hfun, TauCeti.Contour.residue_comp_add_const
      (fun w : ℂ ↦ Gamma w * (c ^ (-(w - p)) * Gamma (w - p))) p,
    harg, residue_Gamma_mul_neg_nat k hw, hpow, hsub]
  ring

/-- For `p ∉ ℤ` and `c ≠ 0`, the residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at `s = -k` is
`(π / sin (π * p))` times the `k`-th term of `₀F₁(; 1 - p; c)`. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat_eq_regularizedHGFunCoeff
    {c p : ℂ} (hc : c ≠ 0) (hp : ∀ m : ℤ, p ≠ m) (k : ℕ) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-(k : ℂ)) =
      π / sin (π * p) * (regularizedHGFunCoeff 0 {1 - p} k * c ^ k) := by
  have hp_sub : ∀ m : ℕ, p - k ≠ -m := fun m h ↦
    hp ((k : ℤ) - m) (by push_cast; linear_combination h)
  have hsin_ne : sin (π * p) ≠ 0 :=
    sin_pi_mul_ne_zero (x := p) (not_exists.mpr fun m hm ↦ hp m hm.symm)
  have hrefl := neg_one_pow_div_factorial_mul_Gamma_sub_natCast hsin_ne k
  rw [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat hc k hp_sub,
    regularizedHGFunCoeff_zero_singleton, mul_right_comm, hrefl]
  ring

/-- For `p ∉ ℤ`, the residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at `s = -p - k` is
`-(π / sin (π * p)) * c ^ p` times the `k`-th term of `₀F₁(; 1 + p; c)`. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat_eq_regularizedHGFunCoeff
    {c p : ℂ} (hp : ∀ m : ℤ, p ≠ m) (k : ℕ) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-p - k) =
      -(π / sin (π * p) * (c ^ p * (regularizedHGFunCoeff 0 {1 + p} k * c ^ k))) := by
  have hp_neg : ∀ m : ℕ, -p - k ≠ -m := fun m h ↦
    hp ((m : ℤ) - k) (by push_cast; linear_combination -h)
  rcases eq_or_ne c 0 with rfl | hc
  · have hp0 : p ≠ 0 := by simpa using hp 0
    have hpk : p + k ≠ 0 := fun h ↦ hp (-k) (by push_cast; linear_combination h)
    rw [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat k hp_neg, zero_cpow hpk, zero_cpow hp0]
    simp
  have hsin_ne : sin (π * (-p)) ≠ 0 := by
    rw [mul_neg, sin_neg, neg_ne_zero]
    exact sin_pi_mul_ne_zero (x := p) (not_exists.mpr fun m hm ↦ hp m hm.symm)
  have hrefl := neg_one_pow_div_factorial_mul_Gamma_sub_natCast hsin_ne k
  rw [mul_neg, sin_neg, sub_neg_eq_add] at hrefl
  -- Group `(-1) ^ k / k! * Γ(-p - k)` so `hrefl` rewrites it directly.
  have hrearr : (-1 : ℂ) ^ k / (k ! : ℂ) * (c ^ p * c ^ k) * Gamma (-p - k) =
      c ^ p * c ^ k * ((-1 : ℂ) ^ k / (k ! : ℂ) * Gamma (-p - k)) := by ring
  rw [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat k hp_neg,
    cpow_add _ _ hc, cpow_natCast, regularizedHGFunCoeff_zero_singleton, hrearr, hrefl]
  ring

/-! ### Finite contour shift between two vertical lines -/

/-- Unfold `gammaPolesRightOf a σ₁ \ gammaPolesRightOf a σ₂` to a ceiling-interval image. -/
private lemma gammaPolesRightOf_sdiff (a : ℂ) (σ₁ σ₂ : ℝ) :
    gammaPolesRightOf a σ₁ \ gammaPolesRightOf a σ₂ =
      (Finset.Ico ⌈-(σ₂ + a.re)⌉₊ ⌈-(σ₁ + a.re)⌉₊).image fun k : ℕ ↦ -a - k := by
  ext t
  simp only [Finset.mem_sdiff, mem_gammaPolesRightOf, Finset.mem_image,
    TauCeti.mem_Ico_ceil_neg_iff, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨h₁, k, rfl⟩, h₂⟩
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · simp only [sub_re, neg_re, natCast_re] at h₁
      linarith
    · have hle : (-a - k).re ≤ σ₂ := not_lt.mp fun h ↦ h₂ ⟨h, k, rfl⟩
      simp only [sub_re, neg_re, natCast_re] at hle
      linarith
  · rintro ⟨k, ⟨h₁, h₂⟩, rfl⟩
    refine ⟨⟨by simp; linarith, k, rfl⟩, fun ⟨hlt, k', hk'⟩ ↦ ?_⟩
    have hre : (-a - k').re = (-a - k).re := congrArg re hk'.symm
    simp only [sub_re, neg_re, natCast_re] at hlt hre
    linarith

/-- Evaluation of the finite residue sum over the two disjoint pole families in `(σ₁, σ₂]`. -/
private lemma sum_residue_strip_cpow_neg_mul_Gamma_mul_Gamma_add
    {c p : ℂ} (hc : c ≠ 0) (hp : ∀ m : ℤ, p ≠ m) (σ₁ σ₂ : ℝ) :
    ∑ s ∈ (gammaPolesRightOf 0 σ₁ ∪ gammaPolesRightOf p σ₁) \
        (gammaPolesRightOf 0 σ₂ ∪ gammaPolesRightOf p σ₂),
        TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s =
      π / sin (π * p) *
        ((∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k) -
          c ^ p * ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
            regularizedHGFunCoeff 0 {1 + p} k * c ^ k) := by
  -- For `p ∉ ℤ`, the two pole lattices `-k` and `-p - k` never collide, so the sdiff splits.
  have hdisj_all : ∀ k₁ k₂ : ℕ, (-(k₁ : ℂ)) ≠ -p - k₂ := fun k₁ k₂ hk ↦
    hp ((k₁ : ℤ) - k₂) (by push_cast; linear_combination hk)
  have hsdiff_eq : (gammaPolesRightOf 0 σ₁ ∪ gammaPolesRightOf p σ₁) \
      (gammaPolesRightOf 0 σ₂ ∪ gammaPolesRightOf p σ₂) =
      (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
        (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k) := by
    have hsplit : (gammaPolesRightOf 0 σ₁ ∪ gammaPolesRightOf p σ₁) \
        (gammaPolesRightOf 0 σ₂ ∪ gammaPolesRightOf p σ₂) =
        (gammaPolesRightOf 0 σ₁ \ gammaPolesRightOf 0 σ₂) ∪
          (gammaPolesRightOf p σ₁ \ gammaPolesRightOf p σ₂) := by
      ext s
      simp only [Finset.mem_sdiff, Finset.mem_union, mem_gammaPolesRightOf]
      constructor
      · rintro ⟨⟨h₁, k, rfl⟩ | ⟨h₁, k, rfl⟩, h₂⟩
        · exact Or.inl ⟨⟨h₁, k, rfl⟩, fun h ↦ h₂ (Or.inl h)⟩
        · exact Or.inr ⟨⟨h₁, k, rfl⟩, fun h ↦ h₂ (Or.inr h)⟩
      · rintro (⟨⟨h₁, k, rfl⟩, h₂⟩ | ⟨⟨h₁, k, rfl⟩, h₂⟩)
        · refine ⟨Or.inl ⟨h₁, k, rfl⟩, ?_⟩
          rintro (h | ⟨_, k', hk'⟩)
          · exact h₂ h
          · exact hdisj_all k k' (by simpa using hk')
        · refine ⟨Or.inr ⟨h₁, k, rfl⟩, ?_⟩
          rintro (⟨_, k', hk'⟩ | h)
          · exact hdisj_all k' k (by simpa using hk'.symm)
          · exact h₂ h
    have hzero : (fun k : ℕ ↦ -(0 : ℂ) - k) = fun k : ℕ ↦ -(k : ℂ) :=
      funext fun k ↦ by simp
    rw [hsplit, gammaPolesRightOf_sdiff 0 σ₁ σ₂, gammaPolesRightOf_sdiff p σ₁ σ₂,
      zero_re, add_zero, add_zero, hzero]
  have hdisj : Disjoint
      ((Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)))
      ((Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    rcases Finset.mem_image.mp hs1 with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp hs2 with ⟨k₂, _, hk⟩
    exact hdisj_all k₁ k₂ hk.symm
  have hinj1 : Function.Injective (fun k : ℕ ↦ -(k : ℂ)) := fun _ _ h ↦
    Nat.cast_injective (neg_inj.mp h)
  have hinj2 : Function.Injective (fun k : ℕ ↦ -p - (k : ℂ)) := fun _ _ h ↦
    Nat.cast_injective (by linear_combination -h)
  rw [hsdiff_eq, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h ↦ hinj1 h),
    Finset.sum_image (fun _ _ _ _ h ↦ hinj2 h)]
  -- Evaluate each family's sum using the Euler-reflection residue formulas.
  have hsum1 : ∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊,
      TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) (-(k : ℂ)) =
      π / sin (π * p) *
        ∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦
      residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat_eq_regularizedHGFunCoeff hc hp k
  have hsum2 : ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
      TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) (-p - k) =
      -(π / sin (π * p) * (c ^ p *
        ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
          regularizedHGFunCoeff 0 {1 + p} k * c ^ k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦
      residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat_eq_regularizedHGFunCoeff hp k
  rw [hsum1, hsum2]
  ring

/-- **Raw finite contour shift for `Γ(s) Γ(s + p)`.** For `c ∈ Complex.slitPlane`, arbitrary
`p : ℂ` (including integers, where double poles can occur), and any two pole-avoiding abscissas
`σ₁ ≤ σ₂`, the difference of the vertical integrals along `Re s = σ₂` and `Re s = σ₁` equals
`2π` times the sum of residues of `c ^ (-s) * (Γ(s) * Γ(s + p))` over the union of the pole
sets in the open strip `(σ₁, σ₂)`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral_eq_sum_residue
    {c p : ℂ} (hc : c ∈ slitPlane) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (hσ₁ : ∀ n : ℕ, σ₁ ≠ -n) (hσ₁p : ∀ n : ℕ, σ₁ + p.re ≠ -n)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) :
    (∫ y : ℝ, c ^ (-(σ₂ + y * I)) * (Gamma (σ₂ + y * I) * Gamma (σ₂ + y * I + p))) -
      (∫ y : ℝ, c ^ (-(σ₁ + y * I)) * (Gamma (σ₁ + y * I) * Gamma (σ₁ + y * I + p))) =
        2 * π * ∑ s ∈
          (gammaPolesRightOf 0 σ₁ ∪ gammaPolesRightOf p σ₁) \
            (gammaPolesRightOf 0 σ₂ ∪ gammaPolesRightOf p σ₂),
            TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  set f : ℂ → ℂ := fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))
  set P : Finset ℂ :=
    (gammaPolesRightOf 0 σ₁ ∪ gammaPolesRightOf p σ₁) \
      (gammaPolesRightOf 0 σ₂ ∪ gammaPolesRightOf p σ₂)
  -- Check that `P` lies in the open strip `(σ₁, σ₂)` and `f` is differentiable off `P`.
  have hre_ne {σ : ℝ} (hσ0 : ∀ n : ℕ, σ ≠ -n) (hσp : ∀ n : ℕ, σ + p.re ≠ -n) {s : ℂ}
      (hs : ∃ k : ℕ, s = -0 - k ∨ s = -p - k) : s.re ≠ σ := by
    obtain ⟨k, rfl | rfl⟩ := hs
    · exact fun h ↦ hσ0 k (by simpa using h.symm)
    · exact fun h ↦ hσp k (by simp only [sub_re, neg_re, natCast_re] at h; linarith)
  have hP : ∀ s ∈ P, σ₁ < s.re ∧ s.re < σ₂ := fun s hs ↦ by
    rw [Finset.mem_sdiff, mem_gammaPolesRightOf_union, mem_gammaPolesRightOf_union] at hs
    obtain ⟨⟨h₁, hk⟩, h₂⟩ := hs
    exact ⟨h₁, lt_of_le_of_ne (not_lt.mp fun h ↦ h₂ ⟨h, hk⟩) (hre_ne hσ₂ hσ₂p hk)⟩
  have hdiff_closed : DifferentiableOn ℂ f ({t : ℂ | σ₁ ≤ t.re ∧ t.re ≤ σ₂} \ (↑P : Set ℂ)) := by
    intro s ⟨hs, hsP⟩
    have hpole {w : ℂ} (hw : ∀ k : ℕ, s + w = -k → ∃ m : ℕ, s = -0 - m ∨ s = -p - m) :
        ∀ k : ℕ, s + w ≠ -k := fun k hk ↦ by
      have hm := hw k hk
      refine hsP (Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨mem_gammaPolesRightOf_union.mpr
        ⟨lt_of_le_of_ne hs.1 (hre_ne hσ₁ hσ₁p hm).symm, hm⟩, fun h ↦ ?_⟩))
      exact (mem_gammaPolesRightOf_union.mp h).1.not_ge hs.2
    exact (differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add hc0
      (by simpa only [add_zero] using hpole (w := 0) fun k hk ↦ ⟨k, Or.inl (by simpa using hk)⟩)
      (hpole (w := p) fun k hk ↦ ⟨k, Or.inr (by linear_combination hk)⟩)).differentiableWithinAt
  obtain ⟨C, K, T₀, _, hstrip⟩ := exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_le hc0 σ₁ σ₂
  have hα : 0 < π - |c.arg| := sub_pos.mpr (abs_arg_lt_pi_of_mem_slitPlane hc)
  have hB : Tendsto (fun T : ℝ ↦ C * ((1 + |T|) ^ K * Real.exp (-((π - |c.arg|) * |T|))))
      atTop (𝓝 0) := by
    simpa using ((TauCeti.tendsto_one_add_abs_rpow_mul_exp_neg_mul_abs K hα).mono_left
      atTop_le_cocompact).const_mul C
  have hbound : ∀ᶠ (T : ℝ) in atTop, ∀ x ∈ Icc σ₁ σ₂,
      ‖f ((x : ℂ) + T * I)‖ ≤ C * ((1 + |T|) ^ K * Real.exp (-((π - |c.arg|) * |T|))) ∧
        ‖f ((x : ℂ) - T * I)‖ ≤ C * ((1 + |T|) ^ K * Real.exp (-((π - |c.arg|) * |T|))) := by
    filter_upwards [eventually_ge_atTop T₀] with T hT x hx
    refine ⟨hstrip x hx T (hT.trans (le_abs_self T)), ?_⟩
    simpa [f, sub_eq_add_neg, abs_neg] using
      hstrip x hx (-T) (by rw [abs_neg]; exact hT.trans (le_abs_self T))
  exact TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue_of_norm_le f hσ P hP
    hdiff_closed.continuousOn
    (hdiff_closed.mono (sdiff_subset_sdiff_left fun _ ⟨h1, h2⟩ ↦ ⟨h1.le, h2.le⟩))
    (fun s _ ↦ meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add hc0 s)
    (integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₂ hσ₂p)
    (integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₁ hσ₁p) hB hbound

/-- **Finite contour shift for `Γ(s) Γ(s + p)`.** For `c ∈ Complex.slitPlane`, `p ∉ ℤ`, and any
two pole-avoiding abscissas `σ₁ ≤ σ₂`, the difference of the vertical integrals along `Re s = σ₂`
and `Re s = σ₁` equals `2π` times the sum of residues of `c ^ (-s) * (Γ(s) * Γ(s + p))` at the
poles in the open strip `(σ₁, σ₂)`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral
    {c p : ℂ} (hc : c ∈ slitPlane) (hp : ∀ m : ℤ, p ≠ m)
    {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (hσ₁ : ∀ n : ℕ, σ₁ ≠ -n) (hσ₁p : ∀ n : ℕ, σ₁ + p.re ≠ -n)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) :
    (∫ y : ℝ, c ^ (-(σ₂ + y * I)) * (Gamma (σ₂ + y * I) * Gamma (σ₂ + y * I + p))) -
      (∫ y : ℝ, c ^ (-(σ₁ + y * I)) * (Gamma (σ₁ + y * I) * Gamma (σ₁ + y * I + p))) =
        2 * π * (π / sin (π * p) *
          ((∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k) -
            c ^ p * ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
              regularizedHGFunCoeff 0 {1 + p} k * c ^ k)) := by
  rw [integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral_eq_sum_residue hc hσ hσ₁ hσ₁p hσ₂ hσ₂p,
    sum_residue_strip_cpow_neg_mul_Gamma_mul_Gamma_add (slitPlane_ne_zero hc) hp σ₁ σ₂]

/-! ### Vanishing of the shifted vertical integral as `Re s → -∞` -/

/-- The negation of a point in `(0, 1)` is never an integer. -/
private lemma neg_ne_intCast_of_mem_Ioo_zero_one {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    -(δ : ℝ) ≠ m := fun hm ↦ by
  have h1 : m < 0 := by exact_mod_cast (by linarith [hδ.1] : (m : ℝ) < 0)
  have h2 : (-1 : ℤ) < m := by exact_mod_cast (by linarith [hδ.2] : (-1 : ℝ) < m)
  omega

/-- Uniform pointwise factorial/exponential bound on the left-shifted vertical line
`Re s = -N - δ` for `N ≥ ⌈p.re - δ⌉₊`. -/
private lemma exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_sub_natCast_le
    {c p : ℂ} (hc : c ∈ slitPlane) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hpδ : ∀ m : ℤ, p.re - δ ≠ m) :
    ∃ C₀ > 0, ∀ ⦃N : ℕ⦄, ⌈p.re - δ⌉₊ ≤ N → ∀ y : ℝ,
      ‖c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
          (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p))‖ ≤
        C₀ * (‖c‖ ^ N / (N ! : ℝ)) * Real.exp (-((π - |c.arg|) * |y|)) := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  obtain ⟨C₁, hC₁, hG₁⟩ :=
    TauCeti.exists_norm_Gamma_sub_natCast_le (neg_ne_intCast_of_mem_Ioo_zero_one hδ)
  obtain ⟨C₂, hC₂, hG₂⟩ := TauCeti.exists_norm_Gamma_sub_natCast_le hpδ
  have hceil₀ : ⌈-δ⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith [hδ.1])
  set M : ℕ := ⌈p.re - δ⌉₊
  refine ⟨‖c‖ ^ δ * (C₁ * (C₂ * Real.exp (π * |p.im| / 2))), by positivity, fun N hMN y ↦ ?_⟩
  set s : ℂ := ((-(N : ℝ) - δ : ℝ) : ℂ) + y * I
  -- 1. Exponential-in-`|y|` and `‖c‖ ^ N` bound on `‖c ^ (-s)‖`.
  have hcpow : ‖c ^ (-s)‖ ≤ ‖c‖ ^ δ * ‖c‖ ^ N * Real.exp (|c.arg| * |y|) := by
    refine (norm_cpow_le_mul_exp_arg c (-s)).trans_eq ?_
    have hre : (-s).re = δ + (N : ℝ) := by
      simp only [s, neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
      ring
    have him : |(-s).im| = |y| := by
      simp only [s, neg_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_one, mul_zero, add_zero, zero_add, abs_neg]
    rw [hre, him, Real.rpow_add (norm_pos_iff.mpr hc0), Real.rpow_natCast]
  -- 2. Left-shift Gamma bounds on `‖Γ(s)‖` (with `1 / N!`) and `‖Γ(s + p)‖`.
  have hb₁ : ‖Gamma s‖ ≤ C₁ / (N ! : ℝ) * (1 + |y|) ^ (0 : ℝ) * Real.exp (-(π * |y| / 2)) := by
    rw [Real.rpow_zero, mul_one]
    have h := hG₁ (N := N) (hceil₀ ▸ Nat.zero_le N) y
    rw [hceil₀, Nat.sub_zero] at h
    refine h.trans_eq' (congrArg (fun z ↦ ‖Gamma z‖) ?_)
    simp only [s]; push_cast; ring
  have hb₂ : ‖Gamma (s + p)‖ ≤
      (C₂ * Real.exp (π * |p.im| / 2)) * (1 + |y|) ^ (0 : ℝ) * Real.exp (-(π * |y| / 2)) := by
    rw [Real.rpow_zero, mul_one]
    have h := hG₂ hMN (y + p.im)
    -- Align `(p.re - δ : ℂ) - N + (y + p.im) * I` with `s + p` so `hG₂` applies.
    have harg : ((p.re - δ : ℝ) : ℂ) - N + (y + p.im : ℝ) * I = s + p := by
      dsimp [s]
      conv_rhs => rw [← re_add_im p]
      push_cast
      ring
    rw [harg] at h
    have hfac1 : (1 : ℝ) ≤ (Nat.factorial (N - M) : ℝ) :=
      by exact_mod_cast Nat.factorial_pos (N - M)
    have htri : |y| - |p.im| ≤ |y + p.im| := by
      simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub y (-p.im)
    have hexp_tri : Real.exp (-(π * |y + p.im| / 2)) ≤
        Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [pi_pos, htri])
    calc ‖Gamma (s + p)‖
        ≤ C₂ / (Nat.factorial (N - M) : ℝ) * Real.exp (-(π * |y + p.im| / 2)) := h
      _ ≤ C₂ * (Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2))) :=
          mul_le_mul (div_le_self hC₂.le hfac1) hexp_tri (Real.exp_pos _).le hC₂.le
      _ = C₂ * Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2)) := by ring
  -- 3. Combine the factors using `norm_cpow_neg_mul_Gamma_mul_Gamma_add_le`.
  have hcomb := norm_cpow_neg_mul_Gamma_mul_Gamma_add_le hcpow hb₁ hb₂
  rw [add_zero, Real.rpow_zero, one_mul] at hcomb
  exact hcomb.trans_eq (by ring)

/-- For `δ ∈ (0, 1)` with `p.re - δ ∉ ℤ`, the shifted abscissa `-N - δ` avoids both `-ℕ` and
`-p.re - ℕ`. -/
private lemma left_shift_avoids_poles {p : ℂ} {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hpδ : ∀ m : ℤ, p.re - δ ≠ m) (N : ℕ) :
    (∀ n : ℕ, -(N : ℝ) - δ ≠ -n) ∧ (∀ n : ℕ, -(N : ℝ) - δ + p.re ≠ -n) :=
  ⟨fun n h ↦ neg_ne_intCast_of_mem_Ioo_zero_one hδ ((N : ℤ) - n) (by push_cast; linarith),
   fun n h ↦ hpδ ((N : ℤ) - n) (by push_cast; linarith)⟩

/-- For a fixed offset `δ ∈ (0, 1)` with `p.re - δ ∉ ℤ`, the vertical integral along
`Re s = -N - δ` tends to `0` as `N → ∞`, with bound `O(‖c‖ ^ N / N!)`. -/
private lemma tendsto_integral_cpow_neg_mul_Gamma_mul_Gamma_add_left
    {c p : ℂ} (hc : c ∈ slitPlane) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hpδ : ∀ m : ℤ, p.re - δ ≠ m) :
    Tendsto (fun N : ℕ ↦ ∫ y : ℝ,
        c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
          (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p)))
      atTop (𝓝 0) := by
  set α : ℝ := π - |c.arg|
  have hα : 0 < α := sub_pos.mpr (abs_arg_lt_pi_of_mem_slitPlane hc)
  obtain ⟨C₀, _, hpt⟩ := exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_sub_natCast_le hc hδ hpδ
  refine squeeze_zero_norm' ?_ (by simpa using
    ((Real.summable_pow_div_factorial ‖c‖).tendsto_atTop_zero.const_mul C₀).mul_const (2 / α))
  filter_upwards [eventually_ge_atTop ⌈p.re - δ⌉₊] with N hMN
  have ⟨hσ₁, hσ₁p⟩ := left_shift_avoids_poles hδ hpδ N
  refine (norm_integral_le_integral_norm _).trans ((integral_mono
    ((integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₁ hσ₁p).norm)
    ((TauCeti.integrable_exp_neg_mul_abs hα).const_mul _) (hpt hMN)).trans_eq ?_)
  rw [integral_const_mul, TauCeti.integral_exp_neg_mul_abs hα]

/-! ### Main Mellin–Barnes evaluation -/

/-- Partial sums of `regularizedHGFunCoeff 0 {b} k * c ^ k` up to `⌈N + a⌉₊` converge to
`regularizedHGFun 0 {b} c` as `N → ∞`. -/
private lemma tendsto_sum_range_ceil_regularizedHGFunCoeff (b c : ℂ) (a : ℝ) :
    Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range ⌈(N : ℝ) + a⌉₊,
        regularizedHGFunCoeff 0 {b} k * c ^ k)
      atTop (𝓝 (regularizedHGFun 0 {b} c)) :=
  (hasSum_regularizedHGFun (a := 0) (b := {b}) (by simp) c).tendsto_sum_nat.comp
    (tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))

/-- **Mellin–Barnes integral of `Γ(s) Γ(s + p)` on the slit plane.** For `c ∈ Complex.slitPlane`,
`p ∉ ℤ`, and any abscissa `σ` with `0 < σ` and `0 < σ + Re p`,
`∫ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p) dy` equals
`2π (π / sin (π p)) (₀F₁(; 1 - p; c) - c ^ p · ₀F₁(; 1 + p; c))`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_add
    {c p : ℂ} (hc : c ∈ slitPlane) (hp : ∀ m : ℤ, p ≠ m)
    {σ : ℝ} (hσ : 0 < σ) (hσp : 0 < σ + p.re) :
    ∫ y : ℝ, c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p)) =
      2 * π * (π / sin (π * p) *
        (regularizedHGFun 0 {1 - p} c - c ^ p * regularizedHGFun 0 {1 + p} c)) := by
  -- 1. Choose a pole-avoiding offset `δ ∈ (0, 1)` for the left-shifted contours `Re s = -N - δ`.
  obtain ⟨δ, hδ, hpδ⟩ := TauCeti.exists_mem_Ioo_zero_one_sub_ne_intCast p.re
  set Iσ : ℂ := ∫ y : ℝ, c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p))
  set IN : ℕ → ℂ := fun N ↦
    ∫ y : ℝ, c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
      (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p))
  -- 2. Express `Iσ - IN N` as the finite residue sum between `-N - δ` and `σ`.
  have hshift : ∀ N : ℕ, Iσ - IN N =
      2 * π * (π / sin (π * p) *
        ((∑ k ∈ Finset.range ⌈(N : ℝ) + δ⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k) -
          c ^ p * ∑ k ∈ Finset.range ⌈(N : ℝ) + (δ - p.re)⌉₊,
            regularizedHGFunCoeff 0 {1 + p} k * c ^ k)) := by
    intro N
    have ⟨hσ₁, hσ₁p⟩ := left_shift_avoids_poles hδ hpδ N
    have h := integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral hc hp
      (by linarith [N.cast_nonneg (α := ℝ), hδ.1] : -(N : ℝ) - δ ≤ σ)
      hσ₁ hσ₁p
      (fun n h ↦ by linarith [n.cast_nonneg (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg (α := ℝ)])
    have hc1 : ⌈-σ⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    have hc2 : ⌈-(σ + p.re)⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    -- Rewrite the ceiling cutoffs into `(N : ℝ) + a` for
    -- `tendsto_sum_range_ceil_regularizedHGFunCoeff`.
    have ha1 : -(-(N : ℝ) - δ) = (N : ℝ) + δ := by ring
    have ha2 : -((-(N : ℝ) - δ) + p.re) = (N : ℝ) + (δ - p.re) := by ring
    rw [ha1, ha2, hc1, hc2, Nat.Ico_zero_eq_range, Nat.Ico_zero_eq_range] at h
    exact h
  -- 3. Pass to the limit `N → ∞`: `IN N → 0` on the LHS, while the partial sums give `₀F₁`.
  have hlim_lhs : Tendsto (fun N : ℕ ↦ Iσ - IN N) atTop (𝓝 Iσ) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (tendsto_integral_cpow_neg_mul_Gamma_mul_Gamma_add_left hc hδ hpδ)
  have hlim_rhs : Tendsto (fun N : ℕ ↦ Iσ - IN N) atTop
      (𝓝 (2 * π * (π / sin (π * p) *
        (regularizedHGFun 0 {1 - p} c - c ^ p * regularizedHGFun 0 {1 + p} c)))) := by
    have hsum1 := tendsto_sum_range_ceil_regularizedHGFunCoeff (1 - p) c δ
    have hsum2 := tendsto_sum_range_ceil_regularizedHGFunCoeff (1 + p) c (δ - p.re)
    simpa only [← hshift] using
      ((hsum1.sub (hsum2.const_mul (c ^ p))).const_mul (π / sin (π * p))).const_mul (2 * (π : ℂ))
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

/-- **Mellin inversion of `Γ(s) Γ(s + p)` as a regularized hypergeometric difference.** For
`p ∉ ℤ`, `0 < σ`, `0 < σ + Re p`, and real `c > 0`,
`mellinInv σ (fun s ↦ Γ(s) Γ(s + p)) c` equals
`(π / sin (π p)) (₀F₁(; 1 - p; c) - c ^ p · ₀F₁(; 1 + p; c))`. -/
theorem mellinInv_Gamma_mul_Gamma_add_eq_regularizedHGFun
    {p : ℂ} (hp : ∀ m : ℤ, p ≠ m)
    {σ : ℝ} (hσ : 0 < σ) (hσp : 0 < σ + p.re)
    {c : ℝ} (hc : 0 < c) :
    mellinInv σ (fun s ↦ Gamma s * Gamma (s + p)) c =
      π / sin (π * p) *
        (regularizedHGFun 0 {1 - p} c - (c : ℂ) ^ p * regularizedHGFun 0 {1 + p} c) := by
  have h := integral_cpow_neg_mul_Gamma_mul_Gamma_add (ofReal_mem_slitPlane.mpr hc) hp hσ hσp
  rw [mellinInv, real_smul]
  simp_rw [smul_eq_mul]
  rw [h]
  have hpi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)
  push_cast
  field_simp [hpi]

end Complex

end
