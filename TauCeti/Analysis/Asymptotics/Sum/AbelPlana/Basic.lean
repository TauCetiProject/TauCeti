/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import TauCeti.Analysis.Complex.VerticalStrip.Growth
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The Abel–Plana summation formula

For integers `a ≤ n` and a function `f : ℂ → ℂ` holomorphic on the open vertical strip
`a < Re z < n` and continuous on its closure `a ≤ Re z ≤ n`, with `f(z) = o(e^{2π|Im z|})` as
`|Im z| → ∞` uniformly in the strip:

* If the two boundary integrands `y ↦ (f(c + iy) - f(c - iy)) / (e^{2πy} - 1)` are integrable on
  `(0, ∞)` at `c = a` and `c = n`, the general complex Abel–Plana formula
  (`TauCeti.sum_Icc_eq_abelPlana_sub`) expresses `∑_{j=a}^n f(j)` through `∫_a^n f`, the
  half-endpoint terms `(f(a) + f(n)) / 2`, and the two improper integrals along the vertical
  boundary lines `Re z = a` and `Re z = n` against `(e^{2πy} - 1)⁻¹`.
* If in addition `f` is real on `[a, n]` and the two boundary integrands
  `y ↦ Im f(c + iy) / (e^{2πy} - 1)` are integrable on `(0, ∞)` at `c = a` and `c = n`, Schwarz
  reflection symmetry (`TauCeti.apply_conj_eq_conj_of_im_eq_zero_on_strip`, imported from
  `TauCeti.Analysis.Complex.Conformal.Reflection.Principle`) specializes this to the classical real
  form (`TauCeti.sum_Icc_eq_abelPlana`).

Compared with the Euler–Maclaurin formula (`TauCeti.sum_Icc_eq_eulerMaclaurin`), the correction is
controlled by the growth of `f` on the vertical lines rather than by real higher derivatives on
`[a, n]`. The companion module `TauCeti.Analysis.Asymptotics.Sum.AbelPlana.Bernoulli` expands the
vertical-line integral in powers of `y` to recover the Bernoulli derivative series with an
exponentially damped vertical-line remainder.

## Main results

* `TauCeti.sum_Icc_eq_abelPlana_sub`: the general complex Abel–Plana formula (without assuming `f`
  is real on `[a, n]`), assuming `(f(c + i y) - f(c - i y)) / (e^{2πy} - 1)` is integrable on
  `(0, ∞)` at `c = a` and `c = n`.
* `TauCeti.sum_Icc_eq_abelPlana`: the exact Abel–Plana formula (DLMF 2.10.2) for `f` real on
  `[a, n]`, assuming `Im f(c + i y) / (e^{2πy} - 1)` is integrable on `(0, ∞)` at `c = a` and
  `c = n`.
* `TauCeti.tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le`: growth criterion verifying the uniform
  `o(e^{2π|Im z|})` hypothesis when `‖f z‖ ≤ C * (1 + |z.im|) ^ p * e^{c |z.im|}` eventually as
  `|Im z| → ∞` in the strip with `c < 2 * π`.

## Proof strategy

Fix `0 < ε < 1 / 2` and `T > ε`. Apply Cauchy's rectangle theorem to
`g₊(z) = f(z) / (e^{-2πiz} - 1)` on `[a, n] × [ε, T]` and on the `n - a` pole-free bottom strips
`[j + ε, j + 1 - ε] × [0, ε]` (`j ∈ [a, n)`). Applying the same finite-`(ε, T)` identity to the
Schwarz conjugate `z ↦ conj (f (conj z))` and taking complex conjugates supplies the lower
half-plane identity for `g₋(z) = f(z) / (e^{2πiz} - 1)` without duplicating any contour estimate.
Adding the two equations cancels the poles along `(j + ε, j + 1 - ε)` via
`1 / (w - 1) + 1 / (w⁻¹ - 1) = -1` and pairs the vertical boundary integrals into
`(f(c + i y) - f(c - i y)) / (e^{2πy} - 1)`. Sending `T → +∞` and then `ε → 0⁺` evaluates each
quarter-box indent around an integer `k` to `f(k) / 4` via `Complex.log` on `Complex.slitPlane`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(i), formula 2.10.2.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §3.2–3.3.
-/

public section

open Complex Filter intervalIntegral MeasureTheory Set
open scoped ComplexConjugate Interval Nat Real Topology

namespace TauCeti

/-! ### Kernel identities and pole avoidance -/

/-- Upper-half-plane Abel–Plana integrand `f(z) / (e^{-2πiz} - 1)`. -/
private noncomputable def abelPlanaUpper (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / (cexp (-2 * π * I * z) - 1)

/-- The nonzero constant `-2 * π * I`. -/
private theorem neg_two_pi_I_ne_zero : (-2 * π * I : ℂ) ≠ 0 := by
  simp [neg_mul]

/-- `e^{-2πiz} ≠ 1` off the real axis. -/
private theorem cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    cexp (-2 * π * I * z) ≠ 1 := fun h => by
  obtain ⟨m, rfl⟩ := Complex.exp_neg_two_pi_mul_I_mul_eq_one_iff.mp h
  exact hz (intCast_im m)

/-- `e^{-2πiz} ≠ 1` whenever `Re z` lies strictly between two consecutive integers. -/
private theorem cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo {z : ℂ} (j : ℤ)
    (hz : z.re ∈ Ioo (j : ℝ) (j + 1)) : cexp (-2 * π * I * z) ≠ 1 := fun h => by
  obtain ⟨m, rfl⟩ := Complex.exp_neg_two_pi_mul_I_mul_eq_one_iff.mp h
  have h1 : (j : ℝ) < m := by simpa using hz.1
  have h2 : (m : ℝ) < (j + 1 : ℤ) := by push_cast; simpa using hz.2
  have : j < m := by exact_mod_cast h1
  have : m < j + 1 := by exact_mod_cast h2
  omega

/-- On `(j, j + 1)`, combining `g₊` with the conjugate of `g₊` for `conj ∘ f ∘ conj` gives
`-f(x)`. -/
private theorem abelPlanaUpper_add_conj_comp (f : ℂ → ℂ) {x : ℝ} (j : ℤ)
    (hx : x ∈ Ioo (j : ℝ) (j + 1)) :
    abelPlanaUpper f x + conj (abelPlanaUpper (fun z => conj (f (conj z))) x) = -f x := by
  dsimp only [abelPlanaUpper]
  simp only [map_div₀, map_sub, map_one, map_ofNat, Complex.conj_ofReal, starRingEnd_self_apply,
    ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I]
  set w : ℂ := cexp (-2 * π * I * (x : ℂ))
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr
    (cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j (by simpa using hx))
  have hw1' : 1 - w ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hw1).symm
  have hpos : cexp (-2 * ↑π * -I * ↑x) = w⁻¹ := by rw [← Complex.exp_neg]; congr 1; ring
  rw [hpos]
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have : w⁻¹ - 1 ≠ 0 := fun h0 => hw1 (sub_eq_zero.mpr (inv_eq_one.mp (sub_eq_zero.mp h0)))
  field_simp
  ring

/-! ### Finite-`(ε, T)` upper contour identity -/

/-- Upper-right quarter-box indent around an integer `k`: horizontal top `[k, k + ε] + iε` minus
vertical right `k + ε + i[0, ε]`. -/
private noncomputable def upperRightCap (f : ℂ → ℂ) (k : ℤ) (ε : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((k : ℂ) + t + ε * I)) -
    I * (∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((k : ℂ) + ε + y * I))

/-- Upper-left quarter-box indent around an integer `k`: horizontal top `[k - ε, k] + iε` plus
vertical left `k - ε + i[0, ε]`. -/
private noncomputable def upperLeftCap (f : ℂ → ℂ) (k : ℤ) (ε : ℝ) : ℂ :=
  (∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f ((k : ℂ) + t + ε * I)) +
    I * (∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((k : ℂ) - ε + y * I))

/-- Cauchy's rectangle theorem for `abelPlanaUpper f` on any pole-free subrectangle
`[x₁, x₂] × [y₁, y₂]` of the strip `a ≤ Re z ≤ n`. -/
private theorem cauchy_rect_abelPlanaUpper {f : ℂ → ℂ} {a n : ℤ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx1 : (a : ℝ) ≤ x₁) (hx12 : x₁ ≤ x₂) (hx2 : x₂ ≤ n) (hy12 : y₁ ≤ y₂)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hne : ∀ z ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂, cexp (-2 * π * I * z) ≠ 1) :
    ((∫ x in x₁..x₂, abelPlanaUpper f (x + y₁ * I)) -
      ∫ x in x₁..x₂, abelPlanaUpper f (x + y₂ * I)) +
      I * (∫ y in y₁..y₂, abelPlanaUpper f (x₂ + y * I)) -
      I * (∫ y in y₁..y₂, abelPlanaUpper f (x₁ + y * I)) = 0 := by
  let z₀ : ℂ := x₁ + y₁ * I
  let w₀ : ℂ := x₂ + y₂ * I
  have hz : z₀.re = x₁ ∧ z₀.im = y₁ ∧ w₀.re = x₂ ∧ w₀.im = y₂ := by simp [z₀, w₀]
  rcases hz with ⟨hzre, hzim, hwre, hwim⟩
  have hbox : ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) = Icc x₁ x₂ ×ℂ Icc y₁ y₂ := by
    rw [hzre, hwre, hzim, hwim, uIcc_of_le hx12, uIcc_of_le hy12]
  have hne' : ∀ z ∈ ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]), cexp (-2 * π * I * z) - 1 ≠ 0 :=
    fun z hz => sub_ne_zero.mpr (hne z (hbox ▸ hz))
  have hcont_r : ContinuousOn (abelPlanaUpper f) ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) :=
    (hcont.mono fun z hz => by rw [hbox] at hz; exact ⟨hx1.trans hz.1.1, hz.1.2.trans hx2⟩).div
      (by fun_prop) hne'
  have hopen : (Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ
      Ioo (min z₀.im w₀.im) (max z₀.im w₀.im)) = Ioo x₁ x₂ ×ℂ Ioo y₁ y₂ := by
    rw [hzre, hwre, hzim, hwim, min_eq_left hx12, max_eq_right hx12,
      min_eq_left hy12, max_eq_right hy12]
  have hdiff_r : DifferentiableOn ℂ (abelPlanaUpper f)
      (Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ
        Ioo (min z₀.im w₀.im) (max z₀.im w₀.im)) := by
    refine (hf.mono fun z hz => ?_).div (by fun_prop) fun z hz => hne' z ?_
    · rw [hopen] at hz; exact ⟨hx1.trans_lt hz.1.1, hz.1.2.trans_le hx2⟩
    · rw [hbox]; rw [hopen] at hz; exact ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
  simpa only [hzre, hzim, hwre, hwim, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (abelPlanaUpper f) z₀ w₀ hcont_r hdiff_r

/-- Continuity of `x ↦ abelPlanaUpper f (x + ε * I)` across `[a, n]` for `ε ≠ 0`. -/
private theorem continuousOn_abelPlanaUpper_add_mul_I {f : ℂ → ℂ} {a n : ℤ} {ε : ℝ}
    (hε0 : ε ≠ 0) (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    ContinuousOn (fun x : ℝ => abelPlanaUpper f (x + ε * I)) (Icc (a : ℝ) n) :=
  (hcont.comp (by fun_prop) fun x hx => ⟨by simp [hx.1], by simp [hx.2]⟩).div (by fun_prop)
    fun _ _ => sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by simp [hε0]))

/-- Rewriting a horizontal unit segment `∫_{j}^{j+1} g₊(x + iε) dx` via Cauchy's theorem on the
pole-free bottom rectangle `[j + ε, j + 1 - ε] × [0, ε]`. -/
private theorem upper_unit_strip_eq {f : ℂ → ℂ} {a n j : ℤ} {ε : ℝ}
    (hj : j ∈ Finset.Ico a n) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    ∫ x in (j : ℝ)..(j + 1), abelPlanaUpper f (x + ε * I) =
      (∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
        upperRightCap f j ε + upperLeftCap f (j + 1) ε := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hle1 : (j : ℝ) + ε ≤ (j : ℝ) + 1 - ε := by linarith
  have hcauchy := cauchy_rect_abelPlanaUpper (by linarith) hle1 (by linarith) hε0.le hf hcont
    fun z hz => cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j
      ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hcauchy
  have hcont_line : ContinuousOn (fun x : ℝ => abelPlanaUpper f (x + ε * I))
      (Icc (j : ℝ) ((j : ℝ) + 1)) :=
    (continuousOn_abelPlanaUpper_add_mul_I hε0.ne' hcont).mono (Icc_subset_Icc hja' hjn')
  have hint1 := (hcont_line.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc
    (μ := volume) (by linarith : (j : ℝ) ≤ (j : ℝ) + ε)
  have hint2 := (hcont_line.mono (Icc_subset_Icc (by linarith)
    (by linarith))).intervalIntegrable_of_Icc (μ := volume) hle1
  have hint3 := (hcont_line.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc
    (μ := volume) (by linarith : (j : ℝ) + 1 - ε ≤ (j : ℝ) + 1)
  rw [← integral_add_adjacent_intervals (hint1.trans hint2) hint3,
    ← integral_add_adjacent_intervals hint1 hint2]
  have hshiftR : ∫ x in (j : ℝ)..((j : ℝ) + ε), abelPlanaUpper f (x + ε * I) =
      ∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + t + ε * I) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (integral_comp_add_right (fun x : ℝ => abelPlanaUpper f (x + ε * I)) (j : ℝ)
        (a := 0) (b := ε)).symm
  have hshiftL : ∫ x in ((j : ℝ) + 1 - ε)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I) =
      ∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + t + ε * I) := by
    have h := (integral_comp_add_right (fun x : ℝ => abelPlanaUpper f (x + ε * I))
      ((j : ℝ) + 1) (a := -ε) (b := 0)).symm
    rw [neg_add_eq_sub, zero_add] at h
    exact h.trans (integral_congr fun t _ => by congr 1; push_cast; ring)
  have hcastR : (∫ y in (0 : ℝ)..ε, abelPlanaUpper f (↑((j : ℝ) + ε) + ↑y * I)) =
      ∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ε + y * I) :=
    integral_congr fun y _ => by congr 1; push_cast; ring
  have hcastL : (∫ y in (0 : ℝ)..ε, abelPlanaUpper f (↑((j : ℝ) + 1 - ε) + ↑y * I)) =
      ∫ y in (0 : ℝ)..ε, abelPlanaUpper f (((j + 1 : ℤ) : ℂ) - ε + y * I) :=
    integral_congr fun y _ => by congr 1; push_cast; ring
  rw [hcastR, hcastL] at hcauchy
  rw [hshiftR, hshiftL]
  dsimp only [upperRightCap, upperLeftCap]
  linear_combination -hcauchy

/-- Finite-`(ε, T)` upper contour identity combining `[a, n] × [ε, T]` with the `n - a` bottom
strips `[j + ε, j + 1 - ε] × [0, ε]`. -/
private theorem upper_rect_identity {f : ℂ → ℂ} {a n : ℤ} {ε T : ℝ}
    (han : a < n) (hε0 : 0 < ε) (hε2 : ε < 1 / 2) (hεT : ε ≤ T)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    (∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
      (∑ j ∈ Finset.Ico a n, (upperRightCap f j ε + upperLeftCap f (j + 1) ε)) =
      (∫ x in (a : ℝ)..n, abelPlanaUpper f (x + T * I)) +
        I * (∫ y in ε..T, f (a + y * I) / (Real.exp (2 * π * y) - 1)) -
        I * (∫ y in ε..T, f (n + y * I) / (Real.exp (2 * π * y) - 1)) := by
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han.le
  have hcauchy := cauchy_rect_abelPlanaUpper le_rfl han' le_rfl hεT hf hcont fun z hz =>
    cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by linarith [hz.2.1])
  simp only [Complex.ofReal_intCast] at hcauchy
  have hcont_line := continuousOn_abelPlanaUpper_add_mul_I hε0.ne' hcont
  have hsum_units :
      (∑ j ∈ Finset.Ico a n, ∫ x in (j : ℝ)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I)) =
        (∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
          ∑ j ∈ Finset.Ico a n, (upperRightCap f j ε + upperLeftCap f (j + 1) ε) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj => by
      rw [upper_unit_strip_eq hj hε0 hε2 hf hcont, add_assoc]
  have hsplit : ∫ x in (a : ℝ)..n, abelPlanaUpper f (x + ε * I) =
      ∑ j ∈ Finset.Ico a n, ∫ x in (j : ℝ)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I) := by
    have hsum := TauCeti.intervalIntegral.sum_integral_adjacent_intervals_Ico_int han.le
      (fun j : ℤ => (j : ℝ)) fun j hj => by
        obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
        simpa [Int.cast_add, Int.cast_one] using
          (hcont_line.mono (Icc_subset_Icc (by exact_mod_cast hja)
            (by exact_mod_cast hjn))).intervalIntegrable_of_Icc
              (μ := volume) (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)
    simpa [Int.cast_add, Int.cast_one] using hsum.symm
  have hvert : ∀ k : ℤ, (∫ y in ε..T, abelPlanaUpper f (k + y * I)) =
      ∫ y in ε..T, f (k + y * I) / (Real.exp (2 * π * y) - 1) :=
    fun k => integral_congr fun y _ => by
      dsimp only [abelPlanaUpper]; rw [Complex.exp_neg_two_pi_mul_I_mul_intCast_add_mul_I]
  rw [hvert a, hvert n, hsplit, hsum_units] at hcauchy
  linear_combination hcauchy

/-! ### Horizontal decay as `T → +∞` and quarter-box limits as `ε → 0⁺` -/

/-- The top horizontal integral `∫_a^n g₊(x + iT) dx` vanishes as `T → +∞` under `hgrowth`. -/
private theorem tendsto_integral_abelPlanaUpper_atTop {f : ℂ → ℂ} {a n : ℤ} (han : a ≤ n)
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x in (a : ℝ)..n, abelPlanaUpper f (x + T * I)) atTop (𝓝 0) := by
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  have hlen_pos : 0 < (n : ℝ) - a + 1 := by linarith
  have h1exp : 0 < 1 - Real.exp (-(2 * π)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.two_pi_pos))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hmem := hgrowth.eventually (Metric.ball_mem_nhds 0
    (by positivity : 0 < δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1)))
  rw [Filter.eventually_inf_principal, Filter.eventually_comap] at hmem
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hmem
  refine Filter.eventually_atTop.mpr ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  rw [dist_zero_right]
  have hbound : ∀ x ∈ Ioc (a : ℝ) n, ‖abelPlanaUpper f (x + T * I)‖ ≤ δ / ((n : ℝ) - a + 1) := by
    intro x hx
    set z : ℂ := (x : ℂ) + (T : ℂ) * I
    have hz_im : |z.im| = T := by simp [z, abs_of_pos hTpos]
    have hsmall : ‖f z‖ * Real.exp (-(2 * π * T)) ≤
        δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1) := by
      have h := (hT₀ T ((le_max_left _ _).trans hT) z hz_im
        ⟨by simp [z, hx.1.le], by simp [z, hx.2]⟩).le
      rwa [hz_im, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le] at h
    have hden_ge : Real.exp (2 * π * T) - 1 ≤ ‖cexp (-2 * π * I * z) - 1‖ := by
      simpa [Complex.norm_exp, z] using norm_sub_norm_le (cexp (-2 * π * I * z)) 1
    have hden_pos : 0 < Real.exp (2 * π * T) - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
    have h1T : 1 - Real.exp (-(2 * π)) ≤ 1 - Real.exp (-(2 * π * T)) :=
      sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) 1
    have hfac : (Real.exp (2 * π * T) - 1) * Real.exp (-(2 * π * T)) =
        1 - Real.exp (-(2 * π * T)) := by
      rw [sub_mul, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [abelPlanaUpper, norm_div]
    calc
      ‖f z‖ / ‖cexp (-2 * π * I * z) - 1‖ ≤ ‖f z‖ / (Real.exp (2 * π * T) - 1) := by gcongr
      _ = (‖f z‖ * Real.exp (-(2 * π * T))) / (1 - Real.exp (-(2 * π * T))) := by
        rw [← hfac, div_mul_eq_div_div_swap, mul_div_cancel_right₀ _ (Real.exp_pos _).ne']
      _ ≤ (δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1)) / (1 - Real.exp (-(2 * π))) := by
        gcongr
      _ = δ / ((n : ℝ) - a + 1) := by field_simp
  have hint_norm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a : ℝ)) (b := n)
    (C := δ / ((n : ℝ) - a + 1)) fun x hx => hbound x (by rwa [uIoc_of_le han'] at hx)
  rw [abs_of_nonneg (sub_nonneg.mpr han')] at hint_norm
  refine hint_norm.trans_lt ?_
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ hlen_pos).mpr (by linarith)

/-- Evaluates a segment integral of the singular model `c / (-2πi * (z₀ + t d))` multiplied by
the segment direction `d`, factoring out `c / (-2πi)` and applying
`integral_inv_linear_mul_eq_log_sub`. -/
private theorem mul_integral_div_neg_two_pi_I_mul_linear (c d u z₀ : ℂ) {a₀ b₀ : ℝ}
    (hslit : ∀ t ∈ Set.uIcc a₀ b₀, u * (z₀ + (t : ℂ) * d) ∈ Complex.slitPlane) :
    d * (∫ t in a₀..b₀, c / (-2 * π * I * (z₀ + (t : ℂ) * d))) =
      (c / (-2 * π * I)) *
        (Complex.log (u * (z₀ + (b₀ : ℂ) * d)) - Complex.log (u * (z₀ + (a₀ : ℂ) * d))) := by
  have hrew : d * (∫ t in a₀..b₀, c / (-2 * π * I * (z₀ + (t : ℂ) * d))) =
      (c / (-2 * π * I)) * ∫ t in a₀..b₀, (z₀ + (t : ℂ) * d)⁻¹ * d := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact integral_congr fun _ _ => by rw [div_mul_eq_div_div, div_eq_mul_inv]; ring
  rw [hrew, integral_inv_linear_mul_eq_log_sub hslit]

/-- Exact evaluation of the singular model for the upper-right quarter-box indent. -/
private theorem upperRightCap_model (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0 : ℝ)..ε, c / (-2 * π * I * ((t : ℂ) + ε * I))) -
      I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * ((ε : ℂ) + y * I))) = c / 4 := by
  have h1 := mul_integral_div_neg_two_pi_I_mul_linear c 1 1 ((ε : ℂ) * I) (a₀ := 0) (b₀ := ε)
    fun t _ => Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [hε.ne']))
  simp only [one_mul, mul_one, ofReal_zero, add_comm ((ε : ℂ) * I), zero_add] at h1
  have h2 := mul_integral_div_neg_two_pi_I_mul_linear c I 1 ε (a₀ := 0) (b₀ := ε)
    fun y _ => Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hε]))
  simp only [one_mul, ofReal_zero, zero_mul, add_zero] at h2
  rw [h1, h2, ← mul_sub, sub_sub_sub_cancel_left,
    Complex.log_ofReal_mul hε I_ne_zero, Complex.ofReal_log hε.le, Complex.log_I,
    sub_add_cancel_left]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp; ring

/-- Exact evaluation of the singular model for the upper-left quarter-box indent, using the rotated
branch `w ↦ log (-i * w)` on the second quadrant. -/
private theorem upperLeftCap_model (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (-ε)..(0 : ℝ), c / (-2 * π * I * ((t : ℂ) + ε * I))) +
      I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * (-(ε : ℂ) + y * I))) = c / 4 := by
  have hrot1 : ∀ t : ℝ, -I * ((ε : ℂ) * I + (t : ℂ) * 1) = (ε : ℂ) - (t : ℂ) * I := fun t => by
    calc -I * ((ε : ℂ) * I + (t : ℂ) * 1) = -(t : ℂ) * I - (ε : ℂ) * (I * I) := by ring
      _ = (ε : ℂ) - (t : ℂ) * I := by rw [I_mul_I]; ring
  have hrot2 : ∀ y : ℝ, -I * (-(ε : ℂ) + (y : ℂ) * I) = (y : ℂ) + (ε : ℂ) * I := fun y => by
    calc -I * (-(ε : ℂ) + (y : ℂ) * I) = -(y : ℂ) * (I * I) + (ε : ℂ) * I := by ring
      _ = (y : ℂ) + (ε : ℂ) * I := by rw [I_mul_I]; ring
  have h1 := mul_integral_div_neg_two_pi_I_mul_linear c 1 (-I) ((ε : ℂ) * I) (a₀ := -ε) (b₀ := 0)
    fun t _ => Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hrot1]; simp [hε]))
  have hlog : (ε : ℂ) - -(ε : ℂ) * I = (ε : ℂ) + ε * I := by ring
  rw [hrot1, hrot1] at h1
  simp only [one_mul, mul_one, ofReal_zero, zero_mul, sub_zero, ofReal_neg, hlog,
    add_comm ((ε : ℂ) * I)] at h1
  have h2 := mul_integral_div_neg_two_pi_I_mul_linear c I (-I) (-ε) (a₀ := 0) (b₀ := ε)
    fun y _ => Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [hrot2]; simp [hε.ne']))
  rw [hrot2, hrot2] at h2
  simp only [ofReal_zero, zero_add] at h2
  rw [h1, h2, ← mul_add, sub_add_sub_cancel,
    Complex.log_ofReal_mul hε I_ne_zero, Complex.ofReal_log hε.le, Complex.log_I,
    sub_add_cancel_left]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp; ring

/-- Near an integer `k` in the strip `S`, `‖w‖ * ‖g₊(k + w) - f(k) / (-2πiw)‖ → 0` as `w → 0`. -/
private theorem tendsto_norm_mul_abelPlanaUpper_sub {f : ℂ → ℂ} {S : Set ℂ} {k : ℤ}
    (hk : (k : ℂ) ∈ S) (hcont : ContinuousOn f S) :
    Tendsto (fun w : ℂ => ‖w‖ * ‖abelPlanaUpper f ((k : ℂ) + w) - f k / (-2 * π * I * w)‖)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 0) := by
  have hc_ne : (-2 * π * I : ℂ) ≠ 0 := neg_two_pi_I_ne_zero
  have hinv : Tendsto (fun u : ℂ => u / (cexp u - 1)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    simpa [div_eq_inv_mul] using
      ((Complex.hasDerivAt_exp 0).tendsto_slope_zero).inv₀ (by simp : cexp 0 ≠ 0)
  have hmap_u : Tendsto (fun w : ℂ => -2 * π * I * w)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous fun w : ℂ => -2 * π * I * w).tendsto' 0 0
        (mul_zero _)).mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with w hw using mul_ne_zero hc_ne hw.1)
  have hquot : Tendsto (fun w : ℂ => w / (cexp (-2 * π * I * w) - 1))
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 (1 / (-2 * π * I))) :=
    ((hinv.comp hmap_u).div_const (-2 * π * I)).congr fun w => by
      dsimp only [Function.comp_apply]; rw [div_right_comm, mul_div_cancel_left₀ _ hc_ne]
  have hf_lim : Tendsto (fun w : ℂ => f ((k : ℂ) + w))
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 (f k)) :=
    (hcont (k : ℂ) hk).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun w : ℂ => (k : ℂ) + w)
        (((by fun_prop : Continuous fun w : ℂ => (k : ℂ) + w).tendsto' 0 (k : ℂ)
          (add_zero _)).mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with _ hw using hw.2))
  have hprod : Tendsto (fun w : ℂ =>
      ‖f ((k : ℂ) + w) * (w / (cexp (-2 * π * I * w) - 1)) - f k / (-2 * π * I)‖)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 0) := by
    simpa [div_eq_mul_inv] using ((hf_lim.mul hquot).sub_const (f k / (-2 * π * I))).norm
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  dsimp only [abelPlanaUpper]
  rw [add_comm (k : ℂ), Complex.exp_neg_two_pi_mul_I_mul_add_intCast, ← norm_mul, mul_sub]
  congr 1
  have hw0 : w ≠ 0 := hw.1
  rcases em (cexp (-2 * π * I * w) - 1 = 0) with h0 | h0
  · rw [h0]; field_simp [hw0, hc_ne]
  · field_simp [hw0, hc_ne, h0]

/-- If `0 < ‖w‖ < 1`, `w` cannot be a nonzero integer, so `e^{-2πi(k + w)} ≠ 1`. -/
private theorem cexp_neg_two_pi_I_mul_int_add_ne_one_of_norm_lt_one (k : ℤ) {w : ℂ}
    (hw0 : 0 < ‖w‖) (hw1 : ‖w‖ < 1) : cexp (-2 * π * I * ((k : ℂ) + w)) ≠ 1 := by
  rw [add_comm (k : ℂ), Complex.exp_neg_two_pi_mul_I_mul_add_intCast]
  intro h
  obtain ⟨m, rfl⟩ := Complex.exp_neg_two_pi_mul_I_mul_eq_one_iff.mp h
  rw [Complex.norm_intCast] at hw0 hw1
  have : (0 : ℤ) < |m| := by exact_mod_cast hw0
  have : |m| < (1 : ℤ) := by exact_mod_cast hw1
  omega

/-- Along a family of segments `γ ε : [a₀ ε, b₀ ε] → ℂ` of length `ε` with `ε ≤ ‖γ ε t‖ ≤ 2 * ε`,
the integral of `abelPlanaUpper f (k + γ ε t)` minus its singular model tends to `0` as `ε → 0⁺`. -/
private theorem tendsto_integral_abelPlanaUpper_sub_zero {f : ℂ → ℂ} {S : Set ℂ} {k : ℤ}
    {a₀ b₀ : ℝ → ℝ} {γ : ℝ → ℝ → ℂ} (hk : (k : ℂ) ∈ S) (hcont : ContinuousOn f S)
    (hseg : ∀ ε ∈ Ioo (0 : ℝ) 1, b₀ ε - a₀ ε = ε ∧ Continuous (γ ε) ∧
      ∀ t ∈ Icc (a₀ ε) (b₀ ε), ε ≤ ‖γ ε t‖ ∧ ‖γ ε t‖ ≤ 2 * ε ∧ (k : ℂ) + γ ε t ∈ S) :
    Tendsto (fun ε : ℝ => (∫ t in a₀ ε..b₀ ε, abelPlanaUpper f ((k : ℂ) + γ ε t)) -
      ∫ t in a₀ ε..b₀ ε, f k / (-2 * π * I * γ ε t)) (𝓝[>] 0) (𝓝 0) := by
  have hc_ne : (-2 * π * I : ℂ) ≠ 0 := neg_two_pi_I_ne_zero
  have hlim := tendsto_norm_mul_abelPlanaUpper_sub hk hcont
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hball := hlim.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < δ / 2))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hball
  obtain ⟨r, hr, hball⟩ := hball
  refine eventually_nhdsWithin_iff.mpr (Metric.eventually_nhds_iff.mpr
    ⟨min (r / 3) (1 / 3), by positivity, fun ε hε_dist (hε : 0 < ε) => ?_⟩)
  have hε_lt : ε < min (r / 3) (1 / 3) := by simpa [Real.dist_eq, abs_of_pos hε] using hε_dist
  have hεr : ε < r / 3 := hε_lt.trans_le (min_le_left _ _)
  have hε3 : ε < 1 / 3 := hε_lt.trans_le (min_le_right _ _)
  obtain ⟨hlen, hγ, hsegε⟩ := hseg ε ⟨hε, by linarith⟩
  have hab : a₀ ε ≤ b₀ ε := by linarith
  have hint1 : IntervalIntegrable (fun t : ℝ => abelPlanaUpper f ((k : ℂ) + γ ε t))
      volume (a₀ ε) (b₀ ε) :=
    (ContinuousOn.div
      (hcont.comp (continuous_const.add hγ).continuousOn fun t ht => (hsegε t ht).2.2)
      (by fun_prop) fun t ht => sub_ne_zero.mpr
        (cexp_neg_two_pi_I_mul_int_add_ne_one_of_norm_lt_one k
          (hε.trans_le (hsegε t ht).1) ((hsegε t ht).2.1.trans_lt (by linarith))))
      |>.intervalIntegrable_of_Icc hab
  have hint2 : IntervalIntegrable (fun t : ℝ => f k / (-2 * π * I * γ ε t))
      volume (a₀ ε) (b₀ ε) :=
    (ContinuousOn.div continuousOn_const (by fun_prop) fun t ht =>
      mul_ne_zero hc_ne (norm_pos_iff.mp (hε.trans_le (hsegε t ht).1)))
      |>.intervalIntegrable_of_Icc hab
  rw [dist_zero_right, ← intervalIntegral.integral_sub hint1 hint2]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := (δ / 2) / ε) fun t ht => by
    rw [uIoc_of_le hab] at ht
    obtain ⟨hlo, hhi, hS⟩ := hsegε t ⟨ht.1.le, ht.2⟩
    have hm := hball (by rw [dist_zero_right]; linarith)
      ⟨norm_pos_iff.mp (hε.trans_le hlo), hS⟩
    have hpt : ‖γ ε t‖ * ‖abelPlanaUpper f ((k : ℂ) + γ ε t) -
        f k / (-2 * π * I * γ ε t)‖ ≤ δ / 2 :=
      le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hm)
    exact ((le_div_iff₀' (hε.trans_le hlo)).mpr hpt).trans
      (div_le_div_of_nonneg_left (by positivity) hε hlo)
  rw [hlen, abs_of_pos hε, div_mul_cancel₀ _ hε.ne'] at hle
  exact hle.trans_lt (by linarith)

/-- Quarter-box limit `upperRightCap f j ε → f j / 4` as `ε → 0⁺` for `j ∈ [a, n)`. -/
private theorem tendsto_upperRightCap {f : ℂ → ℂ} {a n j : ℤ} (hj : j ∈ Finset.Ico a n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    Tendsto (fun ε : ℝ => upperRightCap f j ε) (𝓝[>] 0) (𝓝 (f j / 4)) := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hjS : (j : ℂ) ∈ {z : ℂ | (a : ℝ) ≤ z.re ∧ z.re ≤ n} :=
    ⟨by simpa using hja', by simp; linarith⟩
  have hb1 := tendsto_integral_abelPlanaUpper_sub_zero hjS hcont
    (a₀ := fun _ => 0) (b₀ := fun ε => ε) (γ := fun ε t => (t : ℂ) + ε * I) fun ε ⟨hε0, hε1⟩ =>
      ⟨sub_zero ε, by fun_prop, fun t ht =>
        ⟨by simpa [abs_of_pos hε0] using Complex.abs_im_le_norm ((t : ℂ) + ε * I),
         (norm_add_le _ _).trans (by simp [abs_of_nonneg ht.1, abs_of_pos hε0]; linarith [ht.2]),
         by simp; constructor <;> linarith [ht.1, ht.2]⟩⟩
  have hb2 := tendsto_integral_abelPlanaUpper_sub_zero hjS hcont
    (a₀ := fun _ => 0) (b₀ := fun ε => ε) (γ := fun ε y => (ε : ℂ) + y * I) fun ε ⟨hε0, hε1⟩ =>
      ⟨sub_zero ε, by fun_prop, fun y hy =>
        ⟨by simpa [abs_of_pos hε0] using Complex.abs_re_le_norm ((ε : ℂ) + y * I),
         (norm_add_le _ _).trans (by simp [abs_of_pos hε0, abs_of_nonneg hy.1]; linarith [hy.2]),
         by simp; constructor <;> linarith⟩⟩
  have hcomb := (hb1.sub (hb2.const_mul I)).add_const (f j / 4)
  simp only [mul_zero, sub_self, zero_add] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  dsimp only [upperRightCap]
  simp only [add_assoc]
  linear_combination -upperRightCap_model (f j) hε

/-- Quarter-box limit `upperLeftCap f (j + 1) ε → f (j + 1) / 4` as `ε → 0⁺` for `j ∈ [a, n)`. -/
private theorem tendsto_upperLeftCap {f : ℂ → ℂ} {a n j : ℤ} (hj : j ∈ Finset.Ico a n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    Tendsto (fun ε : ℝ => upperLeftCap f (j + 1) ε) (𝓝[>] 0) (𝓝 (f ((j + 1 : ℤ) : ℂ) / 4)) := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  let k : ℤ := j + 1
  have hka' : (a : ℝ) + 1 ≤ k := by dsimp [k]; exact_mod_cast Int.add_le_add_right hja 1
  have hkn' : (k : ℝ) ≤ n := by dsimp [k]; exact_mod_cast hjn
  have hkS : (k : ℂ) ∈ {z : ℂ | (a : ℝ) ≤ z.re ∧ z.re ≤ n} :=
    ⟨by simp; linarith, by simpa using hkn'⟩
  have hb1 := tendsto_integral_abelPlanaUpper_sub_zero hkS hcont
    (a₀ := fun ε => -ε) (b₀ := fun _ => 0) (γ := fun ε t => (t : ℂ) + ε * I) fun ε ⟨hε0, hε1⟩ =>
      ⟨by ring, by fun_prop, fun t ht =>
        ⟨by simpa [abs_of_pos hε0] using Complex.abs_im_le_norm ((t : ℂ) + ε * I),
         (norm_add_le _ _).trans (by simp [abs_of_nonpos ht.2, abs_of_pos hε0]; linarith [ht.1]),
         by simp; constructor <;> linarith [ht.1, ht.2]⟩⟩
  have hb2 := tendsto_integral_abelPlanaUpper_sub_zero hkS hcont
    (a₀ := fun _ => 0) (b₀ := fun ε => ε) (γ := fun ε y => -(ε : ℂ) + y * I) fun ε ⟨hε0, hε1⟩ =>
      ⟨sub_zero ε, by fun_prop, fun y hy =>
        ⟨by simpa [abs_of_pos hε0] using Complex.abs_re_le_norm (-(ε : ℂ) + y * I),
         (norm_add_le _ _).trans (by simp [abs_of_pos hε0, abs_of_nonneg hy.1]; linarith [hy.2]),
         by simp; constructor <;> linarith⟩⟩
  have hcomb := (hb1.add (hb2.const_mul I)).add_const (f k / 4)
  simp only [mul_zero, add_zero, zero_add] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  dsimp only [upperLeftCap, k]
  simp only [sub_eq_add_neg, add_assoc]
  linear_combination -upperLeftCap_model (f ((j + 1 : ℤ) : ℂ)) hε

/-- Shrinking the punctured unit subintervals `[j + ε, j + 1 - ε]` to `[j, j + 1]` recovers
`- ∫_a^n f` as `ε → 0⁺`. -/
private theorem tendsto_neg_sum_integral_Ico {f : ℂ → ℂ} {a n : ℤ} (han : a < n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    Tendsto
      (fun ε : ℝ => - ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x)
      (𝓝[>] 0) (𝓝 (- ∫ x in (a : ℝ)..n, f x)) := by
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han.le
  have hint : IntervalIntegrable (fun x : ℝ => f x) volume (a : ℝ) n :=
    (hcont.comp Complex.continuous_ofReal.continuousOn
      fun x hx => ⟨by simp [hx.1], by simp [hx.2]⟩).intervalIntegrable_of_Icc han'
  have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ ε :=
    eventually_nhdsWithin_of_forall fun _ h => le_of_lt h
  exact (TauCeti.intervalIntegral.tendsto_sum_integral_Ico_add_sub han.le hint hev hev h0 h0).neg

/-! ### General complex Abel–Plana formula and Schwarz-symmetric specialization -/

/-- Schwarz conjugate `z ↦ conj (f (conj z))` used to deduce the lower half-plane contour identity
from the upper half-plane one. -/
private noncomputable def schwarzConjFun (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (f (conj z))

/-- Combining the upper and conjugated lower quarter-box limits over `j ∈ [a, n)` yields the
trapezoidal sum `∑_{j=a}^n f(j) - f(a) / 2 - f(n) / 2` as `ε → 0⁺`. -/
private theorem tendsto_sum_abelPlana_caps {f : ℂ → ℂ} {a n : ℤ} (han : a < n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    Tendsto
      (fun ε : ℝ => ∑ j ∈ Finset.Ico a n,
        (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
          upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε)))
      (𝓝[>] 0) (𝓝 ((∑ j ∈ Finset.Icc a n, f j) - f a / 2 - f n / 2)) := by
  have hcont_conj : ContinuousOn (schwarzConjFun f) {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n} :=
    continuousOn_conj_conj_of_symmetric (fun _ h => by simpa using h) hcont
  have htrap : ∑ j ∈ Finset.Ico a n, (f j / 2 + f ((j + 1 : ℤ) : ℂ) / 2) =
      (∑ j ∈ Finset.Icc a n, f j) - f a / 2 - f n / 2 := by
    have hsum := Finset.sum_Ico_add_add_endpoints (fun j : ℤ => f j / 2) han.le
    have h2 : 2 • ∑ j ∈ Finset.Icc a n, f j / 2 = ∑ j ∈ Finset.Icc a n, f j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [two_smul, add_halves]
    rw [h2] at hsum; linear_combination hsum
  rw [← htrap]
  refine tendsto_finsetSum _ fun j hj => ?_
  have hr2 := (Complex.continuous_conj.tendsto _).comp (tendsto_upperRightCap hj hcont_conj)
  have hl2 := (Complex.continuous_conj.tendsto _).comp (tendsto_upperLeftCap hj hcont_conj)
  have hsum4 := (((tendsto_upperRightCap hj hcont).add hr2).add
    (tendsto_upperLeftCap hj hcont)).add hl2
  have hval : f j / 4 + conj (schwarzConjFun f j / 4) + f ((j + 1 : ℤ) : ℂ) / 4 +
      conj (schwarzConjFun f ((j + 1 : ℤ) : ℂ) / 4) =
      f j / 2 + f ((j + 1 : ℤ) : ℂ) / 2 := by
    dsimp only [schwarzConjFun]
    simp only [map_div₀, map_ofNat, map_intCast, starRingEnd_self_apply]; ring
  rwa [hval] at hsum4

private theorem tendsto_schwarzConjFun_growth {f : ℂ → ℂ} {a b : ℝ}
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) (𝓝 0)) :
    Tendsto (fun z => schwarzConjFun f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) (𝓝 0) := by
  have hmap : Tendsto (starRingEnd ℂ)
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b})
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · rw [tendsto_comap_iff]
      have heq : ((fun z : ℂ => |z.im|) ∘ starRingEnd ℂ) = fun z : ℂ => |z.im| := by
        ext z; simp
      rw [heq]
      exact tendsto_comap.mono_left inf_le_left
    · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
      simpa using hz
  have h1 := (Complex.continuous_conj.tendsto 0).comp (hgrowth.comp hmap)
  simp only [map_zero] at h1
  refine h1.congr fun z => ?_
  dsimp only [Function.comp_apply, schwarzConjFun]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_im, abs_neg]

/-- Pairing the upper and conjugated lower integrands along a pole-free real segment
`[j + ε, j + 1 - ε]` yields `- ∫_{j + ε}^{j + 1 - ε} f`. -/
private theorem real_seg_add_conj_eq {f : ℂ → ℂ} {a n j : ℤ} {ε : ℝ}
    (hj : j ∈ Finset.Ico a n) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    (∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
      conj (∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper (schwarzConjFun f) x) =
    - ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hle1 : (j : ℝ) + ε ≤ (j : ℝ) + 1 - ε := by linarith
  have hc : ∀ {g : ℂ → ℂ}, ContinuousOn g {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n} →
      ContinuousOn (fun x : ℝ => abelPlanaUpper g x) (Icc ((j : ℝ) + ε) ((j : ℝ) + 1 - ε)) :=
    fun hg => (hg.comp (by fun_prop) fun x hx =>
      ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩).div (by fun_prop) fun x hx =>
        sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j
          ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩)
  have hc1 := (hc hcont).intervalIntegrable_of_Icc (μ := volume) hle1
  have hc2 : IntervalIntegrable
      (fun x : ℝ => conj (abelPlanaUpper (schwarzConjFun f) x)) volume _ _ :=
    (Complex.continuous_conj.comp_continuousOn
      (hc (continuousOn_conj_conj_of_symmetric (fun _ h => by simpa using h)
        hcont))).intervalIntegrable_of_Icc (μ := volume) hle1
  rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_add hc1 hc2,
    ← intervalIntegral.integral_neg]
  refine integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hle1] at hx
  exact abelPlanaUpper_add_conj_comp f j ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Pairing the upper and conjugated lower vertical boundary integrals on `[ε, T]` along
`Re z = k`. -/
private theorem vert_seg_add_conj_eq {f : ℂ → ℂ} {a n k : ℤ} {ε T : ℝ}
    (hε0 : 0 < ε) (hεT : ε ≤ T) (hka : (a : ℝ) ≤ k) (hkn : (k : ℝ) ≤ n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    I * (∫ y in ε..T, f (k + y * I) / (Real.exp (2 * π * y) - 1)) +
      (-I) * conj (∫ y in ε..T, schwarzConjFun f (k + y * I) / (Real.exp (2 * π * y) - 1)) =
    I * (∫ y in ε..T, (f (k + y * I) - f (k - y * I)) / (Real.exp (2 * π * y) - 1)) := by
  have hden_ne : ∀ y ∈ Icc ε T, ((Real.exp (2 * π * y) : ℂ) - 1) ≠ 0 := fun y hy => by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr
      (Real.one_lt_exp_iff.mpr (mul_pos Real.two_pi_pos (hε0.trans_le hy.1))).ne')
  have hv : ∀ {g : ℂ → ℂ}, ContinuousOn g {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n} →
      ContinuousOn (fun y : ℝ => g (k + y * I) / (Real.exp (2 * π * y) - 1)) (Icc ε T) :=
    fun hg => (hg.comp (by fun_prop) fun _ _ => ⟨by simp [hka], by simp [hkn]⟩).div
      (by fun_prop) hden_ne
  have hv1 := (hv hcont).intervalIntegrable_of_Icc (μ := volume) hεT
  have hv2 : IntervalIntegrable
      (fun y : ℝ => conj (schwarzConjFun f (k + y * I) / (Real.exp (2 * π * y) - 1))) volume _ _ :=
    (Complex.continuous_conj.comp_continuousOn
      (hv (continuousOn_conj_conj_of_symmetric (fun _ h => by simpa using h)
        hcont))).intervalIntegrable_of_Icc (μ := volume) hεT
  rw [← intervalIntegral.intervalIntegral_conj, neg_mul, ← sub_eq_add_neg, ← mul_sub,
    ← intervalIntegral.integral_sub hv1 hv2]
  exact congrArg (I * ·) (integral_congr fun y _ => by
    dsimp only [schwarzConjFun]
    simp only [map_div₀, map_sub, map_one, Complex.conj_ofReal, starRingEnd_self_apply,
      map_add, map_intCast, map_mul, Complex.conj_I, mul_neg, ← sub_eq_add_neg, sub_div])

/-- Finite-`(ε, T)` combined upper and lower contour identity obtained by pairing `f` with
`schwarzConjFun f`. -/
private theorem combined_rect_identity {f : ℂ → ℂ} {a n : ℤ} {ε T : ℝ}
    (han : a < n) (hε0 : 0 < ε) (hε2 : ε < 1 / 2) (hεT : ε ≤ T)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    (∫ x in (a : ℝ)..n, abelPlanaUpper f (x + T * I)) +
      conj (∫ x in (a : ℝ)..n, abelPlanaUpper (schwarzConjFun f) (x + T * I)) +
      I * (∫ y in ε..T, (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) -
      I * (∫ y in ε..T, (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) =
    (- ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x) +
      (∑ j ∈ Finset.Ico a n,
        (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
          upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε))) := by
  have hu1 := upper_rect_identity han hε0 hε2 hεT hf hcont
  have hu2 := congrArg (starRingEnd ℂ)
    (upper_rect_identity (f := schwarzConjFun f) han hε0 hε2 hεT
      (differentiableOn_conj_conj_of_symmetric (fun _ h => by simpa using h) hf)
      (continuousOn_conj_conj_of_symmetric (fun _ h => by simpa using h) hcont))
  simp only [map_add, map_sub, map_sum, map_mul, Complex.conj_I] at hu2
  have hcomb := congrArg₂ (· + ·) hu1 hu2
  have hsum_real :
      (∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
        ∑ j ∈ Finset.Ico a n,
          conj (∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper (schwarzConjFun f) x) =
      - ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => real_seg_add_conj_eq hj hε0 hε2 hcont
  have hsum_caps :
      (∑ j ∈ Finset.Ico a n, (upperRightCap f j ε + upperLeftCap f (j + 1) ε)) +
        ∑ j ∈ Finset.Ico a n, (conj (upperRightCap (schwarzConjFun f) j ε) +
          conj (upperLeftCap (schwarzConjFun f) (j + 1) ε)) =
      ∑ j ∈ Finset.Ico a n,
        (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
          upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han.le
  linear_combination -hcomb + hsum_real + hsum_caps -
    vert_seg_add_conj_eq hε0 hεT le_rfl han' hcont +
    vert_seg_add_conj_eq hε0 hεT han' le_rfl hcont

/-- Sending `T → +∞` in `combined_rect_identity` at fixed `ε ∈ (0, 1 / 2)`. -/
private theorem combined_strip_identity {f : ℂ → ℂ} {a n : ℤ} {ε : ℝ}
    (han : a < n) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0))
    (hinta : IntegrableOn
      (fun y : ℝ => (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) (Ioi 0))
    (hintn : IntegrableOn
      (fun y : ℝ => (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    (- ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x) +
      (∑ j ∈ Finset.Ico a n,
        (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
          upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε))) =
    I * (∫ y in Ioi ε, (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) -
      I * (∫ y in Ioi ε, (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) := by
  have hlim_top1 := tendsto_integral_abelPlanaUpper_atTop han.le hgrowth
  have hlim_top2 := (Complex.continuous_conj.tendsto 0).comp
    (tendsto_integral_abelPlanaUpper_atTop han.le (tendsto_schwarzConjFun_growth hgrowth))
  have hlim_va :=
    intervalIntegral_tendsto_integral_Ioi ε (hinta.mono_set (Ioi_subset_Ioi hε0.le)) tendsto_id
  have hlim_vn :=
    intervalIntegral_tendsto_integral_Ioi ε (hintn.mono_set (Ioi_subset_Ioi hε0.le)) tendsto_id
  have hlim_lhs := ((hlim_top1.add hlim_top2).add (hlim_va.const_mul I)).sub (hlim_vn.const_mul I)
  simp only [map_zero, zero_add] at hlim_lhs
  refine (tendsto_nhds_unique (hlim_lhs.congr' ?_) tendsto_const_nhds).symm
  filter_upwards [eventually_ge_atTop ε] with T hεT
  exact combined_rect_identity han hε0 hε2 hεT hf hcont

/-- **General complex Abel–Plana summation formula** (Olver, Ch. 8, §3.2, eq. 3.07). For integers
`a ≤ n` and `f : ℂ → ℂ` holomorphic on `a < Re z < n`, continuous on `a ≤ Re z ≤ n`, satisfying
`f(z) = o(e^{2π|Im z|})` as `|Im z| → ∞` uniformly in the strip, with
`(f(c + i y) - f(c - i y)) / (e^{2πy} - 1)` integrable on `(0, ∞)` at `c = a` and `c = n`,
`∑_{j=a}^n f(j) = ∫_a^n f + (f(a) + f(n)) / 2
  + i ∫_0^∞ (f(a + iy) - f(a - iy)) / (e^{2πy} - 1) dy
  - i ∫_0^∞ (f(n + iy) - f(n - iy)) / (e^{2πy} - 1) dy`. -/
theorem sum_Icc_eq_abelPlana_sub {f : ℂ → ℂ} {a n : ℤ} (han : a ≤ n)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0))
    (hinta : IntegrableOn
      (fun y : ℝ => (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) (Ioi 0))
    (hintn : IntegrableOn
      (fun y : ℝ => (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    ∑ j ∈ Finset.Icc a n, f j =
      (∫ x in (a : ℝ)..n, f x) + f a / 2 + f n / 2 +
        I * (∫ y in Ioi (0 : ℝ),
          (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) -
        I * (∫ y in Ioi (0 : ℝ),
          (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) := by
  rcases han.lt_or_eq with han | rfl
  swap; · simp
  -- Combine the segment, quarter-box, and improper vertical-tail limits as `ε → 0⁺`.
  have hlim_seg := tendsto_neg_sum_integral_Ico han hcont
  have hlim_caps := tendsto_sum_abelPlana_caps han hcont
  have hlim_rhs :=
    ((hinta.continuousWithinAt_Ici_primitive_Ioi.mono Ioi_subset_Ici_self).tendsto.const_mul I).sub
      ((hintn.continuousWithinAt_Ici_primitive_Ioi.mono Ioi_subset_Ici_self).tendsto.const_mul I)
  have heq_ev := Filter.Eventually.mono (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))
    fun ε hε => combined_strip_identity han hε.1 hε.2 hf hcont hgrowth hinta hintn
  linear_combination tendsto_nhds_unique ((hlim_seg.add hlim_caps).congr' heq_ev) hlim_rhs

/-- **The Abel–Plana formula** (DLMF 2.10.2, exact form). Let `a ≤ n` be integers and let `f` be
holomorphic on the open strip `a < Re z < n` and continuous on its closure `a ≤ Re z ≤ n`, with
`f(z) = o(e^{2π|Im z|})` uniformly in the strip, `f` real on `[a, n]`, and
`y ↦ Im f(c + iy) / (e^{2πy} - 1)` integrable on `(0, ∞)` at `c = a` and `c = n`. Then
`∑_{j=a}^n f(j) = ∫_a^n f + f(a) / 2 + f(n) / 2
  - 2 ∫_0^∞ Im f(a + iy) / (e^{2πy} - 1) dy
  + 2 ∫_0^∞ Im f(n + iy) / (e^{2πy} - 1) dy`. -/
theorem sum_Icc_eq_abelPlana {f : ℂ → ℂ} {a n : ℤ} (han : a ≤ n)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n})
    (hgrowth : Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) (𝓝 0))
    (hreal : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ n → (f x).im = 0)
    (hinta : IntegrableOn (fun y : ℝ => (f (a + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0))
    (hintn : IntegrableOn (fun y : ℝ => (f (n + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0)) :
    ∑ j ∈ Finset.Icc a n, f j =
      (∫ x in (a : ℝ)..n, f x) + f a / 2 + f n / 2 -
        2 * ((∫ y in Ioi (0 : ℝ), (f (a + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) +
        2 * ((∫ y in Ioi (0 : ℝ), (f (n + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
  rcases han.lt_or_eq with han | rfl
  swap; · simp
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have hvert : ∀ (k : ℤ), (a : ℝ) ≤ k → (k : ℝ) ≤ n →
      IntegrableOn (fun y : ℝ => (f (k + y * I)).im / (Real.exp (2 * π * y) - 1)) (Ioi 0) →
      IntegrableOn (fun y : ℝ => (f (k + y * I) - f (k - y * I)) / (Real.exp (2 * π * y) - 1))
        (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), (f (k + y * I) - f (k - y * I)) / (Real.exp (2 * π * y) - 1)) =
        (2 * I) *
          ((∫ y in Ioi (0 : ℝ), (f (k + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
    intro k hka hkn hk_int
    have hdiff : ∀ y : ℝ, (f (k + y * I) - f (k - y * I)) / (Real.exp (2 * π * y) - 1) =
        (2 * I) * (((f (k + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := fun y => by
      have hsymm := apply_conj_eq_conj_of_im_eq_zero_on_strip han' hf hcont
        (fun x h1 h2 => hreal x h1.le h2.le)
        (z := (k : ℂ) + (y : ℂ) * I) ⟨by simp [hka], by simp [hkn]⟩
      have hconj : conj ((k : ℂ) + (y : ℂ) * I) = (k : ℂ) - (y : ℂ) * I := by
        simp [sub_eq_add_neg]
      rw [← hconj, hsymm, Complex.sub_conj]
      push_cast; ring
    exact ⟨IntegrableOn.congr_fun (hk_int.ofReal.const_mul (2 * I))
      (fun y _ => (hdiff y).symm) measurableSet_Ioi,
      by rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hdiff y),
           MeasureTheory.integral_const_mul, integral_complex_ofReal]⟩
  obtain ⟨hinta', hia⟩ := hvert a le_rfl han'.le hinta
  obtain ⟨hintn', hin⟩ := hvert n han'.le le_rfl hintn
  rw [sum_Icc_eq_abelPlana_sub han.le hf hcont hgrowth hinta' hintn', hia, hin]
  have hI2 : I * (2 * I) = (-2 : ℂ) := by
    calc I * (2 * I) = 2 * (I * I) := by ring
      _ = -2 := by rw [I_mul_I]; ring
  linear_combination (norm := ring)
    ((∫ y in Ioi (0 : ℝ), (f (a + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) * hI2 -
      ((∫ y in Ioi (0 : ℝ), (f (n + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) * hI2

/-! ### Growth criterion -/

/-- Sufficient growth condition for the Abel–Plana formula: if `‖f z‖ ≤ C * (1 + |z.im|) ^ p *
exp (c * |z.im|)` holds eventually as `|z.im| → ∞` uniformly on the closed strip `{a ≤ z.re ≤ b}`
with `c < 2 * π`, then `f z * exp (-(2 * π * |z.im|)) → 0` as `|z.im| → ∞` uniformly in the
strip. -/
theorem tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le {f : ℂ → ℂ} {a b C p c : ℝ}
    (hc : c < 2 * π)
    (hbound : ∀ᶠ z in comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b},
      ‖f z‖ ≤ C * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) :
    Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) (𝓝 0) :=
  tendsto_mul_exp_neg_mul_abs_im_of_norm_le hc hbound

end TauCeti
