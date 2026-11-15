/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle

/-!
# The Abel–Plana summation formula

For integers `a ≤ n` and a function `f : ℂ → ℂ` holomorphic on the open vertical strip
`a < Re z < n` and continuous on its closure `a ≤ Re z ≤ n`, with `f(z) = o(e^{2π|Im z|})` as
`Im z → ±∞` uniformly in the strip, the Abel–Plana formula expresses `∑_{j=a}^n f(j)` through
`∫_a^n f`, the half-endpoint terms `(f(a) + f(n)) / 2`, and two improper integrals along the
vertical boundary lines `Re z = a` and `Re z = n` against the Bose–Einstein kernel
`(e^{2πy} - 1)⁻¹`.

Compared with the Euler–Maclaurin formula (`TauCeti.sum_Icc_eq_eulerMaclaurin`), the correction is
controlled by the growth of `f` on the vertical lines rather than by real higher derivatives on
`[a, n]`. The companion module `TauCeti.Analysis.Asymptotics.Sum.AbelPlana.Bernoulli` expands the
vertical-line integral in powers of `y` to recover the Bernoulli derivative series with an
exponentially damped vertical-line remainder.

## Main results

* `TauCeti.sum_Icc_eq_abelPlana_sub`: the general complex Abel–Plana formula (without assuming `f`
  is real on `[a, n]`), in terms of `(f(c + i y) - f(c - i y)) / (e^{2πy} - 1)` at `c = a, n`.
* `TauCeti.conj_apply_eq_of_im_eq_zero_on_strip`: Schwarz reflection symmetry
  `f(conj z) = conj (f z)` on a closed vertical strip when `f` is real on the real segment.
* `TauCeti.sum_Icc_eq_abelPlana`: the exact Abel–Plana formula (DLMF 2.10.2) for `f` real on
  `[a, n]`, in terms of `Im f(c + i y) / (e^{2πy} - 1)` at `c = a, n`.
* `TauCeti.tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le`: growth criterion verifying the uniform
  `o(e^{2π|Im z|})` hypothesis when `‖f z‖ ≤ C * (1 + |z.im|) ^ p * e^{c |z.im|}` with `c < 2 * π`.

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

namespace TauCeti

open Complex Filter intervalIntegral MeasureTheory Set
open scoped ComplexConjugate Interval Nat Real Topology

/-! ### Kernel identities and pole avoidance -/

/-- Upper-half-plane Abel–Plana integrand `f(z) / (e^{-2πiz} - 1)`. -/
private noncomputable def abelPlanaUpper (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / (cexp (-2 * π * I * z) - 1)

/-- Integer periodicity of `z ↦ e^{-2πiz}`. -/
private theorem cexp_neg_two_pi_I_mul_int_add (k : ℤ) (w : ℂ) :
    cexp (-2 * π * I * ((k : ℂ) + w)) = cexp (-2 * π * I * w) := by
  have hsplit : -2 * π * I * ((k : ℂ) + w) = (-k : ℤ) * (2 * π * I) + (-2 * π * I * w) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- Along a vertical line at an integer abscissa `k`, `e^{-2πi(k + iy)} = e^{2πy}`. -/
private theorem cexp_neg_two_pi_I_mul_int_add_mul_I (k : ℤ) (y : ℝ) :
    cexp (-2 * π * I * ((k : ℂ) + (y : ℂ) * I)) = (Real.exp (2 * π * y) : ℂ) := by
  rw [cexp_neg_two_pi_I_mul_int_add]
  have hy : -2 * π * I * ((y : ℂ) * I) = ((2 * π * y : ℝ) : ℂ) := by
    calc
      -2 * π * I * ((y : ℂ) * I) = -2 * (π : ℂ) * (y : ℂ) * (I * I) := by ring
      _ = ((2 * π * y : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
  rw [hy, Complex.ofReal_exp]

/-- Solutions to `e^{-2πiz} = 1` are integers. -/
private theorem exists_int_of_cexp_neg_two_pi_I_mul_eq_one {z : ℂ}
    (h : cexp (-2 * π * I * z) = 1) : ∃ m : ℤ, z = m := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hneg := mul_right_cancel₀ hpi (by linear_combination hk : -z * (2 * π * I) = k * (2 * π * I))
  exact ⟨-k, by push_cast; linear_combination -hneg⟩

/-- `e^{-2πiz} ≠ 1` off the real axis. -/
private theorem cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    cexp (-2 * π * I * z) ≠ 1 := fun h => by
  obtain ⟨m, rfl⟩ := exists_int_of_cexp_neg_two_pi_I_mul_eq_one h
  exact hz (intCast_im m)

/-- `e^{-2πiz} ≠ 1` whenever `Re z` lies strictly between two consecutive integers. -/
private theorem cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo {z : ℂ} (j : ℤ)
    (hz : z.re ∈ Ioo (j : ℝ) (j + 1)) : cexp (-2 * π * I * z) ≠ 1 := fun h => by
  obtain ⟨m, rfl⟩ := exists_int_of_cexp_neg_two_pi_I_mul_eq_one h
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

/-- Splitting an interval integral over `[a, n]` (`a ≤ n` in `ℤ`) into unit intervals. -/
private theorem integral_eq_sum_Ico_unit {h : ℝ → ℂ} {a n : ℤ} (han : a ≤ n)
    (hcont : ContinuousOn h (Icc (a : ℝ) n)) :
    ∫ x in (a : ℝ)..n, h x = ∑ j ∈ Finset.Ico a n, ∫ x in (j : ℝ)..((j : ℝ) + 1), h x := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = a + m := ⟨(n - a).toNat, by omega⟩
  induction m with
  | zero => simp
  | succ m ih =>
    have hm1 : a ≤ a + m := by omega
    have hstep' : ((a + m : ℤ) : ℝ) ≤ ((a + (m + 1 : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast (by omega : a + m ≤ a + (m + 1 : ℕ))
    have hcont1 := hcont.mono (Icc_subset_Icc le_rfl hstep')
    have hint1 := hcont1.intervalIntegrable_of_Icc (μ := volume) (by exact_mod_cast hm1)
    have hint2 := (hcont.mono (Icc_subset_Icc (by exact_mod_cast hm1)
      le_rfl)).intervalIntegrable_of_Icc (μ := volume) hstep'
    have hIco : Finset.Ico a (a + (m + 1 : ℕ)) = insert (a + m) (Finset.Ico a (a + m)) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hIco, Finset.sum_insert (by simp), ← ih hm1 hcont1,
      ← integral_add_adjacent_intervals hint1 hint2]
    rw [show ((a + (m + 1 : ℕ) : ℤ) : ℝ) = ((a + m : ℤ) : ℝ) + 1 by push_cast; ring, add_comm]

/-- Trapezoidal telescoping identity on `Finset.Ico a n` for `a < n`. -/
private theorem sum_Ico_half_add_half {g : ℤ → ℂ} {a n : ℤ} (han : a < n) :
    ∑ j ∈ Finset.Ico a n, (g j / 2 + g (j + 1) / 2) =
      (∑ j ∈ Finset.Icc a n, g j) - g a / 2 - g n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = a + (m + 1 : ℕ) := ⟨(n - 1 - a).toNat, by omega⟩
  induction m with
  | zero =>
    have hIco : Finset.Ico a (a + (1 : ℕ)) = {a} := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    have hIcc : Finset.Icc a (a + (1 : ℕ)) = insert (a + 1) {a} := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hIco, hIcc, Finset.sum_singleton, Finset.sum_insert (by simp), Finset.sum_singleton]
    push_cast; ring
  | succ m ih =>
    have hIco : Finset.Ico a (a + (m + 1 + 1 : ℕ)) =
        insert (a + (m + 1 : ℕ)) (Finset.Ico a (a + (m + 1 : ℕ))) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hIcc : Finset.Icc a (a + (m + 1 + 1 : ℕ)) =
        insert (a + (m + 1 + 1 : ℕ)) (Finset.Icc a (a + (m + 1 : ℕ))) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIco, hIcc, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih (by omega),
      show a + (m + 1 : ℕ) + 1 = a + (m + 1 + 1 : ℕ) by omega]
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
    (hcont.comp (by fun_prop) fun x hx => ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩).div
      (by fun_prop) fun _ _ =>
        sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by simp [hε0.ne']))
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
    rw [show -ε + ((j : ℝ) + 1) = (j : ℝ) + 1 - ε by ring, zero_add] at h
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
  have hcont_line : ContinuousOn (fun x : ℝ => abelPlanaUpper f (x + ε * I)) (Icc (a : ℝ) n) :=
    (hcont.comp (by fun_prop) fun x hx => ⟨by simp [hx.1], by simp [hx.2]⟩).div (by fun_prop)
      fun _ _ => sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by simp [hε0.ne']))
  have hsum_units :
      (∑ j ∈ Finset.Ico a n, ∫ x in (j : ℝ)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I)) =
        (∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
          ∑ j ∈ Finset.Ico a n, (upperRightCap f j ε + upperLeftCap f (j + 1) ε) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj => by
      rw [upper_unit_strip_eq hj hε0 hε2 hf hcont, add_assoc]
  have hvert : ∀ k : ℤ, (∫ y in ε..T, abelPlanaUpper f (k + y * I)) =
      ∫ y in ε..T, f (k + y * I) / (Real.exp (2 * π * y) - 1) :=
    fun k => integral_congr fun y _ => by
      dsimp only [abelPlanaUpper]; rw [cexp_neg_two_pi_I_mul_int_add_mul_I]
  rw [hvert a, hvert n, integral_eq_sum_Ico_unit han.le hcont_line, hsum_units] at hcauchy
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

/-- Exact logarithm difference `log ε - log (iε) = -iπ / 2` for `ε > 0`. -/
private theorem log_sub_log_mul_I {ε : ℝ} (hε : 0 < ε) :
    Complex.log (ε : ℂ) - Complex.log ((ε : ℂ) * I) = -((π / 2 : ℝ) : ℂ) * I := by
  refine Complex.ext (by simp [Complex.log_re, abs_of_pos hε]) ?_
  simp [Complex.log_im, Complex.arg_ofReal_of_nonneg hε.le,
    Complex.arg_real_mul I hε, Complex.arg_I]

/-- Fundamental theorem of calculus for `t ↦ (z₀ + t * d)⁻¹ * d` along a real segment mapped into
`Complex.slitPlane` after rotation by a nonzero constant `u`. -/
private theorem integral_inv_linear_mul_eq_log_sub {u z₀ d : ℂ} {a₀ b₀ : ℝ} (hu : u ≠ 0)
    (hslit : ∀ t ∈ Set.uIcc a₀ b₀, u * (z₀ + (t : ℂ) * d) ∈ Complex.slitPlane) :
    ∫ t in a₀..b₀, (z₀ + (t : ℂ) * d)⁻¹ * d =
      Complex.log (u * (z₀ + (b₀ : ℂ) * d)) - Complex.log (u * (z₀ + (a₀ : ℂ) * d)) := by
  have hne : ∀ t ∈ Set.uIcc a₀ b₀, z₀ + (t : ℂ) * d ≠ 0 :=
    fun t ht => (mul_ne_zero_iff.mp (Complex.slitPlane_ne_zero (hslit t ht))).2
  have hd : ∀ t ∈ Set.uIcc a₀ b₀,
      HasDerivAt (fun t : ℝ => Complex.log (u * (z₀ + (t : ℂ) * d)))
        ((z₀ + (t : ℂ) * d)⁻¹ * d) t := fun t ht => by
    have hinner : HasDerivAt (fun t : ℝ => u * (z₀ + (t : ℂ) * d)) (u * d) t := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const d).const_add z₀).const_mul u
    refine ((Complex.hasDerivAt_log (hslit t ht)).scomp t hinner).congr_deriv ?_
    have := hne t ht
    rw [smul_eq_mul]; field_simp
  have hint : IntervalIntegrable (fun t : ℝ => (z₀ + (t : ℂ) * d)⁻¹ * d) volume a₀ b₀ :=
    ContinuousOn.intervalIntegrable fun t ht =>
      (((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt.inv₀
        (hne t ht)).mul continuousAt_const).continuousWithinAt
  exact integral_eq_sub_of_hasDerivAt hd hint

/-- Exact evaluation of the singular model for the upper-right quarter-box indent. -/
private theorem upperRightCap_model (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0 : ℝ)..ε, c / (-2 * π * I * ((t : ℂ) + ε * I))) -
      I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * ((ε : ℂ) + y * I))) = c / 4 := by
  have h1 := integral_inv_linear_mul_eq_log_sub (u := 1) (z₀ := (ε : ℂ) * I) (d := 1)
    (a₀ := 0) (b₀ := ε) one_ne_zero fun t _ =>
      Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [hε.ne']))
  simp only [one_mul, mul_one, ofReal_zero, add_comm ((ε : ℂ) * I), zero_add] at h1
  have h2 := integral_inv_linear_mul_eq_log_sub (u := 1) (z₀ := ε) (d := I)
    (a₀ := 0) (b₀ := ε) one_ne_zero fun y _ =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hε]))
  simp only [one_mul, ofReal_zero, zero_mul, add_zero] at h2
  have hrew1 : (∫ t in (0 : ℝ)..ε, c / (-2 * π * I * ((t : ℂ) + ε * I))) =
      (c / (-2 * π * I)) * ∫ t in (0 : ℝ)..ε, ((t : ℂ) + ε * I)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun _ _ => by rw [div_mul_eq_div_div, div_eq_mul_inv]
  have hrew2 : I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * ((ε : ℂ) + y * I))) =
      (c / (-2 * π * I)) * ∫ y in (0 : ℝ)..ε, ((ε : ℂ) + y * I)⁻¹ * I := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact integral_congr fun _ _ => by rw [div_mul_eq_div_div, div_eq_mul_inv]; ring
  rw [hrew1, hrew2, h1, h2, ← mul_sub, sub_sub_sub_cancel_left, log_sub_log_mul_I hε]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : (I : ℂ) ≠ 0 := I_ne_zero
  push_cast; field_simp; ring

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
  have h1 := integral_inv_linear_mul_eq_log_sub (u := -I) (z₀ := (ε : ℂ) * I) (d := 1)
    (a₀ := -ε) (b₀ := 0) (neg_ne_zero.mpr I_ne_zero) fun t _ =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hrot1]; simp [hε]))
  rw [hrot1, hrot1] at h1
  simp only [mul_one, ofReal_zero, zero_mul, sub_zero, ofReal_neg, neg_mul, sub_neg_eq_add,
    add_comm ((ε : ℂ) * I)] at h1
  have h2 := integral_inv_linear_mul_eq_log_sub (u := -I) (z₀ := -ε) (d := I)
    (a₀ := 0) (b₀ := ε) (neg_ne_zero.mpr I_ne_zero) fun y _ =>
      Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [hrot2]; simp [hε.ne']))
  rw [hrot2, hrot2] at h2
  simp only [ofReal_zero, zero_add] at h2
  have hrew1 : (∫ t in (-ε)..(0 : ℝ), c / (-2 * π * I * ((t : ℂ) + ε * I))) =
      (c / (-2 * π * I)) * ∫ t in (-ε)..(0 : ℝ), ((t : ℂ) + ε * I)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun _ _ => by rw [div_mul_eq_div_div, div_eq_mul_inv]
  have hrew2 : I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * (-(ε : ℂ) + y * I))) =
      (c / (-2 * π * I)) * ∫ y in (0 : ℝ)..ε, (-(ε : ℂ) + y * I)⁻¹ * I := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact integral_congr fun _ _ => by rw [div_mul_eq_div_div, div_eq_mul_inv]; ring
  rw [hrew1, hrew2, h1, h2, ← mul_add, sub_add_sub_cancel, log_sub_log_mul_I hε]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : (I : ℂ) ≠ 0 := I_ne_zero
  push_cast; field_simp; ring

/-- Near an integer `k` in the strip `S`, `‖w‖ * ‖g₊(k + w) - f(k) / (-2πiw)‖ → 0` as `w → 0`. -/
private theorem tendsto_norm_mul_abelPlanaUpper_sub {f : ℂ → ℂ} {S : Set ℂ} {k : ℤ}
    (hk : (k : ℂ) ∈ S) (hcont : ContinuousOn f S) :
    Tendsto (fun w : ℂ => ‖w‖ * ‖abelPlanaUpper f ((k : ℂ) + w) - f k / (-2 * π * I * w)‖)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 0) := by
  have hc_ne : (-2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
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
  rw [cexp_neg_two_pi_I_mul_int_add, ← norm_mul, mul_sub]
  congr 1
  have hw0 : w ≠ 0 := hw.1
  rcases em (cexp (-2 * π * I * w) - 1 = 0) with h0 | h0
  · rw [h0]; field_simp [hw0, hc_ne]
  · field_simp [hw0, hc_ne, h0]

/-- If `0 < ‖w‖ < 1`, `w` cannot be a nonzero integer, so `e^{-2πi(k + w)} ≠ 1`. -/
private theorem cexp_neg_two_pi_I_mul_int_add_ne_one_of_norm_lt_one (k : ℤ) {w : ℂ}
    (hw0 : 0 < ‖w‖) (hw1 : ‖w‖ < 1) : cexp (-2 * π * I * ((k : ℂ) + w)) ≠ 1 := by
  rw [cexp_neg_two_pi_I_mul_int_add]
  intro h
  obtain ⟨m, rfl⟩ := exists_int_of_cexp_neg_two_pi_I_mul_eq_one h
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
  have hc_ne : (-2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
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
  have hcomb : Tendsto (fun ε : ℝ =>
      ((∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((t : ℂ) + ε * I))) -
        ∫ t in (0 : ℝ)..ε, f j / (-2 * π * I * ((t : ℂ) + ε * I))) -
      I * ((∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((ε : ℂ) + y * I))) -
        ∫ y in (0 : ℝ)..ε, f j / (-2 * π * I * ((ε : ℂ) + y * I))) + f j / 4)
      (𝓝[>] 0) (𝓝 (f j / 4)) := by
    simpa using (hb1.sub (hb2.const_mul I)).add_const (f j / 4)
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have heq1 : (∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((t : ℂ) + ε * I))) =
      ∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + t + ε * I) := by simp only [add_assoc]
  have heq2 : (∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((ε : ℂ) + y * I))) =
      ∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ε + y * I) := by simp only [add_assoc]
  rw [heq1, heq2]
  dsimp only [upperRightCap]
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
  have hcomb : Tendsto (fun ε : ℝ =>
      ((∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f ((k : ℂ) + ((t : ℂ) + ε * I))) -
        ∫ t in (-ε)..(0 : ℝ), f k / (-2 * π * I * ((t : ℂ) + ε * I))) +
      I * ((∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((k : ℂ) + (-(ε : ℂ) + y * I))) -
        ∫ y in (0 : ℝ)..ε, f k / (-2 * π * I * (-(ε : ℂ) + y * I))) + f k / 4)
      (𝓝[>] 0) (𝓝 (f k / 4)) := by
    simpa using (hb1.add (hb2.const_mul I)).add_const (f k / 4)
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have heq1 : (∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f ((k : ℂ) + ((t : ℂ) + ε * I))) =
      ∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f ((k : ℂ) + t + ε * I) := by simp only [add_assoc]
  have heq2 : (∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((k : ℂ) + (-(ε : ℂ) + y * I))) =
      ∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((k : ℂ) - ε + y * I) :=
    integral_congr fun y _ => by rw [sub_eq_add_neg, add_assoc]
  rw [heq1, heq2]
  dsimp only [upperLeftCap, k]
  linear_combination -upperLeftCap_model (f ((j + 1 : ℤ) : ℂ)) hε

/-! ### General complex Abel–Plana formula and Schwarz-symmetric specialization -/

/-- Right-hand limit `∫_{Ioi ε} g → ∫_{Ioi 0} g` as `ε → 0⁺` for an integrable function on
`Ioi 0`. -/
private theorem tendsto_setIntegral_Ioi_nhdsWithin_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} (hg : IntegrableOn g (Ioi 0)) :
    Tendsto (fun ε : ℝ => ∫ y in Ioi ε, g y) (𝓝[>] 0) (𝓝 (∫ y in Ioi 0, g y)) := by
  have hcov : AECover (volume.restrict (Ioi (0 : ℝ))) (𝓝[>] (0 : ℝ)) (fun ε : ℝ => Ioi ε) :=
    aecover_Ioi_of_Ioi (tendsto_id.mono_left nhdsWithin_le_nhds)
  refine (hcov.integral_tendsto_of_countably_generated hg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left (mem_Ioi.mp hε).le]

/-- Shrinking-endpoint limit `∫_{j+ε}^{j+1-ε} h → ∫_j^{j+1} h` as `ε → 0⁺` for continuous `h`. -/
private theorem tendsto_intervalIntegral_add_sub_nhdsWithin_zero {h : ℝ → ℂ} (j : ℤ)
    (hcont : ContinuousOn h (Icc (j : ℝ) ((j : ℝ) + 1))) :
    Tendsto (fun ε : ℝ => ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), h x) (𝓝[>] 0)
      (𝓝 (∫ x in (j : ℝ)..((j : ℝ) + 1), h x)) := by
  have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun ε : ℝ => (j : ℝ) + ε) (𝓝[>] 0) (𝓝 (j : ℝ)) := by
    simpa using tendsto_const_nhds.add h0
  have hb : Tendsto (fun ε : ℝ => (j : ℝ) + 1 - ε) (𝓝[>] 0) (𝓝 ((j : ℝ) + 1)) := by
    simpa using tendsto_const_nhds.sub h0
  have hcov := aecover_Ioc_of_Ioc (μ := volume) ha hb
  have hint : IntegrableOn h (Ioc (j : ℝ) ((j : ℝ) + 1)) :=
    (hcont.intervalIntegrable_of_Icc (by linarith)).1
  have hlim := hcov.integral_tendsto_of_countably_generated hint
  rw [← intervalIntegral.integral_of_le (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
  have hle : (j : ℝ) + ε ≤ (j : ℝ) + 1 - ε := by linarith [hε.1, hε.2]
  have hsub : Ioc ((j : ℝ) + ε) ((j : ℝ) + 1 - ε) ⊆ Ioc (j : ℝ) ((j : ℝ) + 1) :=
    Ioc_subset_Ioc (by linarith [hε.1]) (by linarith [hε.1])
  rw [intervalIntegral.integral_of_le hle, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_self_of_subset_left hsub]

/-- Schwarz conjugate `z ↦ conj (f (conj z))` used to deduce the lower half-plane contour identity
from the upper half-plane one. -/
private noncomputable def schwarzConjFun (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (f (conj z))

private theorem differentiableOn_schwarzConjFun {f : ℂ → ℂ} {a b : ℝ}
    (hf : DifferentiableOn ℂ f {z | a < z.re ∧ z.re < b}) :
    DifferentiableOn ℂ (schwarzConjFun f) {z | a < z.re ∧ z.re < b} := by
  have himg : conj '' {z : ℂ | a < z.re ∧ z.re < b} = {z : ℂ | a < z.re ∧ z.re < b} := by
    ext z
    exact ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw,
      fun hz => ⟨conj z, by simpa using hz, starRingEnd_self_apply z⟩⟩
  exact himg ▸ differentiableOn_conj_conj hf

private theorem continuousOn_schwarzConjFun {f : ℂ → ℂ} {a b : ℝ}
    (hcont : ContinuousOn f {z | a ≤ z.re ∧ z.re ≤ b}) :
    ContinuousOn (schwarzConjFun f) {z | a ≤ z.re ∧ z.re ≤ b} :=
  Complex.continuous_conj.comp_continuousOn
    (hcont.comp Complex.continuous_conj.continuousOn fun z hz => by simpa using hz)

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
      (hc (continuousOn_schwarzConjFun hcont))).intervalIntegrable_of_Icc (μ := volume) hle1
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
    rw [show (Real.exp (2 * π * y) : ℂ) - 1 = ((Real.exp (2 * π * y) - 1 : ℝ) : ℂ) by
      push_cast; rfl]
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
      (hv (continuousOn_schwarzConjFun hcont))).intervalIntegrable_of_Icc (μ := volume) hεT
  rw [← intervalIntegral.intervalIntegral_conj,
    show ∀ u v : ℂ, I * u + (-I) * v = I * (u - v) by intros; ring,
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
    (upper_rect_identity han hε0 hε2 hεT (differentiableOn_schwarzConjFun hf)
      (continuousOn_schwarzConjFun hcont))
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
  have hT_eq : ∀ᶠ T : ℝ in atTop,
      (∫ x in (a : ℝ)..n, abelPlanaUpper f (x + T * I)) +
        conj (∫ x in (a : ℝ)..n, abelPlanaUpper (schwarzConjFun f) (x + T * I)) +
        I * (∫ y in ε..T, (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) -
        I * (∫ y in ε..T, (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) =
      (- ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x) +
        (∑ j ∈ Finset.Ico a n,
          (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
            upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε))) := by
    filter_upwards [eventually_ge_atTop ε] with T hεT
    exact combined_rect_identity han hε0 hε2 hεT hf hcont
  have hlim_top1 := tendsto_integral_abelPlanaUpper_atTop han.le hgrowth
  have hlim_top2 : Tendsto
      (fun T : ℝ => conj (∫ x in (a : ℝ)..n, abelPlanaUpper (schwarzConjFun f) (x + T * I)))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_conj.tendsto 0).comp
      (tendsto_integral_abelPlanaUpper_atTop han.le (tendsto_schwarzConjFun_growth hgrowth))
  have hlim_va :=
    intervalIntegral_tendsto_integral_Ioi ε (hinta.mono_set (Ioi_subset_Ioi hε0.le)) tendsto_id
  have hlim_vn :=
    intervalIntegral_tendsto_integral_Ioi ε (hintn.mono_set (Ioi_subset_Ioi hε0.le)) tendsto_id
  have hlim_lhs := (((hlim_top1.add hlim_top2).add (hlim_va.const_mul I)).sub
    (hlim_vn.const_mul I))
  simp only [zero_add] at hlim_lhs
  exact (tendsto_nhds_unique (hlim_lhs.congr' hT_eq) tendsto_const_nhds).symm

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
  have hcont_conj := continuousOn_schwarzConjFun hcont
  have hlim_seg : Tendsto
      (fun ε : ℝ => - ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x)
      (𝓝[>] 0) (𝓝 (- ∫ x in (a : ℝ)..n, f x)) := by
    have hcont_real : ContinuousOn (fun x : ℝ => f x) (Icc (a : ℝ) n) :=
      hcont.comp Complex.continuous_ofReal.continuousOn fun x hx => ⟨by simp [hx.1], by simp [hx.2]⟩
    rw [integral_eq_sum_Ico_unit han.le hcont_real]
    refine (tendsto_finsetSum _ fun j hj => ?_).neg
    obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
    exact tendsto_intervalIntegral_add_sub_nhdsWithin_zero j
      (hcont_real.mono (Icc_subset_Icc (by exact_mod_cast hja) (by exact_mod_cast hjn)))
  have hlim_caps : Tendsto
      (fun ε : ℝ => ∑ j ∈ Finset.Ico a n,
        (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
          upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε)))
      (𝓝[>] 0) (𝓝 ((∑ j ∈ Finset.Icc a n, f j) - f a / 2 - f n / 2)) := by
    rw [← sum_Ico_half_add_half han]
    refine tendsto_finsetSum _ fun j hj => ?_
    have hr1 := tendsto_upperRightCap hj hcont
    have hr2 := (Complex.continuous_conj.tendsto _).comp (tendsto_upperRightCap hj hcont_conj)
    have hl1 := tendsto_upperLeftCap hj hcont
    have hl2 := (Complex.continuous_conj.tendsto _).comp (tendsto_upperLeftCap hj hcont_conj)
    have hsum4 := ((hr1.add hr2).add hl1).add hl2
    have hval : f j / 4 + conj (schwarzConjFun f j / 4) + f ((j + 1 : ℤ) : ℂ) / 4 +
        conj (schwarzConjFun f ((j + 1 : ℤ) : ℂ) / 4) =
        f j / 2 + f ((j + 1 : ℤ) : ℂ) / 2 := by
      dsimp only [schwarzConjFun]
      simp only [map_div₀, map_ofNat, map_intCast, starRingEnd_self_apply]; ring
    rwa [hval] at hsum4
  have hlim_rhs := ((tendsto_setIntegral_Ioi_nhdsWithin_zero hinta).const_mul I).sub
    ((tendsto_setIntegral_Ioi_nhdsWithin_zero hintn).const_mul I)
  have heq_ev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (- ∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), f x) +
        (∑ j ∈ Finset.Ico a n,
          (upperRightCap f j ε + conj (upperRightCap (schwarzConjFun f) j ε) +
            upperLeftCap f (j + 1) ε + conj (upperLeftCap (schwarzConjFun f) (j + 1) ε))) =
      I * (∫ y in Ioi ε, (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) -
        I * (∫ y in Ioi ε, (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    exact combined_strip_identity han hε.1 hε.2 hf hcont hgrowth hinta hintn
  linear_combination tendsto_nhds_unique ((hlim_seg.add hlim_caps).congr' heq_ev) hlim_rhs

/-- **Schwarz reflection symmetry on a closed vertical strip.** If `f` is holomorphic on the open
strip `a < Re z < b` (`a < b`), continuous on the closed strip `a ≤ Re z ≤ b`, and real on `[a, b]`,
then `f (conj z) = conj (f z)` throughout the closed strip. -/
theorem conj_apply_eq_of_im_eq_zero_on_strip {f : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : DifferentiableOn ℂ f {z | a < z.re ∧ z.re < b})
    (hcont : ContinuousOn f {z | a ≤ z.re ∧ z.re ≤ b})
    (hreal : ∀ x : ℝ, a ≤ x → x ≤ b → (f x).im = 0)
    {z : ℂ} (hz : z ∈ {w : ℂ | a ≤ w.re ∧ w.re ≤ b}) :
    f (conj z) = conj (f z) := by
  let Ω : Set ℂ := {w : ℂ | a < w.re ∧ w.re < b}
  let S : Set ℂ := {w : ℂ | a ≤ w.re ∧ w.re ≤ b}
  let G : ℂ → ℂ := fun w => f w - schwarzConjFun f w
  have hΩsymm : MapsTo (starRingEnd ℂ) Ω Ω := fun w hw => by simpa [Ω] using hw
  have hGcont : ContinuousOn G S := hcont.sub (continuousOn_schwarzConjFun hcont)
  have hGupper : EqOn G 0 (Ω ∩ {w : ℂ | 0 ≤ w.im}) :=
    eqOn_zero_of_zero_on_real_axis (isOpen_Ioo.preimage Complex.continuous_re)
      ((convex_Ioo a b).linear_preimage Complex.reLm).isPreconnected hΩsymm
      (x := (a + b) / 2) (by simp [Ω]; constructor <;> linarith)
      (hGcont.mono (Set.inter_subset_left.trans fun _ hw => ⟨hw.1.le, hw.2.le⟩))
      ((hf.sub (differentiableOn_schwarzConjFun hf)).mono Set.inter_subset_left) fun w hw hw0 => by
        rw [show w = (w.re : ℂ) from Complex.ext rfl hw0]
        dsimp only [G, schwarzConjFun]
        rw [Complex.conj_ofReal]
        exact sub_eq_zero.mpr (Complex.conj_eq_iff_im.mpr (hreal w.re hw.1.le hw.2.le)).symm
  have hGΩ : EqOn G 0 Ω := fun w hw => by
    rcases le_or_gt 0 w.im with hw_im | hw_im
    · exact hGupper ⟨hw, hw_im⟩
    · have h1 := congrArg (starRingEnd ℂ) (hGupper ⟨hΩsymm hw, by simp; linarith⟩)
      dsimp only [G, schwarzConjFun, Pi.zero_apply] at h1 ⊢
      simp only [map_sub, starRingEnd_self_apply, map_zero] at h1
      linear_combination -h1
  have hG_S : G z = 0 := by
    let u : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * z + (t : ℂ) * (((a + b) / 2 : ℝ) : ℂ)
    have hu_mem : ∀ t ∈ Ioo (0 : ℝ) 1, u t ∈ Ω := fun t ht => by
      have hre : (u t).re = (1 - t) * z.re + t * ((a + b) / 2) := by simp [u]
      exact ⟨by rw [hre]; nlinarith [hz.1, ht.1, ht.2], by rw [hre]; nlinarith [hz.2, ht.1, ht.2]⟩
    have hu_S : Tendsto u (𝓝[>] 0) (𝓝[S] z) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa [u] using ((by fun_prop : Continuous u).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
            exact ⟨(hu_mem t ht).1.le, (hu_mem t ht).2.le⟩)
    refine tendsto_nhds_unique ((hGcont z hz).tendsto.comp hu_S) (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht using (hGΩ (hu_mem t ht)).symm
  simpa [schwarzConjFun] using (congrArg (starRingEnd ℂ) (sub_eq_zero.mp hG_S)).symm

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
      have hsymm := conj_apply_eq_of_im_eq_zero_on_strip han' hf hcont hreal
        (z := (k : ℂ) + (y : ℂ) * I) ⟨by simp [hka], by simp [hkn]⟩
      rw [show (k : ℂ) - (y : ℂ) * I = conj ((k : ℂ) + (y : ℂ) * I) by simp [sub_eq_add_neg],
        hsymm, Complex.sub_conj]
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
exp (c * |z.im|)` on the closed strip `{a ≤ z.re ≤ b}` with `c < 2 * π`, then
`f z * exp (-(2 * π * |z.im|)) → 0` as `|z.im| → ∞` uniformly in the strip. -/
theorem tendsto_mul_exp_neg_two_pi_abs_im_of_norm_le {f : ℂ → ℂ} {a b C p c : ℝ}
    (hc : c < 2 * π)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) :
    Tendsto (fun z => f z * Real.exp (-(2 * π * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) (𝓝 0) := by
  have hd : 0 < 2 * π - c := sub_pos.mpr hc
  have hdec : Tendsto (fun t : ℝ => |C| * (t ^ p * Real.exp (-(2 * π - c) * t))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (2 * π - c) hd).const_mul |C|
  have hmaj : Tendsto (fun z : ℂ =>
      |C| * ((1 + |z.im|) ^ p * Real.exp (-(2 * π - c) * (1 + |z.im|))) * Real.exp (2 * π - c))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) (𝓝 0) := by
    simpa [Function.comp_def] using
      (((hdec.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const
        (Real.exp (2 * π - c))).comp (tendsto_comap.mono_left inf_le_left))
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj)
  filter_upwards [mem_inf_of_right (mem_principal_self {z : ℂ | a ≤ z.re ∧ z.re ≤ b})] with z hz
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (c * |z.im|) * Real.exp (-(2 * π * |z.im|)) =
      Real.exp (-(2 * π - c) * (1 + |z.im|)) * Real.exp (2 * π - c) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    ‖f z‖ * Real.exp (-(2 * π * |z.im|))
      ≤ (C * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(2 * π * |z.im|)) := by
        gcongr; exact hbound z hz.1 hz.2
    _ ≤ (|C| * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(2 * π * |z.im|)) := by
        gcongr; exact le_abs_self C
    _ = |C| * ((1 + |z.im|) ^ p * Real.exp (-(2 * π - c) * (1 + |z.im|))) *
          Real.exp (2 * π - c) := by
        linear_combination |C| * (1 + |z.im|) ^ p * hexp

end TauCeti
