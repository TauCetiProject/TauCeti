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

/-- `e^{-2πiz} ≠ 1` off the real axis. -/
private theorem cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    cexp (-2 * π * I * z) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hzki : -z * (2 * π * I) = (k : ℂ) * (2 * π * I) := by linear_combination hk
  have hz_eq : z = (-k : ℤ) := by
    have hneg := mul_right_cancel₀ hpi hzki
    push_cast
    linear_combination -hneg
  apply hz
  rw [hz_eq]
  exact Complex.intCast_im _

/-- `e^{-2πiz} ≠ 1` whenever `Re z` lies strictly between two consecutive integers. -/
private theorem cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo {z : ℂ} (j : ℤ)
    (hz : z.re ∈ Ioo (j : ℝ) (j + 1)) : cexp (-2 * π * I * z) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hzki : -z * (2 * π * I) = (k : ℂ) * (2 * π * I) := by linear_combination hk
  have hz_re : z.re = ((-k : ℤ) : ℝ) := by
    have hneg := mul_right_cancel₀ hpi hzki
    have hz_eq : z = ((-k : ℤ) : ℂ) := by push_cast; linear_combination -hneg
    simpa using congrArg Complex.re hz_eq
  have hlt1 : (j : ℝ) < ((-k : ℤ) : ℝ) := by linarith [hz.1]
  have hlt2 : ((-k : ℤ) : ℝ) < ((j + 1 : ℤ) : ℝ) := by rw [← hz_re]; push_cast; linarith [hz.2]
  have hk1 : j < -k := Int.cast_lt.mp hlt1
  have hk2 : -k < j + 1 := Int.cast_lt.mp hlt2
  omega

/-- On `(j, j + 1)`, combining `g₊` with the conjugate of `g₊` for `conj ∘ f ∘ conj` gives
`-f(x)`. -/
private theorem abelPlanaUpper_add_conj_comp (f : ℂ → ℂ) {x : ℝ} (j : ℤ)
    (hx : x ∈ Ioo (j : ℝ) (j + 1)) :
    abelPlanaUpper f x +
      conj (abelPlanaUpper (fun z => conj (f (conj z))) x) = -f x := by
  dsimp only [abelPlanaUpper]
  simp only [map_div₀, map_sub, map_one, map_ofNat, Complex.conj_ofReal, starRingEnd_self_apply,
    ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I]
  set w : ℂ := cexp (-2 * π * I * (x : ℂ))
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr
    (cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j (by simpa using hx))
  have hpos : cexp (-2 * ↑π * -I * ↑x) = w⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [hpos]
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hw1' : 1 - w ≠ 0 := fun h0 => hw1 (by linear_combination -h0)
  have : w⁻¹ - 1 ≠ 0 := by
    intro h0
    exact hw1 (sub_eq_zero.mpr (inv_eq_one.mp (sub_eq_zero.mp h0)))
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
    have hstep : a + m ≤ a + (m + 1 : ℕ) := by omega
    have hstep' : ((a + m : ℤ) : ℝ) ≤ ((a + (m + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hstep
    have hcont1 : ContinuousOn h (Icc (a : ℝ) ((a + m : ℤ) : ℝ)) :=
      hcont.mono (Icc_subset_Icc le_rfl hstep')
    have hint1 : IntervalIntegrable h volume (a : ℝ) ((a + m : ℤ) : ℝ) :=
      hcont1.intervalIntegrable_of_Icc (by exact_mod_cast hm1)
    have hint2 : IntervalIntegrable h volume ((a + m : ℤ) : ℝ) ((a + (m + 1 : ℕ) : ℤ) : ℝ) :=
      (hcont.mono (Icc_subset_Icc (by exact_mod_cast hm1) le_rfl)).intervalIntegrable_of_Icc hstep'
    have hIco : Finset.Ico a (a + (m + 1 : ℕ)) = insert (a + m) (Finset.Ico a (a + m)) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIco, Finset.sum_insert (by simp), ← ih hm1 hcont1,
      ← integral_add_adjacent_intervals hint1 hint2]
    have htop : ((a + (m + 1 : ℕ) : ℤ) : ℝ) = ((a + m : ℤ) : ℝ) + 1 := by push_cast; ring
    rw [htop, add_comm]

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
    have hne : a + 1 ∉ ({a} : Finset ℤ) := by simp
    rw [hIco, hIcc, Finset.sum_singleton, Finset.sum_insert hne, Finset.sum_singleton]
    push_cast
    ring
  | succ m ih =>
    have han' : a < a + (m + 1 : ℕ) := by omega
    have hIco : Finset.Ico a (a + (m + 1 + 1 : ℕ)) =
        insert (a + (m + 1 : ℕ)) (Finset.Ico a (a + (m + 1 : ℕ))) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hIcc : Finset.Icc a (a + (m + 1 + 1 : ℕ)) =
        insert (a + (m + 1 + 1 : ℕ)) (Finset.Icc a (a + (m + 1 : ℕ))) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hne1 : a + (m + 1 : ℕ) ∉ Finset.Ico a (a + (m + 1 : ℕ)) := by simp
    have hne2 : a + (m + 1 + 1 : ℕ) ∉ Finset.Icc a (a + (m + 1 : ℕ)) := by simp
    rw [hIco, hIcc, Finset.sum_insert hne1, Finset.sum_insert hne2, ih han']
    have hstep : a + (m + 1 : ℕ) + 1 = a + (m + 1 + 1 : ℕ) := by omega
    rw [hstep]
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

/-- Decomposing `∫_{j}^{j+1} g₊(x + iε) dx` via Cauchy's theorem on the pole-free bottom strip
`[j + ε, j + 1 - ε] × [0, ε]`. -/
private theorem cauchy_bottom_strip {f : ℂ → ℂ} {a n j : ℤ} {ε : ℝ}
    (hj : j ∈ Finset.Ico a n) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hf : DifferentiableOn ℂ f {z | (a : ℝ) < z.re ∧ z.re < n})
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    ((∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) -
      ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f (x + ε * I)) +
      I * (∫ y in (0 : ℝ)..ε, abelPlanaUpper f (↑((j : ℝ) + 1 - ε) + ↑y * I)) -
      I * (∫ y in (0 : ℝ)..ε, abelPlanaUpper f (↑((j : ℝ) + ε) + ↑y * I)) = 0 := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hle1 : (j : ℝ) + ε ≤ (j : ℝ) + 1 - ε := by linarith
  let z₀ : ℂ := ((j : ℝ) + ε : ℝ)
  let w₀ : ℂ := (((j : ℝ) + 1 - ε : ℝ) : ℂ) + (ε : ℂ) * I
  have hzre : z₀.re = (j : ℝ) + ε := by simp [z₀]
  have hzim : z₀.im = 0 := by simp [z₀]
  have hwre : w₀.re = (j : ℝ) + 1 - ε := by simp [w₀]
  have hwim : w₀.im = ε := by simp [w₀]
  have hrect_sub : ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) ⊆
      {z : ℂ | (a : ℝ) ≤ z.re ∧ z.re ≤ n} := by
    intro z hz
    rw [hzre, hwre, hzim, hwim, Set.uIcc_of_le hle1, Set.uIcc_of_le hε0.le] at hz
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have hrect_ne : ∀ z ∈ ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]),
      cexp (-2 * π * I * z) - 1 ≠ 0 := by
    intro z hz
    rw [hzre, hwre, Set.uIcc_of_le hle1] at hz
    exact sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j
      ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩)
  have hcont_rect : ContinuousOn (abelPlanaUpper f) ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) :=
    (hcont.mono hrect_sub).div (by fun_prop) hrect_ne
  have hdiff_rect : DifferentiableOn ℂ (abelPlanaUpper f)
      (Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ Ioo (min z₀.im w₀.im) (max z₀.im w₀.im)) := by
    have hopen_sub :
        (Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ Ioo (min z₀.im w₀.im) (max z₀.im w₀.im)) ⊆
        {z : ℂ | (a : ℝ) < z.re ∧ z.re < n} := by
      intro z hz
      rw [hzre, hwre, min_eq_left hle1, max_eq_right hle1] at hz
      exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    refine (hf.mono hopen_sub).div (by fun_prop) fun z hz => hrect_ne z ?_
    exact ⟨Ioo_subset_Icc_self (by simpa [Set.uIcc_of_le, min_le_max] using hz.1),
      Ioo_subset_Icc_self (by simpa [Set.uIcc_of_le, min_le_max] using hz.2)⟩
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (abelPlanaUpper f) z₀ w₀ hcont_rect hdiff_rect
  simpa only [hzre, hzim, hwre, hwim, Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul]
    using hcauchy

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
  have hcauchy := cauchy_bottom_strip hj hε0 hε2 hf hcont
  have hcont_line : ContinuousOn (fun x : ℝ => abelPlanaUpper f (x + ε * I))
      (Icc (j : ℝ) ((j : ℝ) + 1)) := by
    refine ContinuousOn.div ?_ (by fun_prop) fun x _ => sub_ne_zero.mpr
      (cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by simp [hε0.ne']))
    exact hcont.comp (by fun_prop) fun x hx => ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩
  have hint1 : IntervalIntegrable (fun x : ℝ => abelPlanaUpper f (x + ε * I)) volume
      (j : ℝ) ((j : ℝ) + ε) :=
    (hcont_line.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hint2 : IntervalIntegrable (fun x : ℝ => abelPlanaUpper f (x + ε * I)) volume
      ((j : ℝ) + ε) ((j : ℝ) + 1 - ε) :=
    (hcont_line.mono (Icc_subset_Icc (by linarith) (by linarith))).intervalIntegrable_of_Icc hle1
  have hint3 : IntervalIntegrable (fun x : ℝ => abelPlanaUpper f (x + ε * I)) volume
      ((j : ℝ) + 1 - ε) ((j : ℝ) + 1) :=
    (hcont_line.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
  have hsplit : ∫ x in (j : ℝ)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I) =
      (∫ x in (j : ℝ)..((j : ℝ) + ε), abelPlanaUpper f (x + ε * I)) +
      (∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f (x + ε * I)) +
      (∫ x in ((j : ℝ) + 1 - ε)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I)) := by
    rw [← integral_add_adjacent_intervals (hint1.trans hint2) hint3,
      ← integral_add_adjacent_intervals hint1 hint2]
  have hshiftR : ∫ x in (j : ℝ)..((j : ℝ) + ε), abelPlanaUpper f (x + ε * I) =
      ∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + t + ε * I) := by
    have h := (integral_comp_add_right (fun x : ℝ => abelPlanaUpper f (x + ε * I)) (j : ℝ)
      (a := 0) (b := ε)).symm
    rw [zero_add, add_comm ε (j : ℝ)] at h
    refine h.trans (integral_congr fun t _ => ?_)
    congr 1
    push_cast
    ring
  have hshiftL : ∫ x in ((j : ℝ) + 1 - ε)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I) =
      ∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + t + ε * I) := by
    have h := (integral_comp_add_right (fun x : ℝ => abelPlanaUpper f (x + ε * I))
      ((j : ℝ) + 1) (a := -ε) (b := 0)).symm
    rw [show -ε + ((j : ℝ) + 1) = (j : ℝ) + 1 - ε by ring, zero_add] at h
    refine h.trans (integral_congr fun t _ => ?_)
    congr 1
    push_cast
    ring
  have hcastR : (∫ y in (0 : ℝ)..ε, abelPlanaUpper f (↑((j : ℝ) + ε) + ↑y * I)) =
      ∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ε + y * I) := by
    refine integral_congr fun y _ => ?_
    congr 1
    push_cast
    ring
  have hcastL : (∫ y in (0 : ℝ)..ε, abelPlanaUpper f (↑((j : ℝ) + 1 - ε) + ↑y * I)) =
      ∫ y in (0 : ℝ)..ε, abelPlanaUpper f (((j + 1 : ℤ) : ℂ) - ε + y * I) := by
    refine integral_congr fun y _ => ?_
    congr 1
    push_cast
    ring
  rw [hcastR, hcastL] at hcauchy
  rw [hsplit, hshiftR, hshiftL]
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
  let z₀ : ℂ := (a : ℂ) + (ε : ℂ) * I
  let w₀ : ℂ := (n : ℂ) + (T : ℂ) * I
  have hzre : z₀.re = a := by simp [z₀]
  have hzim : z₀.im = ε := by simp [z₀]
  have hwre : w₀.re = n := by simp [w₀]
  have hwim : w₀.im = T := by simp [w₀]
  have hrect_sub : ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) ⊆
      {z : ℂ | (a : ℝ) ≤ z.re ∧ z.re ≤ n} := by
    intro z hz
    rw [hzre, hwre, Set.uIcc_of_le han'] at hz
    exact hz.1
  have hrect_ne : ∀ z ∈ ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]),
      cexp (-2 * π * I * z) - 1 ≠ 0 := by
    intro z hz
    rw [hzim, hwim, Set.uIcc_of_le hεT] at hz
    exact sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by linarith [hz.2.1]))
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (abelPlanaUpper f) z₀ w₀ ((hcont.mono hrect_sub).div (by fun_prop) hrect_ne) <| by
      have hopen_sub :
          (Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ Ioo (min z₀.im w₀.im) (max z₀.im w₀.im)) ⊆
          {z : ℂ | (a : ℝ) < z.re ∧ z.re < n} := by
        intro z hz
        rw [hzre, hwre, min_eq_left han', max_eq_right han'] at hz
        exact hz.1
      refine (hf.mono hopen_sub).div (by fun_prop) fun z hz => hrect_ne z ?_
      exact ⟨Ioo_subset_Icc_self (by simpa [Set.uIcc_of_le, min_le_max] using hz.1),
        Ioo_subset_Icc_self (by simpa [Set.uIcc_of_le, min_le_max] using hz.2)⟩
  simp only [hzre, hzim, hwre, hwim, Complex.ofReal_intCast, smul_eq_mul] at hcauchy
  have hcont_line : ContinuousOn (fun x : ℝ => abelPlanaUpper f (x + ε * I)) (Icc (a : ℝ) n) := by
    refine ContinuousOn.div ?_ (by fun_prop) fun x _ => sub_ne_zero.mpr
      (cexp_neg_two_pi_I_mul_ne_one_of_im_ne_zero (by simp [hε0.ne']))
    exact hcont.comp (by fun_prop) fun x hx => ⟨by simp [hx.1], by simp [hx.2]⟩
  have hsum_adj := integral_eq_sum_Ico_unit han.le hcont_line
  have hsum_units :
      (∑ j ∈ Finset.Ico a n, ∫ x in (j : ℝ)..((j : ℝ) + 1), abelPlanaUpper f (x + ε * I)) =
        (∑ j ∈ Finset.Ico a n, ∫ x in ((j : ℝ) + ε)..((j : ℝ) + 1 - ε), abelPlanaUpper f x) +
          ∑ j ∈ Finset.Ico a n, (upperRightCap f j ε + upperLeftCap f (j + 1) ε) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [upper_unit_strip_eq hj hε0 hε2 hf hcont, add_assoc]
  have hverta : (∫ y in ε..T, abelPlanaUpper f (a + y * I)) =
      ∫ y in ε..T, f (a + y * I) / (Real.exp (2 * π * y) - 1) := by
    refine integral_congr fun y _ => ?_
    dsimp only [abelPlanaUpper]
    rw [cexp_neg_two_pi_I_mul_int_add_mul_I]
  have hvertn : (∫ y in ε..T, abelPlanaUpper f (n + y * I)) =
      ∫ y in ε..T, f (n + y * I) / (Real.exp (2 * π * y) - 1) := by
    refine integral_congr fun y _ => ?_
    dsimp only [abelPlanaUpper]
    rw [cexp_neg_two_pi_I_mul_int_add_mul_I]
  rw [hverta, hvertn, hsum_adj, hsum_units] at hcauchy
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
  have hδ' : 0 < δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1) := by positivity
  have hmem := hgrowth.eventually (Metric.ball_mem_nhds 0 hδ')
  rw [Filter.eventually_inf_principal, Filter.eventually_comap] at hmem
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hmem
  rw [Filter.eventually_atTop]
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  rw [dist_zero_right]
  have hbound : ∀ x ∈ Ioc (a : ℝ) n, ‖abelPlanaUpper f (x + T * I)‖ ≤ δ / ((n : ℝ) - a + 1) := by
    intro x hx
    set z : ℂ := (x : ℂ) + (T : ℂ) * I
    have hz_im : |z.im| = T := by simp [z, abs_of_pos hTpos]
    have hz_strip : z ∈ {w : ℂ | (a : ℝ) ≤ w.re ∧ w.re ≤ n} :=
      ⟨by simp [z, hx.1.le], by simp [z, hx.2]⟩
    have hsmall : ‖f z * Real.exp (-(2 * π * T))‖ <
        δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1) := by
      have h := hT₀ T hTT₀ z hz_im hz_strip
      simpa [hz_im, dist_zero_right] using h
    have hsmall' : ‖f z‖ * Real.exp (-(2 * π * T)) ≤
        δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1) := by
      have hnorm : ‖f z * (Real.exp (-(2 * π * T)) : ℂ)‖ = ‖f z‖ * Real.exp (-(2 * π * T)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hnorm ▸ hsmall.le
    have hexp_norm : ‖cexp (-2 * π * I * z)‖ = Real.exp (2 * π * T) := by
      have hre : (-2 * π * I * z).re = 2 * π * T := by simp [z]
      rw [Complex.norm_exp, hre]
    have hden_ge : Real.exp (2 * π * T) - 1 ≤ ‖cexp (-2 * π * I * z) - 1‖ := by
      have htri := norm_sub_norm_le (cexp (-2 * π * I * z)) 1
      rw [hexp_norm, norm_one] at htri
      exact htri
    have hden_pos : 0 < Real.exp (2 * π * T) - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
    have h1T : 1 - Real.exp (-(2 * π)) ≤ 1 - Real.exp (-(2 * π * T)) := by
      have : Real.exp (-(2 * π * T)) ≤ Real.exp (-(2 * π)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith
    have hfac : (Real.exp (2 * π * T) - 1) * Real.exp (-(2 * π * T)) =
        1 - Real.exp (-(2 * π * T)) := by
      rw [sub_mul, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    dsimp only [abelPlanaUpper]
    rw [norm_div]
    calc
      ‖f z‖ / ‖cexp (-2 * π * I * z) - 1‖ ≤ ‖f z‖ / (Real.exp (2 * π * T) - 1) := by gcongr
      _ = (‖f z‖ * Real.exp (-(2 * π * T))) / (1 - Real.exp (-(2 * π * T))) := by
        rw [← hfac, div_mul_eq_div_div_swap, mul_div_cancel_right₀ _ (Real.exp_pos _).ne']
      _ ≤ (δ * (1 - Real.exp (-(2 * π))) / ((n : ℝ) - a + 1)) / (1 - Real.exp (-(2 * π))) := by
        gcongr
      _ = δ / ((n : ℝ) - a + 1) := by field_simp
  have hint_norm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a : ℝ)) (b := n)
    (C := δ / ((n : ℝ) - a + 1)) (fun x hx => hbound x (by rwa [uIoc_of_le han'] at hx))
  rw [abs_of_nonneg (sub_nonneg.mpr han')] at hint_norm
  refine lt_of_le_of_lt hint_norm ?_
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ hlen_pos).mpr (by linarith)

/-- Exact logarithm difference `log ε - log (iε) = -iπ / 2` for `ε > 0`. -/
private theorem log_sub_log_mul_I {ε : ℝ} (hε : 0 < ε) :
    Complex.log (ε : ℂ) - Complex.log ((ε : ℂ) * I) = -((π / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re, abs_of_pos hε]
  · simp [Complex.log_im, Complex.arg_ofReal_of_nonneg hε.le, Complex.arg_real_mul I hε,
      Complex.arg_I]

/-- Exact evaluation of the singular model for the upper-right quarter-box indent. -/
private theorem upperRightCap_model (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0 : ℝ)..ε, c / (-2 * π * I * ((t : ℂ) + ε * I))) -
      I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * ((ε : ℂ) + y * I))) = c / 4 := by
  have h1 : ∫ t in (0 : ℝ)..ε, ((t : ℂ) + ε * I)⁻¹ =
      Complex.log ((ε : ℂ) + ε * I) - Complex.log ((ε : ℂ) * I) := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) ε,
        HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) + ε * I)) (((t : ℂ) + ε * I)⁻¹) t := by
      intro t _
      have hslit : (t : ℂ) + ε * I ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [hε.ne']))
      have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) + ε * I) 1 t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((ε : ℂ) * I)
      simpa [Function.comp_def] using (Complex.hasDerivAt_log hslit).scomp t hinner
    have hint : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + ε * I)⁻¹) volume 0 ε := by
      refine ContinuousOn.intervalIntegrable (fun t _ => ContinuousAt.continuousWithinAt ?_)
      exact (continuous_ofReal.add continuous_const).continuousAt.inv₀
        (by intro h0; have := congrArg Complex.im h0; simp [hε.ne'] at this)
    simpa using integral_eq_sub_of_hasDerivAt hd hint
  have h2 : ∫ y in (0 : ℝ)..ε, ((ε : ℂ) + y * I)⁻¹ * I =
      Complex.log ((ε : ℂ) + ε * I) - Complex.log (ε : ℂ) := by
    have hd : ∀ y ∈ Set.uIcc (0 : ℝ) ε,
        HasDerivAt (fun y : ℝ => Complex.log ((ε : ℂ) + y * I)) (((ε : ℂ) + y * I)⁻¹ * I) y := by
      intro y _
      have hslit : (ε : ℂ) + y * I ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simp [hε]))
      have hinner : HasDerivAt (fun y : ℝ => (ε : ℂ) + y * I) I y := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (ε : ℂ)
      simpa [Function.comp_def, smul_eq_mul, mul_comm I] using
        (Complex.hasDerivAt_log hslit).scomp y hinner
    have hint : IntervalIntegrable (fun y : ℝ => ((ε : ℂ) + y * I)⁻¹ * I) volume 0 ε := by
      refine ContinuousOn.intervalIntegrable (fun y _ => ContinuousAt.continuousWithinAt ?_)
      exact ((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt.inv₀
        (by intro h0; have := congrArg Complex.re h0; simp [hε.ne'] at this)).mul continuousAt_const
    simpa using integral_eq_sub_of_hasDerivAt hd hint
  have hrew1 : (∫ t in (0 : ℝ)..ε, c / (-2 * π * I * ((t : ℂ) + ε * I))) =
      (c / (-2 * π * I)) * ∫ t in (0 : ℝ)..ε, ((t : ℂ) + ε * I)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv]
  have hrew2 : I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * ((ε : ℂ) + y * I))) =
      (c / (-2 * π * I)) * ∫ y in (0 : ℝ)..ε, ((ε : ℂ) + y * I)⁻¹ * I := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun y _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv]
    ring
  rw [hrew1, hrew2, h1, h2, ← mul_sub,
    show Complex.log ((ε : ℂ) + ε * I) - Complex.log ((ε : ℂ) * I) -
      (Complex.log ((ε : ℂ) + ε * I) - Complex.log (ε : ℂ)) =
      Complex.log (ε : ℂ) - Complex.log ((ε : ℂ) * I) by ring,
    log_sub_log_mul_I hε]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  push_cast
  field_simp
  ring

/-- Exact evaluation of the singular model for the upper-left quarter-box indent, using the rotated
branch `w ↦ log (-i * w)` on the second quadrant. -/
private theorem upperLeftCap_model (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (-ε)..(0 : ℝ), c / (-2 * π * I * ((t : ℂ) + ε * I))) +
      I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * (-(ε : ℂ) + y * I))) = c / 4 := by
  have hrot1 : ∀ t : ℝ, -I * ((t : ℂ) + ε * I) = (ε : ℂ) - (t : ℂ) * I := fun t => by
    calc
      -I * ((t : ℂ) + ε * I) = -(t : ℂ) * I - (ε : ℂ) * (I * I) := by ring
      _ = (ε : ℂ) - (t : ℂ) * I := by rw [I_mul_I]; ring
  have hrot2 : ∀ y : ℝ, -I * (-(ε : ℂ) + y * I) = (y : ℂ) + (ε : ℂ) * I := fun y => by
    calc
      -I * (-(ε : ℂ) + y * I) = -(y : ℂ) * (I * I) + (ε : ℂ) * I := by ring
      _ = (y : ℂ) + (ε : ℂ) * I := by rw [I_mul_I]; ring
  have h1 : ∫ t in (-ε)..(0 : ℝ), ((t : ℂ) + ε * I)⁻¹ =
      Complex.log (ε : ℂ) - Complex.log ((ε : ℂ) + ε * I) := by
    have hd : ∀ t ∈ Set.uIcc (-ε) (0 : ℝ),
        HasDerivAt (fun t : ℝ => Complex.log (-I * ((t : ℂ) + ε * I)))
          (((t : ℂ) + ε * I)⁻¹) t := by
      intro t _
      have hslit : -I * ((t : ℂ) + ε * I) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hrot1]; simp [hε]))
      have hinner : HasDerivAt (fun t : ℝ => -I * ((t : ℂ) + ε * I)) (-I) t := by
        have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) + ε * I) 1 t := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((ε : ℂ) * I)
        simpa using h0.const_mul (-I)
      have hcomp : HasDerivAt (fun t : ℝ => Complex.log (-I * ((t : ℂ) + ε * I)))
          ((-I) * (-I * ((t : ℂ) + ε * I))⁻¹) t := by
        simpa [Function.comp_def, smul_eq_mul] using (Complex.hasDerivAt_log hslit).scomp t hinner
      refine hcomp.congr_deriv ?_
      have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr I_ne_zero
      rw [mul_inv, mul_inv_cancel_left₀ hI0]
    have hint : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + ε * I)⁻¹) volume (-ε) 0 := by
      refine ContinuousOn.intervalIntegrable (fun t _ => ContinuousAt.continuousWithinAt ?_)
      exact (continuous_ofReal.add continuous_const).continuousAt.inv₀
        (by intro h0; have := congrArg Complex.im h0; simp [hε.ne'] at this)
    have hftc := integral_eq_sub_of_hasDerivAt hd hint
    rw [hrot1, hrot1] at hftc
    simpa [sub_neg_eq_add] using hftc
  have h2 : ∫ y in (0 : ℝ)..ε, (-(ε : ℂ) + y * I)⁻¹ * I =
      Complex.log ((ε : ℂ) + ε * I) - Complex.log ((ε : ℂ) * I) := by
    have hd : ∀ y ∈ Set.uIcc (0 : ℝ) ε,
        HasDerivAt (fun y : ℝ => Complex.log (-I * (-(ε : ℂ) + y * I)))
          ((-(ε : ℂ) + y * I)⁻¹ * I) y := by
      intro y _
      have hslit : -I * (-(ε : ℂ) + y * I) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [hrot2]; simp [hε.ne']))
      have hinner : HasDerivAt (fun y : ℝ => -I * (-(ε : ℂ) + y * I)) 1 y := by
        have h0 : HasDerivAt (fun y : ℝ => -(ε : ℂ) + y * I) I y := by
          simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (-(ε : ℂ))
        simpa [neg_mul, I_mul_I] using h0.const_mul (-I)
      have hcomp : HasDerivAt (fun y : ℝ => Complex.log (-I * (-(ε : ℂ) + y * I)))
          ((-I * (-(ε : ℂ) + y * I))⁻¹) y := by
        simpa [Function.comp_def, one_smul] using (Complex.hasDerivAt_log hslit).scomp y hinner
      refine hcomp.congr_deriv ?_
      rw [mul_inv, inv_neg, inv_I, neg_neg, mul_comm]
    have hint : IntervalIntegrable (fun y : ℝ => (-(ε : ℂ) + y * I)⁻¹ * I) volume 0 ε := by
      refine ContinuousOn.intervalIntegrable (fun y _ => ContinuousAt.continuousWithinAt ?_)
      exact ((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt.inv₀
        (by intro h0; have := congrArg Complex.re h0; simp [hε.ne'] at this)).mul continuousAt_const
    have hftc := integral_eq_sub_of_hasDerivAt hd hint
    rw [hrot2, hrot2] at hftc
    simpa using hftc
  have hrew1 : (∫ t in (-ε)..(0 : ℝ), c / (-2 * π * I * ((t : ℂ) + ε * I))) =
      (c / (-2 * π * I)) * ∫ t in (-ε)..(0 : ℝ), ((t : ℂ) + ε * I)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv]
  have hrew2 : I * (∫ y in (0 : ℝ)..ε, c / (-2 * π * I * (-(ε : ℂ) + y * I))) =
      (c / (-2 * π * I)) * ∫ y in (0 : ℝ)..ε, (-(ε : ℂ) + y * I)⁻¹ * I := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun y _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv]
    ring
  rw [hrew1, hrew2, h1, h2, ← mul_add,
    show Complex.log (ε : ℂ) - Complex.log ((ε : ℂ) + ε * I) +
      (Complex.log ((ε : ℂ) + ε * I) - Complex.log ((ε : ℂ) * I)) =
      Complex.log (ε : ℂ) - Complex.log ((ε : ℂ) * I) by ring,
    log_sub_log_mul_I hε]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  push_cast
  field_simp
  ring

/-- Near an integer `k` in the strip `S`, `‖w‖ * ‖g₊(k + w) - f(k) / (-2πiw)‖ → 0` as `w → 0`. -/
private theorem tendsto_norm_mul_abelPlanaUpper_sub {f : ℂ → ℂ} {S : Set ℂ} {k : ℤ}
    (hk : (k : ℂ) ∈ S) (hcont : ContinuousOn f S) :
    Tendsto (fun w : ℂ => ‖w‖ * ‖abelPlanaUpper f ((k : ℂ) + w) - f k / (-2 * π * I * w)‖)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 0) := by
  have hc_ne : (-2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hslope : Tendsto (fun u : ℂ => (cexp u - 1) / u) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    simpa [div_eq_inv_mul] using (Complex.hasDerivAt_exp 0).tendsto_slope_zero
  have hinv : Tendsto (fun u : ℂ => u / (cexp u - 1)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    simpa using hslope.inv₀ one_ne_zero
  have hmap_u : Tendsto (fun w : ℂ => -2 * π * I * w)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont_u : Continuous (fun w : ℂ => -2 * π * I * w) := by fun_prop
      simpa using (hcont_u.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact mul_ne_zero hc_ne hw.1
  have hquot : Tendsto (fun w : ℂ => w / (cexp (-2 * π * I * w) - 1))
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 (1 / (-2 * π * I))) := by
    have h1 := (hinv.comp hmap_u).div_const (-2 * π * I)
    refine h1.congr fun w => ?_
    dsimp only [Function.comp_apply]
    rw [div_right_comm, mul_div_cancel_left₀ _ hc_ne]
  have hf_lim : Tendsto (fun w : ℂ => f ((k : ℂ) + w))
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 (f k)) := by
    have hmap_k : Tendsto (fun w : ℂ => (k : ℂ) + w)
        (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝[S] (k : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hcont_k : Continuous (fun w : ℂ => (k : ℂ) + w) := by fun_prop
        simpa using (hcont_k.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw using hw.2
    exact (hcont (k : ℂ) hk).tendsto.comp hmap_k
  have hprod : Tendsto (fun w : ℂ =>
      f ((k : ℂ) + w) * (w / (cexp (-2 * π * I * w) - 1)) - f k / (-2 * π * I))
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 0) := by
    simpa [div_eq_mul_inv] using (hf_lim.mul hquot).sub_const (f k / (-2 * π * I))
  have hnorm_lim : Tendsto (fun w : ℂ =>
      ‖f ((k : ℂ) + w) * (w / (cexp (-2 * π * I * w) - 1)) - f k / (-2 * π * I)‖)
      (𝓝[{w : ℂ | w ≠ 0 ∧ (k : ℂ) + w ∈ S}] 0) (𝓝 0) := by
    simpa using hprod.norm
  refine hnorm_lim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  dsimp only [abelPlanaUpper]
  rw [cexp_neg_two_pi_I_mul_int_add, ← norm_mul, mul_sub]
  congr 1
  have hw0 : w ≠ 0 := hw.1
  have hden : cexp (-2 * π * I * w) - 1 = 0 ∨ cexp (-2 * π * I * w) - 1 ≠ 0 := em _
  rcases hden with h0 | h0
  · rw [h0]
    field_simp [hw0, hc_ne]
  · field_simp [hw0, hc_ne, h0]

/-- If `0 < ‖w‖ < 1`, `w` cannot be a nonzero integer, so `e^{-2πi(k + w)} ≠ 1`. -/
private theorem cexp_neg_two_pi_I_mul_int_add_ne_one_of_norm_lt_one (k : ℤ) {w : ℂ}
    (hw0 : 0 < ‖w‖) (hw1 : ‖w‖ < 1) : cexp (-2 * π * I * ((k : ℂ) + w)) ≠ 1 := by
  rw [cexp_neg_two_pi_I_mul_int_add]
  intro h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hwm : -w * (2 * π * I) = (m : ℂ) * (2 * π * I) := by linear_combination hm
  have hw_eq : w = ((-m : ℤ) : ℂ) := by
    have hneg := mul_right_cancel₀ hpi hwm
    push_cast
    linear_combination -hneg
  rw [hw_eq, Complex.norm_intCast] at hw0 hw1
  have hm0 : (0 : ℤ) < |(-m : ℤ)| := by exact_mod_cast hw0
  have hm1 : |(-m : ℤ)| < (1 : ℤ) := by exact_mod_cast hw1
  omega

/-- Uniform integral bound comparing `abelPlanaUpper f (k + γ t)` to its singular model along a
segment `γ : [a₀, b₀] → ℂ` of length `ε = b₀ - a₀` with `ε ≤ ‖γ t‖ ≤ 2 * ε < 1`. -/
private theorem norm_integral_abelPlanaUpper_sub_le {f : ℂ → ℂ} {S : Set ℂ} {k : ℤ}
    {a₀ b₀ ε η : ℝ} {γ : ℝ → ℂ} (hcont : ContinuousOn f S) (hγ : Continuous γ)
    (hε : 0 < ε) (hε2 : 2 * ε < 1) (hlen : b₀ - a₀ = ε) (hη : 0 ≤ η)
    (hseg : ∀ t ∈ Icc a₀ b₀, ε ≤ ‖γ t‖ ∧ ‖γ t‖ ≤ 2 * ε ∧ (k : ℂ) + γ t ∈ S)
    (hpt : ∀ w : ℂ, ε ≤ ‖w‖ → ‖w‖ ≤ 2 * ε → (k : ℂ) + w ∈ S →
      ‖w‖ * ‖abelPlanaUpper f ((k : ℂ) + w) - f k / (-2 * π * I * w)‖ ≤ η) :
    ‖(∫ t in a₀..b₀, abelPlanaUpper f ((k : ℂ) + γ t)) -
      (∫ t in a₀..b₀, f k / (-2 * π * I * γ t))‖ ≤ η := by
  have hab : a₀ ≤ b₀ := by linarith
  have hc_ne : (-2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hint1 : IntervalIntegrable (fun t : ℝ => abelPlanaUpper f ((k : ℂ) + γ t)) volume a₀ b₀ := by
    refine (ContinuousOn.div ?_ (by fun_prop) fun t ht => ?_).intervalIntegrable_of_Icc hab
    · exact hcont.comp (continuous_const.add hγ).continuousOn fun t ht => (hseg t ht).2.2
    · exact sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_int_add_ne_one_of_norm_lt_one k
        (hε.trans_le (hseg t ht).1) ((hseg t ht).2.1.trans_lt hε2))
  have hint2 : IntervalIntegrable (fun t : ℝ => f k / (-2 * π * I * γ t)) volume a₀ b₀ := by
    refine (ContinuousOn.div continuousOn_const (by fun_prop) fun t ht =>
      ?_).intervalIntegrable_of_Icc hab
    exact mul_ne_zero hc_ne (norm_pos_iff.mp (hε.trans_le (hseg t ht).1))
  rw [← intervalIntegral.integral_sub hint1 hint2]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := η / ε) fun t ht => by
    rw [uIoc_of_le hab] at ht
    have ht' : t ∈ Icc a₀ b₀ := ⟨ht.1.le, ht.2⟩
    obtain ⟨hlo, hhi, hS⟩ := hseg t ht'
    exact ((le_div_iff₀' (hε.trans_le hlo)).mpr (hpt (γ t) hlo hhi hS)).trans
      (div_le_div_of_nonneg_left hη hε hlo)
  rwa [hlen, abs_of_pos hε, div_mul_cancel₀ _ hε.ne'] at hle

/-- Quarter-box limit `upperRightCap f j ε → f j / 4` as `ε → 0⁺` for `j ∈ [a, n)`. -/
private theorem tendsto_upperRightCap {f : ℂ → ℂ} {a n j : ℤ} (hj : j ∈ Finset.Ico a n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    Tendsto (fun ε : ℝ => upperRightCap f j ε) (𝓝[>] 0) (𝓝 (f j / 4)) := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  set S : Set ℂ := {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
  have hjS : (j : ℂ) ∈ S := ⟨by simpa using hja', by simp; linarith⟩
  have hlim := tendsto_norm_mul_abelPlanaUpper_sub hjS hcont
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hball := hlim.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < δ / 3))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hball
  obtain ⟨r, hr, hball⟩ := hball
  refine eventually_nhdsWithin_iff.mpr (Metric.eventually_nhds_iff.mpr
    ⟨min (r / 3) (1 / 3), by positivity, fun ε hε_dist hε0 => ?_⟩)
  have hε_pos : 0 < ε := hε0
  have hε_lt : ε < min (r / 3) (1 / 3) := by simpa [Real.dist_eq, abs_of_pos hε_pos] using hε_dist
  have hεr : ε < r / 3 := hε_lt.trans_le (min_le_left _ _)
  have hε3 : ε < 1 / 3 := hε_lt.trans_le (min_le_right _ _)
  have hpt : ∀ w : ℂ, ε ≤ ‖w‖ → ‖w‖ ≤ 2 * ε → (j : ℂ) + w ∈ S →
      ‖w‖ * ‖abelPlanaUpper f ((j : ℂ) + w) - f j / (-2 * π * I * w)‖ ≤ δ / 3 :=
    fun w hlo hhi hwS => by
      have hw_ne : w ≠ 0 := norm_pos_iff.mp (hε_pos.trans_le hlo)
      have hm := hball (by rw [dist_zero_right]; linarith) ⟨hw_ne, hwS⟩
      exact le_of_lt (by
        simpa [Metric.mem_ball, Real.dist_eq,
          abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hm)
  have hb1 := norm_integral_abelPlanaUpper_sub_le hcont (by fun_prop) hε_pos (by linarith)
    (sub_zero ε) (by positivity) (γ := fun t : ℝ => (t : ℂ) + ε * I) (fun t ht =>
      ⟨by simpa [abs_of_pos hε_pos] using Complex.abs_im_le_norm ((t : ℂ) + ε * I),
       (norm_add_le _ _).trans (by simp [abs_of_nonneg ht.1, abs_of_pos hε_pos]; linarith [ht.2]),
       ⟨by simp; linarith [ht.1], by simp; linarith [ht.2]⟩⟩) hpt
  have hb2 := norm_integral_abelPlanaUpper_sub_le hcont (by fun_prop) hε_pos (by linarith)
    (sub_zero ε) (by positivity) (γ := fun y : ℝ => (ε : ℂ) + y * I) (fun y hy =>
      ⟨by simpa [abs_of_pos hε_pos] using Complex.abs_re_le_norm ((ε : ℂ) + y * I),
       (norm_add_le _ _).trans (by simp [abs_of_pos hε_pos, abs_of_nonneg hy.1]; linarith [hy.2]),
       ⟨by simp; linarith, by simp; linarith⟩⟩) hpt
  rw [dist_eq_norm, ← upperRightCap_model (f j) hε_pos]
  dsimp only [upperRightCap]
  have ha1 : (fun t : ℝ => abelPlanaUpper f ((j : ℂ) + t + ε * I)) =
      fun t : ℝ => abelPlanaUpper f ((j : ℂ) + ((t : ℂ) + ε * I)) := by ext t; rw [add_assoc]
  have ha2 : (fun y : ℝ => abelPlanaUpper f ((j : ℂ) + ε + y * I)) =
      fun y : ℝ => abelPlanaUpper f ((j : ℂ) + ((ε : ℂ) + y * I)) := by ext y; rw [add_assoc]
  rw [ha1, ha2, show ∀ A B C D : ℂ, (A - I * B) - (C - I * D) = (A - C) - I * (B - D) by
    intros; ring]
  calc
    ‖((∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((t : ℂ) + ε * I))) -
        ∫ t in (0 : ℝ)..ε, f j / (-2 * π * I * ((t : ℂ) + ε * I))) -
      I * ((∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((ε : ℂ) + y * I))) -
        ∫ y in (0 : ℝ)..ε, f j / (-2 * π * I * ((ε : ℂ) + y * I)))‖
      ≤ ‖(∫ t in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((t : ℂ) + ε * I))) -
          ∫ t in (0 : ℝ)..ε, f j / (-2 * π * I * ((t : ℂ) + ε * I))‖ +
        ‖I * ((∫ y in (0 : ℝ)..ε, abelPlanaUpper f ((j : ℂ) + ((ε : ℂ) + y * I))) -
          ∫ y in (0 : ℝ)..ε, f j / (-2 * π * I * ((ε : ℂ) + y * I)))‖ := norm_sub_le _ _
    _ ≤ δ / 3 + δ / 3 := by rw [norm_mul, norm_I, one_mul]; linarith
    _ < δ := by linarith

/-- Quarter-box limit `upperLeftCap f (j + 1) ε → f (j + 1) / 4` as `ε → 0⁺` for `j ∈ [a, n)`. -/
private theorem tendsto_upperLeftCap {f : ℂ → ℂ} {a n j : ℤ} (hj : j ∈ Finset.Ico a n)
    (hcont : ContinuousOn f {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}) :
    Tendsto (fun ε : ℝ => upperLeftCap f (j + 1) ε) (𝓝[>] 0) (𝓝 (f ((j + 1 : ℤ) : ℂ) / 4)) := by
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  set S : Set ℂ := {z | (a : ℝ) ≤ z.re ∧ z.re ≤ n}
  have hkS : ((j + 1 : ℤ) : ℂ) ∈ S := ⟨by push_cast; simp; linarith, by push_cast; simp; linarith⟩
  have hlim := tendsto_norm_mul_abelPlanaUpper_sub hkS hcont
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hball := hlim.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < δ / 3))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hball
  obtain ⟨r, hr, hball⟩ := hball
  refine eventually_nhdsWithin_iff.mpr (Metric.eventually_nhds_iff.mpr
    ⟨min (r / 3) (1 / 3), by positivity, fun ε hε_dist hε0 => ?_⟩)
  have hε_pos : 0 < ε := hε0
  have hε_lt : ε < min (r / 3) (1 / 3) := by simpa [Real.dist_eq, abs_of_pos hε_pos] using hε_dist
  have hεr : ε < r / 3 := hε_lt.trans_le (min_le_left _ _)
  have hε3 : ε < 1 / 3 := hε_lt.trans_le (min_le_right _ _)
  have hpt : ∀ w : ℂ, ε ≤ ‖w‖ → ‖w‖ ≤ 2 * ε → ((j + 1 : ℤ) : ℂ) + w ∈ S →
      ‖w‖ * ‖abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + w) -
        f ((j + 1 : ℤ) : ℂ) / (-2 * π * I * w)‖ ≤ δ / 3 :=
    fun w hlo hhi hwS => by
      have hw_ne : w ≠ 0 := norm_pos_iff.mp (hε_pos.trans_le hlo)
      have hm := hball (by rw [dist_zero_right]; linarith) ⟨hw_ne, hwS⟩
      exact le_of_lt (by
        simpa [Metric.mem_ball, Real.dist_eq,
          abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hm)
  have hb1 := norm_integral_abelPlanaUpper_sub_le hcont (by fun_prop) hε_pos (by linarith)
    (by ring) (by positivity) (a₀ := -ε) (b₀ := 0) (γ := fun t : ℝ => (t : ℂ) + ε * I) (fun t ht =>
      ⟨by simpa [abs_of_pos hε_pos] using Complex.abs_im_le_norm ((t : ℂ) + ε * I),
       (norm_add_le _ _).trans (by simp [abs_of_nonpos ht.2, abs_of_pos hε_pos]; linarith [ht.1]),
       ⟨by push_cast; simp; linarith [ht.1], by push_cast; simp; linarith [ht.2]⟩⟩) hpt
  have hb2 := norm_integral_abelPlanaUpper_sub_le hcont (by fun_prop) hε_pos (by linarith)
    (sub_zero ε) (by positivity) (a₀ := 0) (b₀ := ε) (γ := fun y : ℝ => -(ε : ℂ) + y * I)
    (fun y hy =>
      ⟨by simpa [abs_of_pos hε_pos] using Complex.abs_re_le_norm (-(ε : ℂ) + y * I),
       (norm_add_le _ _).trans (by simp [abs_of_pos hε_pos, abs_of_nonneg hy.1]; linarith [hy.2]),
       ⟨by push_cast; simp; linarith, by push_cast; simp; linarith⟩⟩) hpt
  rw [dist_eq_norm, ← upperLeftCap_model (f ((j + 1 : ℤ) : ℂ)) hε_pos]
  dsimp only [upperLeftCap]
  have ha1 : (fun t : ℝ => abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + t + ε * I)) =
      fun t : ℝ => abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + ((t : ℂ) + ε * I)) := by
    ext t; rw [add_assoc]
  have ha2 : (fun y : ℝ => abelPlanaUpper f (((j + 1 : ℤ) : ℂ) - ε + y * I)) =
      fun y : ℝ => abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + (-(ε : ℂ) + y * I)) := by
    ext y; ring_nf
  rw [ha1, ha2, show ∀ A B C D : ℂ, (A + I * B) - (C + I * D) = (A - C) + I * (B - D) by
    intros; ring]
  calc
    ‖((∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + ((t : ℂ) + ε * I))) -
        ∫ t in (-ε)..(0 : ℝ), f ((j + 1 : ℤ) : ℂ) / (-2 * π * I * ((t : ℂ) + ε * I))) +
      I * ((∫ y in (0 : ℝ)..ε, abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + (-(ε : ℂ) + y * I))) -
        ∫ y in (0 : ℝ)..ε, f ((j + 1 : ℤ) : ℂ) / (-2 * π * I * (-(ε : ℂ) + y * I)))‖
      ≤ ‖(∫ t in (-ε)..(0 : ℝ), abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + ((t : ℂ) + ε * I))) -
          ∫ t in (-ε)..(0 : ℝ), f ((j + 1 : ℤ) : ℂ) / (-2 * π * I * ((t : ℂ) + ε * I))‖ +
        ‖I * ((∫ y in (0 : ℝ)..ε, abelPlanaUpper f (((j + 1 : ℤ) : ℂ) + (-(ε : ℂ) + y * I))) -
          ∫ y in (0 : ℝ)..ε, f ((j + 1 : ℤ) : ℂ) / (-2 * π * I * (-(ε : ℂ) + y * I)))‖ :=
        norm_add_le _ _
    _ ≤ δ / 3 + δ / 3 := by rw [norm_mul, norm_I, one_mul]; linarith
    _ < δ := by linarith

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
  have hcont_conj := continuousOn_schwarzConjFun hcont
  obtain ⟨hja, hjn⟩ := Finset.mem_Ico.mp hj
  have hja' : (a : ℝ) ≤ j := by exact_mod_cast hja
  have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hle1 : (j : ℝ) + ε ≤ (j : ℝ) + 1 - ε := by linarith
  have hc1 : IntervalIntegrable (fun x : ℝ => abelPlanaUpper f x) volume
      ((j : ℝ) + ε) ((j : ℝ) + 1 - ε) := by
    refine (ContinuousOn.div ?_ (by fun_prop) fun x hx => ?_).intervalIntegrable_of_Icc hle1
    · exact hcont.comp (by fun_prop) fun x hx =>
        ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩
    · exact sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j
        ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩)
  have hc2 : IntervalIntegrable
      (fun x : ℝ => conj (abelPlanaUpper (schwarzConjFun f) x)) volume
      ((j : ℝ) + ε) ((j : ℝ) + 1 - ε) := by
    refine (ContinuousOn.comp Complex.continuous_conj.continuousOn
      (ContinuousOn.div ?_ (by fun_prop) fun x hx => ?_)
        (mapsTo_univ _ _)).intervalIntegrable_of_Icc hle1
    · exact hcont_conj.comp (by fun_prop) fun x hx =>
        ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩
    · exact sub_ne_zero.mpr (cexp_neg_two_pi_I_mul_ne_one_of_re_mem_Ioo j
        ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩)
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
  have hcont_conj := continuousOn_schwarzConjFun hcont
  have hden_ne : ∀ y ∈ Icc ε T, ((Real.exp (2 * π * y) : ℂ) - 1) ≠ 0 := by
    intro y hy
    have hpos : 0 < 2 * π * y := mul_pos Real.two_pi_pos (hε0.trans_le hy.1)
    have h1 : (Real.exp (2 * π * y) : ℂ) - 1 = ((Real.exp (2 * π * y) - 1 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [h1]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hpos).ne')
  have hv1 : IntervalIntegrable
      (fun y : ℝ => f (k + y * I) / (Real.exp (2 * π * y) - 1)) volume ε T :=
    ((hcont.comp (by fun_prop) fun _ _ => ⟨by simp [hka], by simp [hkn]⟩).div
      (by fun_prop) hden_ne).intervalIntegrable_of_Icc hεT
  have hv2 : IntervalIntegrable
      (fun y : ℝ => conj (schwarzConjFun f (k + y * I) / (Real.exp (2 * π * y) - 1)))
      volume ε T :=
    (Complex.continuous_conj.continuousOn.comp
      ((hcont_conj.comp (by fun_prop) fun _ _ => ⟨by simp [hka], by simp [hkn]⟩).div
        (by fun_prop) hden_ne) (mapsTo_univ _ _)).intervalIntegrable_of_Icc hεT
  rw [← intervalIntegral.intervalIntegral_conj,
    show ∀ u v : ℂ, I * u + (-I) * v = I * (u - v) by intros; ring,
    ← intervalIntegral.integral_sub hv1 hv2]
  congr 1
  refine integral_congr fun y _ => ?_
  dsimp only [schwarzConjFun]
  simp only [map_div₀, map_sub, map_one, Complex.conj_ofReal, starRingEnd_self_apply,
    map_add, map_intCast, map_mul, Complex.conj_I, mul_neg, ← sub_eq_add_neg, sub_div]

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
    have hc := (Complex.continuous_conj.tendsto 0).comp
      (tendsto_integral_abelPlanaUpper_atTop han.le (tendsto_schwarzConjFun_growth hgrowth))
    simpa [Function.comp_def] using hc
  have hlim_va : Tendsto
      (fun T : ℝ => ∫ y in ε..T, (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1))
      atTop (𝓝 (∫ y in Ioi ε, (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1))) :=
    intervalIntegral_tendsto_integral_Ioi ε (hinta.mono_set (Ioi_subset_Ioi hε0.le)) tendsto_id
  have hlim_vn : Tendsto
      (fun T : ℝ => ∫ y in ε..T, (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1))
      atTop (𝓝 (∫ y in Ioi ε, (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1))) :=
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
  swap
  · simp
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
    have hr2 : Tendsto (fun ε : ℝ => conj (upperRightCap (schwarzConjFun f) j ε))
        (𝓝[>] 0) (𝓝 (conj (schwarzConjFun f j / 4))) :=
      (Complex.continuous_conj.tendsto _).comp (tendsto_upperRightCap hj hcont_conj)
    have hl1 := tendsto_upperLeftCap hj hcont
    have hl2 : Tendsto (fun ε : ℝ => conj (upperLeftCap (schwarzConjFun f) (j + 1) ε))
        (𝓝[>] 0) (𝓝 (conj (schwarzConjFun f ((j + 1 : ℤ) : ℂ) / 4))) :=
      (Complex.continuous_conj.tendsto _).comp (tendsto_upperLeftCap hj hcont_conj)
    have hsum4 := ((hr1.add hr2).add hl1).add hl2
    have hval : f j / 4 + conj (schwarzConjFun f j / 4) + f ((j + 1 : ℤ) : ℂ) / 4 +
        conj (schwarzConjFun f ((j + 1 : ℤ) : ℂ) / 4) =
        f j / 2 + f ((j + 1 : ℤ) : ℂ) / 2 := by
      dsimp only [schwarzConjFun]
      simp only [map_div₀, map_ofNat, map_intCast, starRingEnd_self_apply]
      ring
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
  have hfinal := tendsto_nhds_unique ((hlim_seg.add hlim_caps).congr' heq_ev) hlim_rhs
  linear_combination hfinal

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
  have hΩopen : IsOpen Ω := isOpen_Ioo.preimage Complex.continuous_re
  have hΩconn : IsPreconnected Ω :=
    ((convex_Ioo a b).linear_preimage Complex.reLm).isPreconnected
  have hΩsymm : MapsTo (starRingEnd ℂ) Ω Ω := fun w hw => by simpa [Ω] using hw
  have hmid : (((a + b) / 2 : ℝ) : ℂ) ∈ Ω := by simp [Ω]; constructor <;> linarith
  have hGcont : ContinuousOn G S := hcont.sub (continuousOn_schwarzConjFun hcont)
  have hGholo : DifferentiableOn ℂ G Ω := hf.sub (differentiableOn_schwarzConjFun hf)
  have hGupper : EqOn G 0 (Ω ∩ {w : ℂ | 0 ≤ w.im}) := by
    refine eqOn_zero_of_zero_on_real_axis hΩopen hΩconn hΩsymm hmid
      (hGcont.mono (Set.inter_subset_left.trans fun _ hw => ⟨hw.1.le, hw.2.le⟩))
      (hGholo.mono Set.inter_subset_left) ?_
    intro w hw hw0
    have hw_eq : w = (w.re : ℂ) := Complex.ext rfl hw0
    rw [hw_eq]
    dsimp only [G, schwarzConjFun]
    rw [Complex.conj_ofReal]
    have him0 := hreal w.re hw.1.le hw.2.le
    have hconj : conj (f w.re) = f w.re := Complex.conj_eq_iff_im.mpr him0
    exact sub_eq_zero.mpr hconj.symm
  have hGΩ : EqOn G 0 Ω := by
    intro w hw
    rcases le_or_gt 0 w.im with hw_im | hw_im
    · exact hGupper ⟨hw, hw_im⟩
    · have hcw : conj w ∈ Ω ∩ {u : ℂ | 0 ≤ u.im} :=
        ⟨hΩsymm hw, by simp; linarith⟩
      have h0 := hGupper hcw
      dsimp only [G, schwarzConjFun, Pi.zero_apply] at h0 ⊢
      rw [starRingEnd_self_apply] at h0
      have h1 := congrArg (starRingEnd ℂ) h0
      simp only [map_sub, starRingEnd_self_apply, map_zero] at h1
      linear_combination -h1
  -- Extend `G = 0` from `Ω` to `S` by density along the segment towards the midpoint `(a + b) / 2`.
  have hG_S : G z = 0 := by
    set c : ℂ := (((a + b) / 2 : ℝ) : ℂ)
    let t : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 2)
    let u : ℕ → ℂ := fun m => ((1 - t m : ℝ) : ℂ) * z + (t m : ℂ) * c
    have hu_mem : ∀ m : ℕ, u m ∈ Ω := by
      intro m
      have ht0 : 0 < t m := by dsimp [t]; positivity
      have ht1 : t m < 1 := by
        dsimp [t]
        rw [div_lt_one (by positivity)]
        linarith
      have hre : (u m).re = (1 - t m) * z.re + t m * ((a + b) / 2) := by
        simp only [u, c, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
      exact ⟨by rw [hre]; nlinarith [hz.1], by rw [hre]; nlinarith [hz.2]⟩
    have hu_lim : Tendsto u atTop (𝓝 z) := by
      have ht : Tendsto t atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
          fun m => by dsimp only [Function.comp_apply, t]; push_cast; ring
      have h1 := (((Complex.continuous_ofReal.tendsto (1 - 0 : ℝ)).comp
        ((tendsto_const_nhds (x := (1 : ℝ))).sub ht)).mul_const z).add
        (((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp ht).mul_const c)
      simpa [u] using h1
    have hu_S : Tendsto u atTop (𝓝[S] z) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_lim
        (Eventually.of_forall fun m => ⟨(hu_mem m).1.le, (hu_mem m).2.le⟩)
    have hGu_lim : Tendsto (G ∘ u) atTop (𝓝 (G z)) := (hGcont z hz).tendsto.comp hu_S
    have hGu_zero : (G ∘ u) = fun _ => 0 := funext fun m => hGΩ (hu_mem m)
    exact tendsto_nhds_unique hGu_lim (hGu_zero ▸ tendsto_const_nhds)
  have h1 := congrArg (starRingEnd ℂ) (sub_eq_zero.mp hG_S)
  simpa [schwarzConjFun] using h1.symm

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
  swap
  · simp
  have han' : (a : ℝ) < n := by exact_mod_cast han
  have hdiff_im : ∀ (k : ℤ), (a : ℝ) ≤ k → (k : ℝ) ≤ n → ∀ y : ℝ,
      (f (k + y * I) - f (k - y * I)) / (Real.exp (2 * π * y) - 1) =
        (2 * I) * (((f (k + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
    intro k hka hkn y
    have hconj_arg : (k : ℂ) - (y : ℂ) * I = conj ((k : ℂ) + (y : ℂ) * I) := by
      simp [sub_eq_add_neg]
    have hsymm := conj_apply_eq_of_im_eq_zero_on_strip han' hf hcont hreal
      (z := (k : ℂ) + (y : ℂ) * I) ⟨by simp [hka], by simp [hkn]⟩
    rw [hconj_arg, hsymm, Complex.sub_conj]
    push_cast
    ring
  have hinta' : IntegrableOn
      (fun y : ℝ => (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) (Ioi 0) :=
    IntegrableOn.congr_fun (hinta.ofReal.const_mul (2 * I))
      (fun y _ => (hdiff_im a le_rfl han'.le y).symm) measurableSet_Ioi
  have hintn' : IntegrableOn
      (fun y : ℝ => (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) (Ioi 0) :=
    IntegrableOn.congr_fun (hintn.ofReal.const_mul (2 * I))
      (fun y _ => (hdiff_im n han'.le le_rfl y).symm) measurableSet_Ioi
  rw [sum_Icc_eq_abelPlana_sub han.le hf hcont hgrowth hinta' hintn']
  have hia :
      (∫ y in Ioi (0 : ℝ), (f (a + y * I) - f (a - y * I)) / (Real.exp (2 * π * y) - 1)) =
        (2 * I) *
          ((∫ y in Ioi (0 : ℝ), (f (a + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hdiff_im a le_rfl han'.le y),
      MeasureTheory.integral_const_mul, integral_complex_ofReal]
  have hin :
      (∫ y in Ioi (0 : ℝ), (f (n + y * I) - f (n - y * I)) / (Real.exp (2 * π * y) - 1)) =
        (2 * I) *
          ((∫ y in Ioi (0 : ℝ), (f (n + y * I)).im / (Real.exp (2 * π * y) - 1) : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hdiff_im n han'.le le_rfl y),
      MeasureTheory.integral_const_mul, integral_complex_ofReal]
  rw [hia, hin]
  have hI2 : I * (2 * I) = (-2 : ℂ) := by
    calc
      I * (2 * I) = 2 * (I * I) := by ring
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
  have hshift : Tendsto (fun y : ℝ => 1 + y) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hproj : Tendsto (fun z : ℂ => |z.im|)
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) atTop :=
    tendsto_comap.mono_left inf_le_left
  have hmaj : Tendsto (fun z : ℂ =>
      |C| * ((1 + |z.im|) ^ p * Real.exp (-(2 * π - c) * (1 + |z.im|))) * Real.exp (2 * π - c))
      (comap (fun z : ℂ => |z.im|) atTop ⊓ 𝓟 {z | a ≤ z.re ∧ z.re ≤ b}) (𝓝 0) := by
    have h1 := ((hdec.comp hshift).mul_const (Real.exp (2 * π - c))).comp hproj
    simpa [Function.comp_def] using h1
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj)
  filter_upwards [mem_inf_of_right (mem_principal_self {z : ℂ | a ≤ z.re ∧ z.re ≤ b})] with z hz
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    ‖f z‖ * Real.exp (-(2 * π * |z.im|))
      ≤ (C * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(2 * π * |z.im|)) := by
        gcongr
        exact hbound z hz.1 hz.2
    _ ≤ (|C| * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(2 * π * |z.im|)) := by
        gcongr
        exact le_abs_self C
    _ = |C| * ((1 + |z.im|) ^ p * Real.exp (-(2 * π - c) * (1 + |z.im|))) *
          Real.exp (2 * π - c) := by
        have hexp : Real.exp (c * |z.im|) * Real.exp (-(2 * π * |z.im|)) =
            Real.exp (-(2 * π - c) * (1 + |z.im|)) * Real.exp (2 * π - c) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc
          (|C| * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(2 * π * |z.im|))
            = |C| * (1 + |z.im|) ^ p * (Real.exp (c * |z.im|) * Real.exp (-(2 * π * |z.im|))) := by
              ring
          _ = |C| * ((1 + |z.im|) ^ p * Real.exp (-(2 * π - c) * (1 + |z.im|))) *
                Real.exp (2 * π - c) := by
              rw [hexp]
              ring

end TauCeti
