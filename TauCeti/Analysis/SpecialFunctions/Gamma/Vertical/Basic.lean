/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import TauCeti.Analysis.MellinTransform

/-!
# The complex Gamma function on vertical lines

On a vertical line `Re s = σ` the complex Gamma function decays faster than every power of
`|Im s|`. This file records the elementary form of that decay which suffices for contour
arguments with integrands of polynomial growth, and the Mellin inversion formula for `Γ`.

For `Re s > 0` the Euler integral gives `‖Γ(s)‖ ≤ Γ(Re s)`. Applying this to `s + n` and using
`Γ(s + n) = s (s + 1) ⋯ (s + n - 1) Γ(s)` gives, for every `s` with `Re s + n > 0`,

`‖Γ(s)‖ ‖s‖ ‖s + 1‖ ⋯ ‖s + n - 1‖ ≤ Γ(Re s + n)`,

which also holds at the poles of `Γ` in that half-plane, where a factor `s + k` vanishes. Since
`‖s + k‖ ≥ |Im s|`, this gives `Γ(σ + i t) = O(|t|⁻ⁿ)` for every `n` without any Stirling
asymptotics; on a vertical line avoiding the poles it gives the explicit bounds
`‖Γ(σ + i t)‖ ≤ C (1 + t²)⁻ᵐ` for every `m`, so `Γ` is integrable on every such line.

Since `Γ` is the Mellin transform of `t ↦ e⁻ᵗ`, Mellin inversion recovers the exponential from
`Γ` on any vertical line `Re s = σ > 0`:

`e⁻ˣ = (1 / 2π) ∫ Γ(σ + i t) x^{-(σ + i t)} dt` for `x > 0`.

This is the smoothing kernel that turns a Dirichlet series into an exponentially weighted sum of
its coefficients.

## Main results

* `Complex.norm_Gamma_le_Gamma_re`: `‖Γ(s)‖ ≤ Γ(Re s)` for `Re s > 0`.
* `Complex.norm_Gamma_mul_prod_norm_le`: `‖Γ(s)‖ ∏_{k < n} ‖s + k‖ ≤ Γ(Re s + n)` whenever
  `Re s + n > 0`.
* `Complex.norm_Gamma_mul_pow_mul_factorial_le`: `‖Γ(s)‖ (1 - a)^N N! ≤ Γ(a)` on the line
  `Re s = a - N` with `0 < a < 1`, so `Γ` decays factorially to the left; and
  `Complex.norm_Gamma_mul_pow_mul_factorial_mul_le`:
  `‖Γ(s)‖ (1 - a)^N N! a (1 + (Im s)²) ≤ Γ(a + 2)` on the same line.
* `Complex.exists_norm_Gamma_le_mul_inv_one_add_sq_pow`: `‖Γ(σ + i t)‖ ≤ C (1 + t²)⁻ᵐ` for every
  `m` on every vertical line `Re s = σ` with `σ` not a nonpositive integer.
* `Complex.norm_Gamma_le_of_re_mem_Ioo`: explicit bound
  `‖Γ(s)‖ ≤ (2 m + 1)! / (-Re s (Re s + 1) (1 + (Im s)²)^{m + 1})` for `-1 < Re s < 0`.
* `Complex.exists_norm_Gamma_le_div_pow_of_re_mem_Icc`: uniform polynomial decay
  `‖Γ(s)‖ ≤ C / |Im s|ᵐ` across any closed strip `σ₀ ≤ Re s ≤ σ₁` for `|Im s| ≥ 1`.
* `Complex.exists_norm_Gamma_mul_Gamma_add_le_div_pow_of_re_mem_Icc`: the same decay for
  `Γ(s) Γ(s + p)` with real `p`.
* `Complex.norm_Gamma_mul_Gamma_add_le_of_re_eq_sub_natCast`: factorial decay of
  `Γ(s) Γ(s + p)` to the left, times `(1 + (Im s)²)⁻¹`, on the line `Re s = δ - N` with
  `0 < δ`, `0 < p` and `δ + p < 1`.
* `Complex.continuousAt_Gamma_of_re_ne_neg_nat`, `Complex.continuous_Gamma_add_mul_I`,
  `Complex.continuous_Gamma_sub_mul_I`: continuity of `Γ` away from `-ℕ` and along pole-free
  vertical lines `y ↦ w ± i y`.
* `Complex.verticalIntegrable_Gamma`: `Γ` is integrable on every vertical line `Re s = σ` with
  `σ` not a nonpositive integer.
* `Complex.verticalIntegrable_Gamma_smul_of_norm_le`: `w ↦ Γ(w) • g(w)` is integrable on
  `Re w = σ` (`σ ≠ -n`) whenever `g` is measurable and almost everywhere polynomially bounded on
  that line.
* `Complex.VerticalIntegrable.mul_Gamma_comp`: multiplying a function integrable on `Re s = σ` by
  `Γ(w(s))`, where `w` maps that line continuously into a vertical line avoiding the poles of `Γ`,
  keeps it integrable.
* `Complex.verticalIntegrable_Gamma_mul_Gamma_add`: `Γ(s) Γ(s + a)` is integrable on every
  vertical line `Re s = σ` with neither `σ` nor `σ + Re a` a nonpositive integer.
* `Complex.mellinInv_Gamma`: Mellin inversion of `Γ` on `Re s = σ > 0` gives `e⁻ˣ`.
* `Complex.integral_cpow_neg_mul_Gamma`: the same formula as the unnormalised vertical integral
  `∫ y^{-(σ + i t)} Γ(σ + i t) dt = 2π e⁻ʸ`.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §4.42 (the Euler integral) and §9.5 (Mellin
  inversion).
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055
  (the smoothing kernel `Γ(s) xˢ` in the proof of Siegel's theorem).
-/

public section

open Real Set MeasureTheory Filter
open scoped Nat
open Complex hiding exp continuous_exp

namespace Complex

/-- On the right half-plane the complex Gamma function is bounded by the real Gamma function of
the real part: `‖Γ(s)‖ ≤ Γ(Re s)`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, Real.Gamma_eq_integral hs, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq (setIntegral_congr_fun measurableSet_Ioi
    fun x (hx : 0 < x) ↦ ?_)
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

/-- The polynomial decay of the Gamma function on vertical lines:
`‖Γ(s)‖ ‖s‖ ‖s + 1‖ ⋯ ‖s + n - 1‖ ≤ Γ(Re s + n)` whenever `Re s + n > 0`. This holds also at the
poles of `Γ` in the half-plane `Re s > -n`, where one of the factors `s + k` vanishes. -/
theorem norm_Gamma_mul_prod_norm_le {s : ℂ} {n : ℕ} (hs : 0 < s.re + n) :
    ‖Gamma s‖ * ∏ k ∈ Finset.range n, ‖s + k‖ ≤ Real.Gamma (s.re + n) := by
  induction n generalizing s with
  | zero => simpa using norm_Gamma_le_Gamma_re (by simpa using hs)
  | succ n ih =>
    rcases eq_or_ne s 0 with rfl | hs0
    · simp only [Finset.prod_range_succ', zero_add, Nat.cast_zero, norm_zero, mul_zero]
      exact (Real.Gamma_pos_of_pos (by simpa using hs)).le
    have h := ih (s := s + 1) (by push_cast at hs ⊢; simp only [add_re, one_re]; linarith)
    have hΓ : ‖Gamma (s + 1)‖ = ‖s‖ * ‖Gamma s‖ := by rw [Gamma_add_one s hs0, norm_mul]
    have hprod : ∏ k ∈ Finset.range n, ‖s + ((k + 1 : ℕ) : ℂ)‖ =
        ∏ k ∈ Finset.range n, ‖s + 1 + k‖ :=
      Finset.prod_congr rfl fun k _ ↦ by push_cast; ring_nf
    rw [Finset.prod_range_succ', hprod,
      show s.re + ((n + 1 : ℕ) : ℝ) = (s + 1).re + n by simp; ring]
    calc _ = ‖Gamma (s + 1)‖ * ∏ k ∈ Finset.range n, ‖s + 1 + k‖ := by rw [hΓ]; simp; ring
      _ ≤ _ := h

/-- On the line `Re w = a - N` with `0 ≤ a < 1`, `(1 - a)^N N! ≤ ∏_{k < N} ‖w + k‖`. -/
private lemma pow_mul_factorial_le_prod_norm_add {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (N : ℕ)
    {w : ℂ} (hw : w.re = a - N) :
    (1 - a) ^ N * (N ! : ℝ) ≤ ∏ k ∈ Finset.range N, ‖w + k‖ := by
  induction N generalizing w with
  | zero => simp
  | succ N ih =>
    have h1 := ih (w := w + 1) (by rw [add_re, hw, one_re]; push_cast; ring)
    have h0 : (1 - a) * (N + 1) ≤ ‖w‖ := by
      have : (1 - a) * (N + 1) ≤ -w.re := by
        rw [hw]; push_cast; nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      exact this.trans ((neg_le_abs _).trans (abs_re_le_norm w))
    calc (1 - a) ^ (N + 1) * ((N + 1) ! : ℝ) = ((1 - a) ^ N * N !) * ((1 - a) * (N + 1)) := by
          rw [pow_succ, Nat.factorial_succ]; push_cast; ring
      _ ≤ (∏ k ∈ Finset.range N, ‖w + 1 + k‖) * ‖w‖ :=
          mul_le_mul h1 h0 (mul_nonneg (by linarith) (by positivity))
            (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
      _ = ∏ k ∈ Finset.range (N + 1), ‖w + k‖ := by
          rw [Finset.prod_range_succ']
          congr 1
          · exact Finset.prod_congr rfl fun k _ ↦ by push_cast; ring_nf
          · simp

/-- Factorial decay of `Γ` to the left: on the vertical line `Re s = a - N` with `0 < a < 1`,
`‖Γ(s)‖ (1 - a)^N N! ≤ Γ(a)`. -/
theorem norm_Gamma_mul_pow_mul_factorial_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ)
    {s : ℂ} (hs : s.re = a - N) :
    ‖Gamma s‖ * ((1 - a) ^ N * (N ! : ℝ)) ≤ Real.Gamma a := by
  have h := norm_Gamma_mul_prod_norm_le (s := s) (n := N) (by rw [hs]; linarith)
  rw [hs, sub_add_cancel] at h
  exact (mul_le_mul_of_nonneg_left (pow_mul_factorial_le_prod_norm_add ha0.le ha1 N hs)
    (norm_nonneg _)).trans h

/-- Factorial decay of `Γ` to the left, together with decay along the line: on the vertical line
`Re s = a - N` with `0 < a < 1`, `‖Γ(s)‖ (1 - a)^N N! a (1 + (Im s)²) ≤ Γ(a + 2)`. -/
theorem norm_Gamma_mul_pow_mul_factorial_mul_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (N : ℕ) {s : ℂ} (hs : s.re = a - N) :
    ‖Gamma s‖ * ((1 - a) ^ N * (N ! : ℝ) * (a * (1 + s.im ^ 2))) ≤ Real.Gamma (a + 2) := by
  have h := norm_Gamma_mul_prod_norm_le (s := s) (n := N + 2) (by rw [hs]; push_cast; linarith)
  rw [hs, show a - N + ((N + 2 : ℕ) : ℝ) = a + 2 by push_cast; ring, Finset.prod_range_succ,
    Finset.prod_range_succ] at h
  have hsq (k : ℕ) : ‖s + k‖ ^ 2 = (a - N + k) ^ 2 + s.im ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply, ← hs]
    simp only [add_re, add_im, natCast_re, natCast_im, add_zero]
    ring
  -- the last two factors give the decay `a (1 + (Im s)²)`
  have hlast : a * (1 + s.im ^ 2) ≤ ‖s + N‖ * ‖s + ((N + 1 : ℕ) : ℂ)‖ := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    have e1 : ‖s + N‖ ^ 2 = a ^ 2 + s.im ^ 2 := by rw [hsq]; ring
    have e2 : ‖s + ((N + 1 : ℕ) : ℂ)‖ ^ 2 = (a + 1) ^ 2 + s.im ^ 2 := by
      rw [hsq]; push_cast; ring
    have hm := sq_nonneg s.im
    have i1 : a ^ 2 * (1 + s.im ^ 2) ≤ a ^ 2 + s.im ^ 2 := by
      nlinarith [mul_nonneg hm (by nlinarith : (0 : ℝ) ≤ 1 - a ^ 2)]
    have i2 : 1 + s.im ^ 2 ≤ (a + 1) ^ 2 + s.im ^ 2 := by nlinarith
    calc (a * (1 + s.im ^ 2)) ^ 2 = a ^ 2 * (1 + s.im ^ 2) * (1 + s.im ^ 2) := by ring
      _ ≤ (a ^ 2 + s.im ^ 2) * ((a + 1) ^ 2 + s.im ^ 2) :=
          mul_le_mul i1 i2 (by positivity) (by positivity)
      _ = (‖s + N‖ * ‖s + ((N + 1 : ℕ) : ℂ)‖) ^ 2 := by rw [mul_pow, e1, e2]
  calc ‖Gamma s‖ * ((1 - a) ^ N * (N ! : ℝ) * (a * (1 + s.im ^ 2)))
      ≤ ‖Gamma s‖ * ((∏ k ∈ Finset.range N, ‖s + k‖) * (‖s + N‖ * ‖s + ((N + 1 : ℕ) : ℂ)‖)) := by
        gcongr
        exact pow_mul_factorial_le_prod_norm_add ha0.le ha1 N hs
    _ ≤ Real.Gamma (a + 2) := (le_of_eq (by ring)).trans h

/-- On a vertical line `Re s = σ` avoiding the poles of the Gamma function, `Γ(σ + i t)` decays
faster than every power of `|t|`: for every `m`, `‖Γ(σ + i t)‖` is bounded by a constant multiple
of `(1 + t²)⁻ᵐ`. -/
theorem exists_norm_Gamma_le_mul_inv_one_add_sq_pow {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Gamma (σ + t * I)‖ ≤ C * ((1 + t ^ 2) ^ m)⁻¹ := by
  obtain ⟨n, hn2, hn⟩ : ∃ n : ℕ, 2 * m ≤ n ∧ 0 < σ + n :=
    ⟨⌈-σ⌉₊ + 2 * m + 1, by omega, by push_cast; linarith [Nat.le_ceil (-σ)]⟩
  set c : ℝ := ∏ k ∈ Finset.range n, min ((σ + k) ^ 2) 1
  have hc : 0 < c := Finset.prod_pos fun k _ ↦ lt_min (by
    have : σ + k ≠ 0 := fun h ↦ hσ k (by linarith)
    positivity) one_pos
  refine ⟨Real.Gamma (σ + n) / √c, fun t ↦ ?_⟩
  set s : ℂ := σ + t * I
  have hre : s.re = σ := by simp [s]
  have hT : 0 < 1 + t ^ 2 := by positivity
  -- each factor satisfies `‖s + k‖² ≥ min ((σ + k)², 1) (1 + t²)`
  have hfac (k : ℕ) : min ((σ + k) ^ 2) 1 * (1 + t ^ 2) ≤ ‖s + k‖ ^ 2 := by
    have : ‖s + k‖ ^ 2 = (σ + k) ^ 2 + t ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp [s]; ring
    rw [this]
    nlinarith [min_le_left ((σ + k) ^ 2) 1, min_le_right ((σ + k) ^ 2) 1, sq_nonneg t,
      le_min (sq_nonneg (σ + k)) zero_le_one]
  have hprod : c * ((1 + t ^ 2) ^ m) ^ 2 ≤ (∏ k ∈ Finset.range n, ‖s + k‖) ^ 2 := by
    calc c * ((1 + t ^ 2) ^ m) ^ 2 ≤ c * (1 + t ^ 2) ^ n := by
          rw [← pow_mul, mul_comm m]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by nlinarith) hn2) hc.le
      _ = ∏ k ∈ Finset.range n, min ((σ + k) ^ 2) 1 * (1 + t ^ 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ ≤ ∏ k ∈ Finset.range n, ‖s + k‖ ^ 2 :=
          Finset.prod_le_prod₀ (fun k _ ↦ mul_nonneg (le_min (sq_nonneg _) zero_le_one) hT.le)
            fun k _ ↦ hfac k
      _ = _ := Finset.prod_pow _ _ _
  have hbound := norm_Gamma_mul_prod_norm_le (s := s) (n := n) (by rw [hre]; exact hn)
  rw [hre] at hbound
  have hsq : (√c * (1 + t ^ 2) ^ m) ^ 2 ≤ (∏ k ∈ Finset.range n, ‖s + k‖) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hc.le]
  have hP : √c * (1 + t ^ 2) ^ m ≤ ∏ k ∈ Finset.range n, ‖s + k‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun k _ ↦ norm_nonneg _) hsq
  rw [show Real.Gamma (σ + n) / √c * ((1 + t ^ 2) ^ m)⁻¹ =
      Real.Gamma (σ + n) / (√c * (1 + t ^ 2) ^ m) by field_simp, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left hP (norm_nonneg _)).trans hbound

/-- Explicit polynomial vertical decay of `Γ` in the strip `-1 < Re s < 0`: for every `m : ℕ`,
`‖Γ(s)‖ ≤ (2 m + 1)! / (-Re s (Re s + 1) (1 + (Im s)²)^{m + 1})`. -/
theorem norm_Gamma_le_of_re_mem_Ioo {s : ℂ} (hs : s.re ∈ Ioo (-1) 0) (m : ℕ) :
    ‖Gamma s‖ ≤ ((2 * m + 1).factorial : ℝ) / (-s.re * (s.re + 1) * (1 + s.im ^ 2) ^ (m + 1)) := by
  have hbound := norm_Gamma_mul_prod_norm_le (s := s) (n := 2 * m + 2)
    (by push_cast; linarith [hs.1])
  have hΓ_le : Real.Gamma (s.re + (2 * m + 2 : ℕ)) ≤ (2 * m + 1).factorial := by
    have hconv := Real.convexOn_Gamma.le_max_of_mem_Icc (x := (1 : ℝ))
      (y := ((2 * m + 1 : ℕ) : ℝ) + 1) (z := s.re + (2 * m + 2 : ℕ))
      (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr (by positivity))
      ⟨by push_cast; linarith [hs.1], by push_cast; linarith [hs.2]⟩
    rw [Real.Gamma_one, Real.Gamma_nat_eq_factorial] at hconv
    exact hconv.trans (max_le (Nat.one_le_cast.mpr (Nat.factorial_pos _)) le_rfl)
  have hsq (k : ℕ) : ‖s + k‖ ^ 2 = (s.re + k) ^ 2 + s.im ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]; simp; ring
  have h0 : (-s.re) ^ 2 * (1 + s.im ^ 2) ≤ ‖s + (0 : ℕ)‖ ^ 2 := by
    have hre_sq : (-s.re) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    rw [hsq 0]; push_cast
    nlinarith [mul_le_of_le_one_left (sq_nonneg s.im) hre_sq]
  have h1 : (s.re + 1) ^ 2 * (1 + s.im ^ 2) ≤ ‖s + (1 : ℕ)‖ ^ 2 := by
    have hre_sq : (s.re + 1) ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    rw [hsq 1]; push_cast
    nlinarith [mul_le_of_le_one_left (sq_nonneg s.im) hre_sq]
  have htail : (1 + s.im ^ 2) ^ (2 * m) ≤
      ∏ k ∈ Finset.range (2 * m), ‖s + ((k + 2 : ℕ) : ℂ)‖ ^ 2 := by
    calc (1 + s.im ^ 2) ^ (2 * m)
        = ∏ _k ∈ Finset.range (2 * m), (1 + s.im ^ 2) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ k ∈ Finset.range (2 * m), ‖s + ((k + 2 : ℕ) : ℂ)‖ ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun k _ ↦ by
            rw [hsq (k + 2)]; push_cast; nlinarith [hs.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hprod_sq : (-s.re * (s.re + 1) * (1 + s.im ^ 2) ^ (m + 1)) ^ 2 ≤
      (∏ k ∈ Finset.range (2 * m + 2), ‖s + k‖) ^ 2 := by
    rw [← Finset.prod_pow, Finset.prod_range_succ', Finset.prod_range_succ']
    calc (-s.re * (s.re + 1) * (1 + s.im ^ 2) ^ (m + 1)) ^ 2
        = (1 + s.im ^ 2) ^ (2 * m) * ((s.re + 1) ^ 2 * (1 + s.im ^ 2)) *
            ((-s.re) ^ 2 * (1 + s.im ^ 2)) := by
          rw [pow_succ _ m, mul_pow (-s.re * (s.re + 1)), mul_pow ((1 + s.im ^ 2) ^ m),
            ← pow_mul, mul_comm m 2]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul htail h1 (by positivity) (by positivity)) h0
          (by positivity) (by positivity)
  have hpos : 0 < -s.re * (s.re + 1) * (1 + s.im ^ 2) ^ (m + 1) :=
    mul_pos (mul_pos (by linarith [hs.2]) (by linarith [hs.1])) (by positivity)
  have hprod : -s.re * (s.re + 1) * (1 + s.im ^ 2) ^ (m + 1) ≤
      ∏ k ∈ Finset.range (2 * m + 2), ‖s + k‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hprod_sq
  rw [le_div_iff₀ hpos]
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans (hbound.trans hΓ_le)

/-- Uniform polynomial decay of `Γ` on horizontal segments across a closed vertical strip: for
every `σ₀, σ₁ : ℝ` and `m : ℕ`, there is `C ≥ 0` such that `‖Γ(s)‖ ≤ C / |Im s|ᵐ` whenever
`Re s ∈ [σ₀, σ₁]` and `1 ≤ |Im s|`. -/
theorem exists_norm_Gamma_le_div_pow_of_re_mem_Icc (σ₀ σ₁ : ℝ) (m : ℕ) :
    ∃ C ≥ 0, ∀ s : ℂ, s.re ∈ Icc σ₀ σ₁ → 1 ≤ |s.im| → ‖Gamma s‖ ≤ C / |s.im| ^ m := by
  set n : ℕ := ⌈-σ₀⌉₊ + m + 1
  have hn0 : 0 < σ₀ + n := by
    dsimp [n]; push_cast; linarith [Nat.le_ceil (-σ₀)]
  have hcont : ContinuousOn Real.Gamma (Icc (σ₀ + n) (σ₁ + n)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono fun x hx ↦ hn0.trans_le hx.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun s hs him ↦ ?_⟩
  have hpos : 0 < |s.im| ^ m := pow_pos (by linarith) m
  rw [le_div_iff₀ hpos]
  have hs_n : 0 < s.re + n := hn0.trans_le (by linarith [hs.1])
  have hbound := norm_Gamma_mul_prod_norm_le (s := s) (n := n) hs_n
  have hΓ_le : Real.Gamma (s.re + n) ≤ max C 0 := by
    have hmem : s.re + n ∈ Icc (σ₀ + n) (σ₁ + n) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC _ hmem).trans (le_max_left _ _))
  have him_pow : |s.im| ^ m ≤ ∏ k ∈ Finset.range n, ‖s + k‖ := by
    calc |s.im| ^ m ≤ |s.im| ^ n := pow_le_pow_right₀ him (by dsimp [n]; omega)
      _ = ∏ _k ∈ Finset.range n, |s.im| := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ k ∈ Finset.range n, ‖s + k‖ :=
          Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun k _ ↦ by
            simpa using abs_im_le_norm (s + k)
  exact (mul_le_mul_of_nonneg_left him_pow (norm_nonneg _)).trans (hbound.trans hΓ_le)

/-- Uniform polynomial decay of `Γ(s) Γ(s + p)` on horizontal segments across a closed vertical
strip, for real `p`: for every `σ₀, σ₁ : ℝ` and `m : ℕ`, there is `C ≥ 0` such that
`‖Γ(s) Γ(s + p)‖ ≤ C / |Im s|ᵐ` whenever `Re s ∈ [σ₀, σ₁]` and `1 ≤ |Im s|`. -/
theorem exists_norm_Gamma_mul_Gamma_add_le_div_pow_of_re_mem_Icc (p σ₀ σ₁ : ℝ) (m : ℕ) :
    ∃ C ≥ 0, ∀ s : ℂ, s.re ∈ Icc σ₀ σ₁ → 1 ≤ |s.im| →
      ‖Gamma s * Gamma (s + p)‖ ≤ C / |s.im| ^ m := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_Gamma_le_div_pow_of_re_mem_Icc σ₀ σ₁ m
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_Gamma_le_div_pow_of_re_mem_Icc (σ₀ + p) (σ₁ + p) 0
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun s hs him ↦ ?_⟩
  have h2 := hC₂ (s + p) (by simp only [add_re, ofReal_re]; exact ⟨by linarith [hs.1],
    by linarith [hs.2]⟩) (by simpa using him)
  rw [pow_zero, div_one] at h2
  calc ‖Gamma s * Gamma (s + p)‖ = ‖Gamma s‖ * ‖Gamma (s + p)‖ := norm_mul _ _
    _ ≤ C₁ / |s.im| ^ m * C₂ := mul_le_mul (hC₁ s hs him) h2 (norm_nonneg _)
        (div_nonneg hC₁0 (by positivity))
    _ = C₁ * C₂ / |s.im| ^ m := by ring

/-- On the line `Re s = δ - N`, with `0 < δ`, `0 < p` and `δ + p < 1`, the product
`Γ(s) Γ(s + p)` is bounded by `(1 + (Im s)²)⁻¹` times a constant multiple of `1 / (κ^N N!²)`,
where `κ = (1 - δ)(1 - δ - p)`. -/
theorem norm_Gamma_mul_Gamma_add_le_of_re_eq_sub_natCast {p δ : ℝ} (hδ : 0 < δ) (hp : 0 < p)
    (hδp : δ + p < 1) (N : ℕ) {s : ℂ} (hs : s.re = δ - N) :
    ‖Gamma s * Gamma (s + p)‖ ≤
      Real.Gamma (δ + 2) * Real.Gamma (δ + p) /
        (δ * ((1 - δ) * (1 - (δ + p))) ^ N * (N ! : ℝ) ^ 2) * (1 + s.im ^ 2)⁻¹ := by
  have h1 := norm_Gamma_mul_pow_mul_factorial_mul_le hδ (by linarith) N hs
  have h2 := norm_Gamma_mul_pow_mul_factorial_le (a := δ + p) (by linarith) hδp N
    (s := s + p) (by rw [add_re, ofReal_re, hs]; ring)
  have hD1 : 0 < (1 - δ) ^ N * (N ! : ℝ) * (δ * (1 + s.im ^ 2)) := by
    have : 0 < 1 - δ := by linarith
    positivity
  have hD2 : 0 < (1 - (δ + p)) ^ N * (N ! : ℝ) := by
    have : 0 < 1 - (δ + p) := by linarith
    positivity
  rw [norm_mul]
  calc ‖Gamma s‖ * ‖Gamma (s + p)‖
      ≤ Real.Gamma (δ + 2) / ((1 - δ) ^ N * (N ! : ℝ) * (δ * (1 + s.im ^ 2))) *
          (Real.Gamma (δ + p) / ((1 - (δ + p)) ^ N * (N ! : ℝ))) :=
        mul_le_mul ((le_div_iff₀ hD1).mpr h1) ((le_div_iff₀ hD2).mpr h2) (norm_nonneg _)
          (div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le hD1.le)
    _ = _ := by
        have : 0 < 1 - δ := by linarith
        have : 0 < 1 - (δ + p) := by linarith
        rw [mul_pow]
        field_simp

/-- `Complex.Gamma` is continuous at every `s` whose real part is not a nonpositive integer. -/
theorem continuousAt_Gamma_of_re_ne_neg_nat {s : ℂ} (hs : ∀ n : ℕ, s.re ≠ -n) :
    ContinuousAt Gamma s :=
  continuousAt_Gamma s fun m hm ↦ hs m (by simpa using congrArg re hm)

/-- Along any vertical line `y ↦ w + i y` avoiding the nonpositive-integer poles (`Re w ∉ -ℕ`),
`y ↦ Γ(w + i y)` is continuous on `ℝ`. -/
theorem continuous_Gamma_add_mul_I {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    Continuous fun y : ℝ ↦ Gamma (w + y * I) :=
  continuous_iff_continuousAt.mpr fun y ↦
    (continuousAt_Gamma_of_re_ne_neg_nat (by simpa using hw)).comp (by fun_prop)

/-- Along any vertical line `y ↦ w - i y` avoiding the nonpositive-integer poles (`Re w ∉ -ℕ`),
`y ↦ Γ(w - i y)` is continuous on `ℝ`. -/
theorem continuous_Gamma_sub_mul_I {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    Continuous fun y : ℝ ↦ Gamma (w - y * I) :=
  continuous_iff_continuousAt.mpr fun y ↦
    (continuousAt_Gamma_of_re_ne_neg_nat (by simpa [sub_eq_add_neg] using hw)).comp (by fun_prop)

/-- The Gamma function is integrable on every vertical line `Re s = σ` which avoids its poles,
that is, for `σ` not a nonpositive integer. -/
theorem verticalIntegrable_Gamma {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    VerticalIntegrable Gamma σ := by
  obtain ⟨C, hC⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hσ 1
  exact (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_Gamma_add_mul_I (by simpa using hσ)).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ by simpa using hC t)

/-- Because `Γ(σ + i t)` decays faster than every power of `|t|`, multiplying any measurable
function `g` that is almost everywhere polynomially bounded on `Re w = σ` (`σ` not a nonpositive
integer) by `Γ` produces a vertically integrable function. -/
theorem verticalIntegrable_Gamma_smul_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} {σ C : ℝ} {m : ℕ} (hσ : ∀ n : ℕ, σ ≠ -n)
    (hmeas : AEStronglyMeasurable fun t : ℝ ↦ g (σ + t * I))
    (hg : ∀ᵐ t : ℝ, ‖g (σ + t * I)‖ ≤ C * (1 + t ^ 2) ^ m) :
    VerticalIntegrable (fun w ↦ Gamma w • g w) σ := by
  obtain ⟨A, hA⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hσ (m + 1)
  have hA0 : 0 ≤ A := by simpa using (norm_nonneg (Gamma σ)).trans (by simpa using hA 0)
  refine (integrable_inv_one_add_sq.const_mul (A * C)).mono'
    ((continuous_Gamma_add_mul_I (by simpa using hσ)).aestronglyMeasurable.smul hmeas)
    (hg.mono fun t hgt ↦ ?_)
  calc ‖Gamma (σ + t * I) • g (σ + t * I)‖
      = ‖Gamma (σ + t * I)‖ * ‖g (σ + t * I)‖ := norm_smul _ _
    _ ≤ (A * ((1 + t ^ 2) ^ (m + 1))⁻¹) * (C * (1 + t ^ 2) ^ m) :=
        mul_le_mul (hA t) hgt (norm_nonneg _) (mul_nonneg hA0 (by positivity))
    _ = A * C * (1 + t ^ 2)⁻¹ := by rw [pow_succ]; field_simp

/-- If `f` is integrable on the vertical line `Re s = σ` and `w` maps that line continuously into
the vertical line `Re s = τ`, with `τ` not a nonpositive integer, then `s ↦ f s Γ(w s)` is
integrable on `Re s = σ`, since `Γ` is continuous and bounded on `Re s = τ`. -/
theorem VerticalIntegrable.mul_Gamma_comp {f w : ℂ → ℂ} {σ τ : ℝ} (hf : VerticalIntegrable f σ)
    (hτ : ∀ n : ℕ, τ ≠ -n) (hw : Continuous w) (hwτ : ∀ y : ℝ, (w (σ + y * I)).re = τ) :
    VerticalIntegrable (fun s ↦ f s * Gamma (w s)) σ := by
  have hline (y : ℝ) : w (σ + y * I) = ↑τ + ↑(w (σ + y * I)).im * I := by
    apply Complex.ext <;> simp [hwτ]
  obtain ⟨C, hC⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hτ 0
  refine hf.mul_bdd (c := C) ?_
    (Eventually.of_forall fun y ↦ by simpa [← hline] using hC (w (σ + y * I)).im)
  refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y ↦ ?_)
  exact (continuousAt_Gamma_of_re_ne_neg_nat (by simpa [hwτ] using hτ)).comp (by fun_prop)

/-- On every vertical line `Re t = σ` with neither `σ` nor `σ + Re a` a nonpositive integer, the
product `Γ(t) Γ(t + a)` is integrable. -/
theorem verticalIntegrable_Gamma_mul_Gamma_add {a : ℂ} {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n)
    (haσ : ∀ n : ℕ, σ + a.re ≠ -n) :
    VerticalIntegrable (fun t ↦ Gamma t * Gamma (t + a)) σ :=
  (verticalIntegrable_Gamma hσ).mul_Gamma_comp haσ (by fun_prop) fun y ↦ by simp

/-- Mellin inversion for the Gamma function: on every vertical line `Re s = σ > 0`,
`(1 / 2π) ∫ x^{-(σ + i t)} Γ(σ + i t) dt = e⁻ˣ` for `x > 0`. -/
theorem mellinInv_Gamma {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ Gamma x = Real.exp (-x) := by
  have hM (t : ℝ) := TauCeti.hasMellin_exp_neg (z := σ + t * I) (by simpa using hσ)
  have hline (t : ℝ) : Gamma (σ + t * I) = mellin (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) (σ + t * I) :=
    (hM t).2.symm
  have hint : VerticalIntegrable (mellin fun u : ℝ ↦ (Real.exp (-u) : ℂ)) σ := by
    refine (verticalIntegrable_Gamma fun n h ↦ ?_).congr (Eventually.of_forall hline)
    linarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have hconv : MellinConvergent (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) σ := by simpa using (hM 0).1
  have h := mellinInv_mellin_eq σ _ hx hconv hint (by fun_prop)
  rw [← h, mellinInv, mellinInv]
  simp_rw [hline]

/-- Mellin inversion for the Gamma function as an integral: on every vertical line
`Re s = σ > 0`, `∫ y^{-(σ + i t)} Γ(σ + i t) dt = 2π e⁻ʸ` for `y > 0`. -/
theorem integral_cpow_neg_mul_Gamma {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * Gamma (σ + t * I) = 2 * π * Real.exp (-y) := by
  have h := mellinInv_Gamma hσ hy
  rw [mellinInv, real_smul] at h
  simp only [smul_eq_mul] at h
  rw [← h, ← mul_assoc,
    show (2 * π : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]

end Complex
