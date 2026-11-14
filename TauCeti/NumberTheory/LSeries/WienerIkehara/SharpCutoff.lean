/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.WienerIkehara
public import TauCeti.Analysis.Asymptotics.Sum.Window
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Approximation

/-!
# The Wiener--Ikehara theorem

Let `a n ≥ 0` have Dirichlet series `F s = ∑ a n n⁻ˢ` convergent on `Re s > 1`, and suppose that
`F s - κ / (s - 1)` agrees on `Re s > 1` with a function `G` continuous on `Re s ≥ 1`. The
Wiener--Ikehara theorem says that the partial sums then grow like `κ x`:
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`.

The analytic input is the smoothed asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_schwartz_atTop`, which evaluates the limit of
`∑ a n / n * 𝓕 g (log (n / x) / 2π)` for a Schwartz function `g`. This file treats two cutoffs.

* **Smooth cutoffs.** For a smooth function `Ψ` with compact support inside `(0, ∞)`, the weight
  `W v = e^{2πv} Ψ(e^{2πv})` is smooth and compactly supported, hence the Fourier transform of the
  Schwartz function `g = 𝓕⁻ W`, and `a n / n * W (log (n / x) / 2π) = x⁻¹ a n Ψ (n / x)`. Since
  `g 0 = ∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`, this gives `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ`.
* **The sharp cutoff.** Mathlib's `WienerIkehara.tendsto_sum_div` proves the theorem under the
  additional hypothesis that the partial sums are `O(N)`. Here that hypothesis is not assumed but
  derived: the Chebyshev bound `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary` follows from
  the boundary behaviour of `F` alone.

The coefficients are real and nonnegative, the hypothesis on the series is `LSeriesHasSum` on the
open half-plane (Mathlib's `LSeries` is a total function, zero where the series diverges), and the
continuous extension is a separately named function `G`, so no junk value of `F` at `s = 1` or on
the line `Re s = 1` is ever used. The sign of `κ` is not assumed: it is forced by the conclusion.

## Main results

* `TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop`: the smoothed asymptotic
  `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ` for a smooth `Ψ` with compact support in `(0, ∞)`.
* `TauCeti.LSeries.wienerIkehara`: **the Wiener--Ikehara theorem**,
  `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ`.
* `TauCeti.LSeries.wienerIkehara_zero`: the case `κ = 0`, in which `F` itself extends continuously
  to `Re s ≥ 1` and the partial sums are `o(x)`.

## Provenance

The passage from Schwartz test functions to smooth cutoffs on `(0, ∞)` follows
`WienerIkeharaSmooth` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`,
the same source as the sibling files in this directory. Here the smooth step is derived from the
Schwartz-function asymptotic by Fourier inversion on `𝓢(ℝ, ℂ)`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff SchwartzMap Topology

namespace TauCeti.LSeries

/-! ### Smooth cutoffs on the positive half-line -/

section Smooth

variable {Ψ : ℝ → ℂ}

/-- The weight `v ↦ e^{2πv} Ψ(e^{2πv})`, which turns the logarithmic frequency `log (n / x) / 2π`
of the smoothed asymptotic back into the ratio `n / x`. -/
private noncomputable def expWeight (Ψ : ℝ → ℂ) (v : ℝ) : ℂ :=
  Real.exp (2 * π * v) • Ψ (Real.exp (2 * π * v))

private lemma contDiff_expWeight (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (expWeight Ψ) := by
  have he : ContDiff ℝ ∞ fun v : ℝ ↦ Real.exp (2 * π * v) := by fun_prop
  exact he.smul (hΨ.comp he)

/-- A compact support inside `(0, ∞)` becomes a compact support after the substitution
`y = e^{2πv}`: it is the image of `tsupport Ψ` under `y ↦ log y / 2π`. -/
private lemma hasCompactSupport_expWeight (hΨc : HasCompactSupport Ψ)
    (hΨpos : tsupport Ψ ⊆ Ioi 0) : HasCompactSupport (expWeight Ψ) := by
  refine HasCompactSupport.intro (K := (fun y ↦ Real.log y / (2 * π)) '' tsupport Ψ)
    (hΨc.isCompact.image_of_continuousOn fun y hy ↦
      ((Real.continuousAt_log (hΨpos hy).ne').div_const _).continuousWithinAt) fun v hv ↦ ?_
  by_contra h
  refine hv ⟨Real.exp (2 * π * v), subset_tsupport _ fun h0 ↦ h ?_, ?_⟩
  · simp [expWeight, h0]
  · simp only [Real.log_exp]
    field_simp

private lemma term_mul_expWeight (a : ℕ → ℂ) (hΨ0 : Ψ 0 = 0) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    _root_.LSeries.term a 1 n * expWeight Ψ (1 / (2 * π) * Real.log (n / x)) =
      (x : ℂ)⁻¹ * (a n * Ψ (n / x)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hΨ0]
  have hexp : Real.exp (2 * π * (1 / (2 * π) * Real.log (n / x))) = n / x := by
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul, Real.exp_log (by positivity)]
  rw [_root_.LSeries.term_of_ne_zero hn, expWeight, hexp, cpow_one, Complex.real_smul]
  push_cast
  field_simp

/-- The substitution `y = e^{2πv}`: `∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`. -/
private lemma integral_expWeight :
    ∫ v, expWeight Ψ v = (2 * π : ℂ)⁻¹ * ∫ y in Ioi 0, Ψ y := by
  have h := Measure.integral_comp_mul_left (fun u ↦ Real.exp u • Ψ (Real.exp u)) (2 * π)
  simp only [expWeight]
  rw [h, integral_comp_exp, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  rfl

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}

/-- **The smoothed Wiener--Ikehara asymptotic for a cutoff on `(0, ∞)`.** Let `a` be
nonnegative, with Dirichlet series summable on `Re s > 1` and a boundary remainder
`G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`. For every smooth `Ψ` whose support is a
compact subset of `(0, ∞)`, `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ` as `x → ∞`. -/
theorem tendsto_inv_mul_tsum_mul_div_atTop (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ) (hΨpos : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun x : ℝ ↦ (x : ℂ)⁻¹ * ∑' n : ℕ, a n * Ψ (n / x)) atTop
      (𝓝 (A * ∫ y in Ioi 0, Ψ y)) := by
  set W : 𝓢(ℝ, ℂ) := (hasCompactSupport_expWeight hΨc hΨpos).toSchwartzMap
    (contDiff_expWeight hΨ)
  have hFg : 𝓕 ((𝓕⁻ W : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = expWeight Ψ := by
    rw [← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
    rfl
  have hg0 : (𝓕⁻ W : 𝓢(ℝ, ℂ)) 0 = (2 * π : ℂ)⁻¹ * ∫ y in Ioi 0, Ψ y := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, ← integral_expWeight]
    simp [W]
  have hΨ0 : Ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl (0 : ℝ) (hΨpos h)
  have key := tendsto_tsum_term_mul_fourier_schwartz_atTop ha hG hG' hsum (𝓕⁻ W)
  have hscale : 2 * (π : ℂ) * A * ((2 * π : ℂ)⁻¹ * ∫ y in Ioi 0, Ψ y) =
      A * ∫ y in Ioi 0, Ψ y := by
    field_simp
  rw [hFg, hg0, hscale] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp_rw [term_mul_expWeight a hΨ0 hx, tsum_mul_left]

end Smooth

/-! ### The sharp cutoff -/

section Sharp

variable {a : ℕ → ℝ} {F G : ℂ → ℂ} {κ : ℝ}

/-- **The Wiener--Ikehara theorem.** Let `a n ≥ 0` have Dirichlet series with sum `F s` on
`Re s > 1`, and let `G` be continuous on `Re s ≥ 1` with `G s = F s - κ / (s - 1)` on `Re s > 1`.
Then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`. -/
theorem wienerIkehara (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 κ) := by
  -- The Chebyshev bound `∑_{1 ≤ n ≤ N} a n ≤ C N` feeds the bounded form of the theorem in
  -- Mathlib, which sums from `n = 0`; the term `a 0` goes into the constant.
  have hG' (s : ℂ) (hs : 1 < s.re) : G s = LSeries (fun n ↦ (a n : ℂ)) s - κ / (s - 1) := by
    rw [hGF s hs, (hF s hs).LSeries_eq]
  obtain ⟨C, hC⟩ := exists_sum_Icc_le_mul_of_isBigO
    (isBigO_sum_Icc_norm_id_of_boundary (fun n ↦ by simpa using ha n) hG hG'
      (fun σ hσ ↦ (hF σ (by simpa using hσ)).LSeriesSummable))
  have hbound (N : ℕ) : ∑ i ∈ Finset.range N, a i ≤ (a 0 + max C 0) * N := by
    rcases N with _ | N
    · simp
    have hsum : ∑ n ∈ Finset.Icc 1 N, a n ≤ C * N := by
      simpa [abs_of_nonneg (ha _)] using hC N
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot N.succ_pos, zero_add,
      Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
    push_cast
    nlinarith [mul_nonneg (ha 0) N.cast_nonneg, le_max_right C 0,
      mul_le_mul_of_nonneg_right (le_max_left C 0) (N.cast_nonneg (α := ℝ))]
  have hmain := WienerIkehara.tendsto_sum_div hbound hG (fun s hs ↦ hG' s hs) ha
  have h0 : Tendsto (fun x : ℝ ↦ a 0 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  rw [← sub_zero κ]
  refine (hmain.sub h0).congr fun x ↦ ?_
  rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _), ← Finset.Icc_add_one_left_eq_Ioc,
    zero_add, add_div, add_sub_cancel_right, div_eq_inv_mul]

/-- **The Wiener--Ikehara theorem with zero residue.** If the Dirichlet series `F` of `a n ≥ 0`
extends continuously from `Re s > 1` to `Re s ≥ 1`, then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → 0`. -/
theorem wienerIkehara_zero (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re}) (hGF : ∀ s : ℂ, 1 < s.re → G s = F s) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) :=
  wienerIkehara ha hF hG fun s hs ↦ by simp [hGF s hs]

end Sharp

end TauCeti.LSeries
