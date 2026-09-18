/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.Analysis.Asymptotics.SumWindow
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Approximation

/-!
# The Wiener--Ikehara theorem

Let `a n ≥ 0` have Dirichlet series `F s = ∑ a n n⁻ˢ` convergent on `Re s > 1`, and suppose that
`F s - κ / (s - 1)` agrees on `Re s > 1` with a function `G` continuous on `Re s ≥ 1`. The
Wiener--Ikehara theorem says that the partial sums then grow like `κ x`:
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`.

The analytic input is the smoothed asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_schwartz_atTop`, which evaluates the limit of
`∑ a n / n * 𝓕 g (log (n / x) / 2π)` for a Schwartz function `g`. This file makes two passes.

* **Smooth cutoffs.** For a smooth function `Ψ` with compact support inside `(0, ∞)`, the weight
  `W v = e^{2πv} Ψ(e^{2πv})` is smooth and compactly supported, hence the Fourier transform of the
  Schwartz function `g = 𝓕⁻ W`, and `a n / n * W (log (n / x) / 2π) = x⁻¹ a n Ψ (n / x)`. Since
  `g 0 = ∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`, this gives `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ`.
* **The sharp cutoff.** The indicator of `(0, 1]` is squeezed between two bump functions. The lower
  bump is supported in `(0, 1)`; the upper bump equals `1` on `[ε, 1]`, and the coefficients with
  `n ≤ ε x` that it misses are controlled by the Chebyshev bound
  `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`. Letting `ε → 0` gives the theorem.

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

The passage from Schwartz test functions to smooth cutoffs on `(0, ∞)` and then to the sharp
cutoff follows `WienerIkeharaSmooth`, `WienerIkeharaInterval` and `WienerIkeharaTheorem'` in
`PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files in this directory. Here the smooth step is derived from the Schwartz-function asymptotic
by Fourier inversion on `𝓢(ℝ, ℂ)`, and the sharp step squeezes directly between two
`ContDiffBump`s, spending the Chebyshev bound only on the initial segment `n ≤ ε x`.

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
  have hn' : (0 : ℝ) < n := by positivity
  have hexp : Real.exp (2 * π * (1 / (2 * π) * Real.log (n / x))) = n / x := by
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul, Real.exp_log (by positivity)]
  rw [_root_.LSeries.term_of_ne_zero hn, expWeight, hexp, cpow_one, Complex.real_smul]
  push_cast
  field_simp

/-- The substitution `y = e^{2πv}`: `∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`. -/
private lemma integral_expWeight :
    ∫ v, expWeight Ψ v = (2 * π : ℂ)⁻¹ * ∫ y in Ioi 0, Ψ y := by
  have h := Measure.integral_comp_mul_left (fun u ↦ Real.exp u • Ψ (Real.exp u)) (2 * π)
  rw [show (fun v ↦ expWeight Ψ v) = fun v ↦ Real.exp (2 * π * v) • Ψ (Real.exp (2 * π * v))
    from rfl, h, integral_comp_exp, abs_of_pos (by positivity), Complex.real_smul]
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
  rw [hFg, hg0, show 2 * (π : ℂ) * A * ((2 * π : ℂ)⁻¹ * ∫ y in Ioi 0, Ψ y) =
    A * ∫ y in Ioi 0, Ψ y by field_simp] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp_rw [term_mul_expWeight a hΨ0 hx, tsum_mul_left]

end Smooth

/-! ### Bump functions on the positive half-line -/

section Bump

variable {c : ℝ} (φ : ContDiffBump c)

private lemma tsupport_bump_subset (h : φ.rOut < c) : tsupport φ ⊆ Ioi 0 := by
  rw [φ.tsupport_eq, Real.closedBall_eq_Icc]
  intro y hy
  exact lt_of_lt_of_le (by linarith) hy.1

private lemma integral_Ioi_bump (h : φ.rOut < c) : ∫ y in Ioi 0, φ y = ∫ y, φ y :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦
    image_eq_zero_of_notMem_tsupport fun h' ↦ hy (tsupport_bump_subset φ h h')

/-- A bump in `(0, ∞)` has integral at most the length `2 rOut` of its support. -/
private lemma integral_Ioi_bump_le (h : φ.rOut < c) : ∫ y in Ioi 0, φ y ≤ 2 * φ.rOut := by
  simpa [integral_Ioi_bump φ h, φ.rOut_pos.le] using φ.integral_le_measure_closedBall (μ := volume)

/-- A bump in `(0, ∞)` has integral at least the length `2 rIn` of the ball where it is `1`. -/
private lemma le_integral_Ioi_bump (h : φ.rOut < c) : 2 * φ.rIn ≤ ∫ y in Ioi 0, φ y := by
  simpa [integral_Ioi_bump φ h, φ.rIn_pos.le] using φ.measure_closedBall_le_integral (μ := volume)

end Bump

/-! ### The sharp cutoff -/

section Sharp

variable {a : ℕ → ℝ} {F G : ℂ → ℂ} {κ : ℝ}

/-- The smoothed asymptotic for real coefficients and a real bump in `(0, ∞)`. -/
private lemma tendsto_inv_mul_tsum_mul_bump (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1))
    {c : ℝ} (φ : ContDiffBump c) (h : φ.rOut < c) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑' n : ℕ, a n * φ (n / x)) atTop
      (𝓝 (κ * ∫ y in Ioi 0, φ y)) := by
  have hmain := tendsto_inv_mul_tsum_mul_div_atTop (a := fun n ↦ (a n : ℂ)) (A := κ)
    (Ψ := fun y ↦ (φ y : ℂ)) (fun n ↦ by simpa using ha n) hG
    (fun z hz ↦ by rw [hGF z hz, (hF z hz).LSeries_eq])
    (fun σ hσ ↦ (hF σ (by simpa using hσ)).LSeriesSummable)
    (ofRealCLM.contDiff.comp φ.contDiff) (φ.hasCompactSupport.comp_left ofReal_zero)
    (by
      rw [tsupport, show (Function.support fun y ↦ (φ y : ℂ)) = Function.support φ from
        Function.support_comp_eq ofReal (by simp) φ]
      exact tsupport_bump_subset φ h)
  rw [integral_complex_ofReal, ← ofReal_mul] at hmain
  refine (continuous_re.tendsto _).comp hmain |>.congr fun x ↦ ?_
  simp only [Function.comp_apply, ← ofReal_inv, ← ofReal_mul, ← ofReal_tsum, ofReal_re]

/-- The lower bump lies below the sharp cutoff. -/
private lemma tsum_mul_bump_le_sum (ha : 0 ≤ a) {c : ℝ} (φ : ContDiffBump c) (h : φ.rOut < c)
    (h1 : c + φ.rOut ≤ 1) {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, a n * φ (n / x) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
  have hzero : ∀ y : ℝ, y ∉ Ioo 0 1 → φ y = 0 := fun y hy ↦ by
    by_contra h0
    have hy' : y ∈ Metric.ball c φ.rOut := φ.support_eq ▸ Function.mem_support.2 h0
    rw [Real.ball_eq_Ioo] at hy'
    exact hy ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) fun n hn ↦ ?_]
  · exact Finset.sum_le_sum fun n _ ↦ mul_le_of_le_one_right (ha n) φ.le_one
  refine mul_eq_zero_of_right _ (hzero _ fun hn' ↦ hn (Finset.mem_Icc.2 ⟨?_, ?_⟩))
  · by_contra h0
    simp_all
  · exact Nat.le_floor ((div_lt_one hx).1 hn'.2).le

/-- The upper bump, together with the initial segment `n ≤ ε x`, lies above the sharp cutoff. -/
private lemma sum_Ioc_le_tsum_mul_bump (ha : 0 ≤ a) {c ε : ℝ} (φ : ContDiffBump c)
    (hε : c - φ.rIn ≤ ε) (h1 : 1 ≤ c + φ.rIn) (h2 : c + φ.rOut ≤ 2) {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.Ioc ⌊ε * x⌋₊ ⌊x⌋₊, a n ≤ ∑' n : ℕ, a n * φ (n / x) := by
  have hsum : Summable fun n : ℕ ↦ a n * φ (n / x) := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌊2 * x⌋₊ + 1)) fun n hn ↦ ?_
    refine mul_eq_zero_of_right _ (φ.zero_of_le_dist ?_)
    have hn' : 2 * x < n := by
      simpa using Nat.lt_of_floor_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (not_lt.1 (Finset.mem_range.not.1 hn)))
    rw [Real.dist_eq, le_abs]
    left
    have : 2 < (n : ℝ) / x := by rwa [lt_div_iff₀ hx]
    linarith
  refine le_trans (Finset.sum_le_sum fun n hn ↦ ?_)
    (hsum.sum_le_tsum _ fun n _ ↦ mul_nonneg (ha n) φ.nonneg)
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.1 hn
  have hlo' : ε * x < n := Nat.lt_of_floor_lt hlo
  have hhi' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hhi
  rw [φ.one_of_mem_closedBall, mul_one]
  rw [Real.closedBall_eq_Icc]
  constructor
  · rw [le_div_iff₀ hx]
    nlinarith
  · rw [div_le_iff₀ hx]
    nlinarith

/-- **The squeeze at width `ε`.** Under a Chebyshev bound `∑_{1 ≤ n ≤ N} a n ≤ C N`, for every
`0 < ε ≤ 1 / 8` the normalized partial sums are eventually within `(C + 4 |κ| + 1) ε` of `κ`. -/
private lemma eventually_abs_inv_mul_sum_sub_le (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ C * N) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∀ᶠ x in atTop, |x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - κ| ≤ (C + 4 * |κ| + 1) * ε := by
  -- The upper bump is `1` on `[ε, 1]` and supported in `(ε / 2, 1 + ε / 2)`; the lower bump is
  -- supported in `(ε, 1 - ε)` and is `1` on `[2ε, 1 - 2ε]`.
  let φp : ContDiffBump ((1 + ε) / 2) := ⟨(1 - ε) / 2, 1 / 2, by linarith, by linarith⟩
  let φm : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 - 2 * ε, 1 / 2 - ε, by linarith, by linarith⟩
  have hp := tendsto_inv_mul_tsum_mul_bump ha hF hG hGF φp (by simp [φp]; linarith)
  have hm := tendsto_inv_mul_tsum_mul_bump ha hF hG hGF φm (by simp [φm]; linarith)
  -- Their integrals are within `ε` and `4ε` of `1`.
  have hIp := integral_Ioi_bump_le φp (by simp [φp]; linarith)
  have hIp' := le_integral_Ioi_bump φp (by simp [φp]; linarith)
  have hIm := integral_Ioi_bump_le φm (by simp [φm]; linarith)
  have hIm' := le_integral_Ioi_bump φm (by simp [φm]; linarith)
  simp only [φp, φm] at hIp hIp' hIm hIm'
  have hκp : |κ * (∫ y in Ioi 0, φp y) - κ| ≤ |κ| * ε := by
    rw [← mul_sub_one, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg κ)
  have hκm : |κ * (∫ y in Ioi 0, φm y) - κ| ≤ |κ| * (4 * ε) := by
    rw [← mul_sub_one, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg κ)
  filter_upwards [eventually_gt_atTop 0, Metric.tendsto_nhds.1 hp ε hε,
    Metric.tendsto_nhds.1 hm ε hε] with x hx0 hUx hLx
  rw [Real.dist_eq] at hUx hLx
  -- The lower squeeze.
  have hlow : x⁻¹ * ∑' n : ℕ, a n * φm (n / x) ≤ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n :=
    mul_le_mul_of_nonneg_left (tsum_mul_bump_le_sum ha φm (by simp [φm]; linarith)
      (by simp [φm]; linarith) hx0) (inv_nonneg.2 hx0.le)
  -- The upper squeeze: split off the initial segment `n ≤ ε x`, where the Chebyshev bound applies.
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n =
      ∑ n ∈ Finset.Icc 1 ⌊ε * x⌋₊, a n + ∑ n ∈ Finset.Ioc ⌊ε * x⌋₊ ⌊x⌋₊, a n := by
    have hI (m : ℕ) : Finset.Icc 1 m = Finset.Ioc 0 m := by
      simpa using Finset.Icc_add_one_left_eq_Ioc 0 m
    rw [hI, hI]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono (by nlinarith))).symm
  have hinit : ∑ n ∈ Finset.Icc 1 ⌊ε * x⌋₊, a n ≤ C * (ε * x) :=
    (hC _).trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hC0)
  have hup : x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n ≤ C * ε + x⁻¹ * ∑' n : ℕ, a n * φp (n / x) := by
    have := sum_Ioc_le_tsum_mul_bump ha φp (ε := ε) (by simp [φp]; linarith)
      (by simp [φp]; linarith) (by simp [φp]; linarith) hx0
    rw [hsplit, mul_add]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_left this (inv_nonneg.2 hx0.le))
    rw [inv_mul_le_iff₀ hx0]
    linarith
  rw [abs_lt] at hUx hLx
  rw [abs_le] at hκp hκm ⊢
  constructor <;> nlinarith [abs_nonneg κ]

/-- **The Wiener--Ikehara theorem.** Let `a n ≥ 0` have Dirichlet series with sum `F s` on
`Re s > 1`, and let `G` be continuous on `Re s ≥ 1` with `G s = F s - κ / (s - 1)` on `Re s > 1`.
Then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`. -/
theorem wienerIkehara (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s - κ / (s - 1)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 κ) := by
  -- The Chebyshev bound `∑_{1 ≤ n ≤ N} a n ≤ C N`.
  obtain ⟨C₀, hC₀⟩ := exists_sum_Icc_le_mul_of_isBigO
    (isBigO_sum_Icc_norm_id_of_boundary (a := fun n ↦ (a n : ℂ)) (A := κ)
      (fun n ↦ by simpa using ha n) hG (fun z hz ↦ by rw [hGF z hz, (hF z hz).LSeries_eq])
      (fun σ hσ ↦ (hF σ (by simpa using hσ)).LSeriesSummable))
  set C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ≤ C * N := fun N ↦ by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_)) ((hC₀ N).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) N.cast_nonneg))
    simp [abs_of_nonneg (ha n)]
  -- Squeeze at a width `ε` small enough that the error `(C + 4 |κ| + 1) ε` is below `δ`.
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set K := C + 4 * |κ| + 2
  have hK : 0 < K := by positivity
  set ε := min (1 / 8) (δ / K)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεK : ε * K ≤ δ := by
    have := min_le_right (1 / 8) (δ / K)
    rwa [le_div_iff₀ hK] at this
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    (eventually_abs_inv_mul_sum_sub_le ha hF hG hGF hC0 hC hε (min_le_left _ _))
  refine ⟨x₀, fun x hx ↦ (hx₀ x hx).trans_lt ?_⟩
  nlinarith

/-- **The Wiener--Ikehara theorem with zero residue.** If the Dirichlet series `F` of `a n ≥ 0`
extends continuously from `Re s > 1` to `Re s ≥ 1`, then `x⁻¹ ∑_{1 ≤ n ≤ x} a n → 0`. -/
theorem wienerIkehara_zero (ha : 0 ≤ a)
    (hF : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s))
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re}) (hGF : ∀ s : ℂ, 1 < s.re → G s = F s) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) :=
  wienerIkehara ha hF hG fun s hs ↦ by simp [hGF s hs]

end Sharp

end TauCeti.LSeries
