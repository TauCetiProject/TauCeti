/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

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
* `Complex.exists_norm_Gamma_le_mul_inv_one_add_sq_pow`: `‖Γ(σ + i t)‖ ≤ C (1 + t²)⁻ᵐ` for every
  `m` on every vertical line `Re s = σ` with `σ` not a nonpositive integer.
* `Complex.norm_Gamma_add_mul_I_le_of_mem_Ioo`: explicit bound
  `‖Γ(σ + i t)‖ ≤ 120 / (-σ (σ + 1) (1 + t²)³)` for `-1 < σ < 0`.
* `Complex.exists_norm_Gamma_le_div_pow_of_re_mem_Icc`: uniform polynomial decay
  `‖Γ(s)‖ ≤ C / |Im s|ᵐ` across any closed strip `σ₀ ≤ Re s ≤ σ₁` for `|Im s| ≥ 1`.
* `Complex.verticalIntegrable_Gamma`: `Γ` is integrable on every vertical line `Re s = σ` with
  `σ` not a nonpositive integer.
* `Complex.verticalIntegrable_Gamma_smul_of_norm_le`: `w ↦ Γ(w) • g(w)` is integrable on
  `Re w = σ` (`σ ≠ -n`) whenever `g` is measurable and polynomially bounded on that line.
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

/-- Explicit polynomial vertical decay of `Γ` in the strip `-1 < σ < 0`: for every `t : ℝ`,
`‖Γ(σ + i t)‖ ≤ 120 / (-σ (σ + 1) (1 + t²)³)`. -/
theorem norm_Gamma_add_mul_I_le_of_mem_Ioo {σ : ℝ} (hσ₀ : -1 < σ) (hσ₁ : σ < 0) (t : ℝ) :
    ‖Gamma (σ + t * I)‖ ≤ 120 / (-σ * (σ + 1) * (1 + t ^ 2) ^ 3) := by
  set s : ℂ := σ + t * I
  have hre : s.re = σ := by simp [s]
  have hbound := norm_Gamma_mul_prod_norm_le (s := s) (n := 6)
    (by rw [hre]; push_cast; linarith)
  rw [hre] at hbound
  have hΓ6 : Real.Gamma (σ + (6 : ℕ)) ≤ 120 := by
    have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn
      (show (2 : ℝ) ≤ σ + (6 : ℕ) by push_cast; linarith) (by norm_num : (2 : ℝ) ≤ 6)
      (by push_cast; linarith)
    have hval : Real.Gamma 6 = 120 := by
      norm_num [show (6 : ℝ) = (5 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial, Nat.factorial]
    exact hmono.trans_eq hval
  have hsq (k : ℕ) : ‖s + k‖ ^ 2 = (σ + k) ^ 2 + t ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]; simp [s]; ring
  have h0 : (-σ) ^ 2 * (1 + t ^ 2) ≤ ‖s + (0 : ℕ)‖ ^ 2 := by
    have hσ_sq : (-σ) ^ 2 ≤ 1 := by nlinarith
    rw [hsq 0]; push_cast
    nlinarith [mul_le_of_le_one_left (sq_nonneg t) hσ_sq]
  have h1 : (σ + 1) ^ 2 * (1 + t ^ 2) ≤ ‖s + (1 : ℕ)‖ ^ 2 := by
    have hσ_sq : (σ + 1) ^ 2 ≤ 1 := by nlinarith
    rw [hsq 1]; push_cast
    nlinarith [mul_le_of_le_one_left (sq_nonneg t) hσ_sq]
  have hk {k : ℕ} (hk2 : 2 ≤ k) : 1 + t ^ 2 ≤ ‖s + k‖ ^ 2 := by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    rw [hsq k]; nlinarith
  have hprod_sq : (-σ * (σ + 1) * (1 + t ^ 2) ^ 3) ^ 2 ≤
      (∏ k ∈ Finset.range 6, ‖s + k‖) ^ 2 := by
    rw [← Finset.prod_pow]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    calc (-σ * (σ + 1) * (1 + t ^ 2) ^ 3) ^ 2
        = ((-σ) ^ 2 * (1 + t ^ 2)) * ((σ + 1) ^ 2 * (1 + t ^ 2)) *
            (1 + t ^ 2) * (1 + t ^ 2) * (1 + t ^ 2) * (1 + t ^ 2) := by ring
      _ ≤ _ := by
        gcongr
        · exact hk (by norm_num)
        · exact hk (by norm_num)
        · exact hk (by norm_num)
        · exact hk (by norm_num)
  have hpos : 0 < -σ * (σ + 1) * (1 + t ^ 2) ^ 3 :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have hprod : -σ * (σ + 1) * (1 + t ^ 2) ^ 3 ≤ ∏ k ∈ Finset.range 6, ‖s + k‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun k _ ↦ norm_nonneg _) hprod_sq
  rw [le_div_iff₀ hpos]
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans (hbound.trans hΓ6)

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

/-- The Gamma function is integrable on every vertical line `Re s = σ` which avoids its poles,
that is, for `σ` not a nonpositive integer. -/
theorem verticalIntegrable_Gamma {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    VerticalIntegrable Gamma σ := by
  obtain ⟨C, hC⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hσ 1
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_
    (Eventually.of_forall fun t ↦ by simpa using hC t)
  refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun t ↦ ?_)
  refine (differentiableAt_Gamma _ fun m h ↦ hσ m ?_).continuousAt.comp (by fun_prop)
  simpa using congrArg re h

/-- Because `Γ(σ + i t)` decays faster than every power of `|t|`, multiplying any measurable,
polynomially bounded function `g` on `Re w = σ` (`σ` not a nonpositive integer) by `Γ` produces a
vertically integrable function. -/
theorem verticalIntegrable_Gamma_smul_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} {σ C : ℝ} {m : ℕ} (hσ : ∀ n : ℕ, σ ≠ -n)
    (hmeas : AEStronglyMeasurable fun t : ℝ ↦ g (σ + t * I))
    (hg : ∀ t : ℝ, ‖g (σ + t * I)‖ ≤ C * (1 + t ^ 2) ^ m) :
    VerticalIntegrable (fun w ↦ Gamma w • g w) σ := by
  obtain ⟨A, hA⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hσ (m + 1)
  have hA0 : 0 ≤ A := by simpa using (norm_nonneg (Gamma σ)).trans (by simpa using hA 0)
  have hΓ_cont : Continuous fun t : ℝ ↦ Gamma (σ + t * I) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (differentiableAt_Gamma _ fun n h ↦ hσ n (by simpa using congrArg re h)).continuousAt.comp
        (by fun_prop)
  refine (integrable_inv_one_add_sq.const_mul (A * C)).mono'
    (hΓ_cont.aestronglyMeasurable.smul hmeas) (Eventually.of_forall fun t ↦ ?_)
  calc ‖Gamma (σ + t * I) • g (σ + t * I)‖
      = ‖Gamma (σ + t * I)‖ * ‖g (σ + t * I)‖ := norm_smul _ _
    _ ≤ (A * ((1 + t ^ 2) ^ (m + 1))⁻¹) * (C * (1 + t ^ 2) ^ m) :=
        mul_le_mul (hA t) (hg t) (norm_nonneg _) (mul_nonneg hA0 (by positivity))
    _ = A * C * (1 + t ^ 2)⁻¹ := by rw [pow_succ]; field_simp

/-- Mellin inversion for the Gamma function: on every vertical line `Re s = σ > 0`,
`(1 / 2π) ∫ x^{-(σ + i t)} Γ(σ + i t) dt = e⁻ˣ` for `x > 0`. -/
theorem mellinInv_Gamma {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ Gamma x = Real.exp (-x) := by
  have hline : ∀ t : ℝ, Gamma (σ + t * I) = mellin (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) (σ + t * I) :=
    fun t ↦ by rw [← GammaIntegral_eq_mellin, Gamma_eq_integral (by simpa using hσ)]
  have hint : VerticalIntegrable (mellin fun u : ℝ ↦ (Real.exp (-u) : ℂ)) σ := by
    refine (verticalIntegrable_Gamma fun n h ↦ ?_).congr (Eventually.of_forall hline)
    linarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have hconv : MellinConvergent (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) σ := by
    refine (GammaIntegral_convergent (s := σ) (by simpa using hσ)).congr_fun (fun u _ ↦ ?_)
      measurableSet_Ioi
    simp [smul_eq_mul, mul_comm]
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
