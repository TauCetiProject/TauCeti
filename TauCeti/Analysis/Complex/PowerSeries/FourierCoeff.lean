/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Laurent.Basic
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.FourierCoeffOn

/-!
# Cauchy coefficients as Fourier coefficients of boundary values

For a function `f : ℂ → E` and a circle `C(c, R)` with `R ≠ 0`, write
`bₘ = ∫ θ in 0..2π, (R e^{iθ}) ^ m • f (c + R e^{iθ})`. In the standard convention
`f̂(n) = (2π)⁻¹ ∫ e^{-inθ} f`, `bₘ` is `2π Rᵐ` times the `(-m)`-th Fourier coefficient of
`θ ↦ f (c + R e^{iθ})`. This file records:

* the circle integral of `(z - c) ^ (m - 1) • f z` is `I • bₘ`
  (`TauCeti.circleIntegral_sub_zpow_sub_one_smul`);
* the coefficients of the Cauchy power series `cauchyPowerSeries f c R` are
  `(2π)⁻¹ • b₋ₙ` (`TauCeti.coeff_cauchyPowerSeries`), and the Laurent coefficient of every integer
  degree `n` is `R⁻ⁿ` times the `n`-th Fourier coefficient of `θ ↦ f (c + R e^{iθ})` on `[0, 2π]`
  (`TauCeti.circleLaurentCoeff_eq_zpow_smul_fourierCoeffOn`);
* for `f` holomorphic on the open disc and continuous on its closure, the integrals `bₘ`
  with `m > 0`, that is the negative-degree Fourier coefficients, vanish by Cauchy's theorem
  (`DiffContOnCl.intervalIntegral_circleMap_zpow_smul_eq_zero`); on the unit circle, read as a
  function on `AddCircle (2 * π)`, its negative Fourier coefficients vanish
  (`DiffContOnCl.fourierCoeff_comp_toCircle_eq_zero`);
* on the unit circle, the angle integral of `w ^ m * F w` and the circle integral of `z ^ j * F z`
  are `2π` and `2π i` times Fourier coefficients of `θ ↦ F(e^{iθ})` on `[0, 2π]`
  (`TauCeti.intervalIntegral_circleMap_zpow_mul`, `TauCeti.circleIntegral_pow_mul`);
* the Fourier coefficients of the boundary defect `θ ↦ e^{ikθ} conj (T(e^{iθ})) - T(e^{iθ})` are
  `conj (a (k - n)) - a n` in terms of those `a` of `θ ↦ T(e^{iθ})`
  (`TauCeti.fourierCoeffOn_circleMap_zpow_mul_conj_sub`);
* on the unit circle, the coefficients of `cauchyPowerSeries F 0 1` are the Fourier coefficients
  of `θ ↦ F(e^{iθ})` (`TauCeti.coeff_cauchyPowerSeries_zero_one`), so the Cauchy integral
  `(2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw` is the power series `∑ zⁿ cₙ` on the open disc, with
  `cₙ` the Fourier coefficients of `θ ↦ φ(e^{iθ})`
  (`TauCeti.hasSum_pow_smul_fourierCoeffOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`);
* conversely, a function holomorphic on the open unit disc, continuous on the closed disc and
  equal on the open disc to a power series `∑ zⁿ aₙ` has `aₙ` as the `n`-th Fourier coefficient of
  its boundary values for every `n ≥ 0`, whether or not the series converges on the circle
  (`DiffContOnCl.fourierCoeffOn_circleMap_eq_of_hasSum`): both are its Taylor coefficients.
-/

public section

open Complex Metric
open scoped ComplexConjugate NNReal ENNReal Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TauCeti

/-- A circle integral against `(z - c) ^ (m - 1)`, written in the angle variable. -/
theorem circleIntegral_sub_zpow_sub_one_smul (f : ℂ → E) (c : ℂ) {R : ℝ} (hR : R ≠ 0) (m : ℤ) :
    (∮ z in C(c, R), (z - c) ^ (m - 1) • f z) =
      I • ∫ θ in 0..2 * π, circleMap 0 R θ ^ m • f (circleMap c R θ) := by
  rw [circleIntegral, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR
  simp only [deriv_circleMap, circleMap_sub_center, smul_smul, zpow_sub_one₀ hz]
  congr 1
  field_simp

/-- The Laurent coefficient of degree `n` extracted by the circle `C(c, R)` is `R⁻ⁿ` times the
`n`-th Fourier coefficient of `θ ↦ f (c + R e^{iθ})` on `[0, 2π]`. -/
theorem circleLaurentCoeff_eq_zpow_smul_fourierCoeffOn (f : ℂ → E) (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (n : ℤ) :
    circleLaurentCoeff f c R n =
      (R : ℂ) ^ (-n) • fourierCoeffOn Real.two_pi_pos (fun θ ↦ f (circleMap c R θ)) n := by
  rw [circleLaurentCoeff_def, circleIntegral_sub_zpow_sub_one_smul f c hR (-n),
    fourierCoeffOn_eq_integral, sub_zero]
  simp only [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [← Complex.coe_smul, smul_smul, fourier_coe_apply, circleMap_zero, mul_zpow,
    ← Complex.exp_intCast_mul]
  congr 1
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/-- The coefficients of the Cauchy power series of `f` on the circle `C(c, R)` are the Fourier
coefficients of `θ ↦ f (c + R e^{iθ})`, weighted by `R⁻ⁿ`. -/
theorem coeff_cauchyPowerSeries (f : ℂ → E) (c : ℂ) {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    (cauchyPowerSeries f c R).coeff n =
      (2 * π : ℂ)⁻¹ • ∫ θ in 0..2 * π, circleMap 0 R θ ^ (-(n : ℤ)) • f (circleMap c R θ) := by
  have h := (cauchyPowerSeries f c R).apply_eq_pow_smul_coeff (n := n) (z := 1)
  rw [one_pow, one_smul] at h
  have hint : (∮ z in C(c, R), (1 / (z - c)) ^ n • (z - c)⁻¹ • f z) =
      ∮ z in C(c, R), (z - c) ^ (-(n : ℤ) - 1) • f z := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hz0 : circleMap c R θ - c ≠ 0 := sub_ne_zero.mpr (circleMap_ne_center hR)
    simp only [smul_smul, zpow_sub_one₀ hz0, zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [← h, cauchyPowerSeries_apply, hint, circleIntegral_sub_zpow_sub_one_smul f c hR, smul_smul]
  congr 1
  field_simp

end TauCeti

/-- For a function holomorphic on an open disc and continuous on its closure, the integrals
`∫ θ in 0..2π, (R e^{iθ}) ^ m • f (c + R e^{iθ})` with `m > 0` vanish, by Cauchy's theorem: these
are the negative-degree Fourier coefficients of the boundary values. -/
theorem DiffContOnCl.intervalIntegral_circleMap_zpow_smul_eq_zero {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) {m : ℤ} (hm : 0 < m) :
    ∫ θ in 0..2 * π, circleMap 0 R θ ^ m • f (circleMap c R θ) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨(m - 1).toNat, by omega⟩
  have h : (∮ z in C(c, R), (z - c) ^ n • f z) = 0 :=
    (((differentiable_id.sub_const c).pow n).diffContOnCl.smul hf).circleIntegral_eq_zero hR.le
  have h' := TauCeti.circleIntegral_sub_zpow_sub_one_smul f c hR.ne' (n + 1)
  simp only [add_sub_cancel_right, zpow_natCast] at h'
  rw [h] at h'
  exact (smul_eq_zero.mp h'.symm).resolve_left I_ne_zero

local instance diffContOnClFourierCoeffTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- A function holomorphic on the open unit disc and continuous on its closure has vanishing
negative Fourier coefficients on the unit circle, read as a function on `AddCircle (2 * π)`. -/
theorem DiffContOnCl.fourierCoeff_comp_toCircle_eq_zero {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (ball 0 1)) {n : ℤ} (hn : n < 0) :
    fourierCoeff (fun x : AddCircle (2 * π) ↦ f (AddCircle.toCircle x)) n = 0 := by
  rw [fourierCoeff_eq_intervalIntegral (T := 2 * π) _ n 0, zero_add]
  have := hf.intervalIntegral_circleMap_zpow_smul_eq_zero one_pos (m := -n) (by omega)
  simp only [TauCeti.fourier_apply_eq_coe_toCircle_zpow, TauCeti.coe_toCircle_coe_eq_circleMap]
  simpa [zpow_neg] using this

namespace TauCeti

/-- The angle integral of `w ^ m * F w` over the unit circle is `2π` times the `-m`-th Fourier
coefficient of `θ ↦ F(e^{iθ})` on `[0, 2π]`. -/
theorem intervalIntegral_circleMap_zpow_mul (F : ℂ → ℂ) (m : ℤ) :
    ∫ θ in 0..2 * π, circleMap 0 1 θ ^ m * F (circleMap 0 1 θ) =
      2 * π * fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ)) (-m) := by
  rw [← fourierCoeff_comp_toCircle, fourierCoeff_eq_intervalIntegral (T := 2 * π) _ (-m) 0,
    zero_add]
  simp only [fourier_apply_eq_coe_toCircle_zpow, coe_toCircle_coe_eq_circleMap, neg_neg,
    smul_eq_mul, real_smul]
  push_cast
  field_simp

/-- The circle integral of `z ^ j * F z` over the unit circle is `2π i` times the `-(j + 1)`-th
Fourier coefficient of `θ ↦ F(e^{iθ})` on `[0, 2π]`. -/
theorem circleIntegral_pow_mul (F : ℂ → ℂ) (j : ℕ) :
    (∮ z in C(0, 1), z ^ j * F z) =
      I * (2 * π * fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ))
        (-((j : ℤ) + 1))) := by
  have h := circleIntegral_sub_zpow_sub_one_smul F 0 one_ne_zero ((j : ℤ) + 1)
  simp only [sub_zero, add_sub_cancel_right, zpow_natCast, smul_eq_mul] at h
  rw [h, intervalIntegral_circleMap_zpow_mul]

/-- The coefficients of the Cauchy power series of `F` on the unit circle are the Fourier
coefficients of `θ ↦ F(e^{iθ})` on `[0, 2π]`. -/
theorem coeff_cauchyPowerSeries_zero_one (F : ℂ → E) (n : ℕ) :
    (cauchyPowerSeries F 0 1).coeff n =
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ)) n := by
  rw [coeff_cauchyPowerSeries F 0 one_ne_zero, ← fourierCoeff_comp_toCircle,
    fourierCoeff_eq_intervalIntegral (T := 2 * π) _ n 0, zero_add]
  simp only [fourier_apply_eq_coe_toCircle_zpow, coe_toCircle_coe_eq_circleMap, one_div,
    ← ofReal_ofNat, ← ofReal_mul, ← ofReal_inv]
  exact Complex.coe_smul _ _

/-- **The Taylor series of the Cauchy integral.** For a function `φ` integrable on the unit circle,
the Cauchy integral `(2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw` is the power series `∑ zⁿ cₙ` on the
open unit disc, where `cₙ` is the `n`-th Fourier coefficient of `θ ↦ φ(e^{iθ})` on `[0, 2π]`. -/
theorem hasSum_pow_smul_fourierCoeffOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul
    {φ : ℂ → E} (hφ : CircleIntegrable φ 0 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n : ℕ ↦ z ^ n • fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
      ((2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) := by
  have h := (hasFPowerSeriesOn_cauchy_integral (R := 1) (by simpa using hφ) one_pos).hasSum
    (y := z) (by rw [Metric.eball_coe, NNReal.coe_one]; exact hz)
  simpa only [zero_add, NNReal.coe_one, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    coeff_cauchyPowerSeries_zero_one] using h

end TauCeti

/-- **The boundary Fourier coefficients of a power series.** If `H` is holomorphic on the open unit
disc, continuous on the closed disc, and equal on the open disc to a power series `∑ zⁿ aₙ`, then
for every `n ≥ 0` the `n`-th Fourier coefficient of `θ ↦ H(e^{iθ})` on `[0, 2π]` is `aₙ`. The
negative coefficients vanish (`DiffContOnCl.fourierCoeff_comp_toCircle_eq_zero`). -/
theorem DiffContOnCl.fourierCoeffOn_circleMap_eq_of_hasSum [CompleteSpace E] {H : ℂ → E}
    {a : ℕ → E}
    (hH : DiffContOnCl ℂ H (ball 0 1))
    (ha : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n ↦ z ^ n • a n) (H z)) (n : ℕ) :
    fourierCoeffOn Real.two_pi_pos (fun θ ↦ H (circleMap 0 1 θ)) n = a n := by
  let p : FormalMultilinearSeries ℂ ℂ E := fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)
  have hp (n : ℕ) (y : ℂ) : p n (fun _ ↦ y) = y ^ n • a n := by
    simp only [p, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hhalf : ((2⁻¹ : ℝ≥0) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    norm_num
  -- The series converges at `z = 1 / 2`, so its radius of convergence is at least `1 / 2`.
  have hr : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    have hn (n : ℕ) : ‖p n‖ * ((2⁻¹ : ℝ≥0) : ℝ) ^ n = ‖((2⁻¹ : ℝ≥0) : ℂ) ^ n • a n‖ := by
      rw [ContinuousMultilinearMap.norm_mkPiRing, norm_smul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, NNReal.abs_eq, mul_comm]
    have := (ha _ hhalf).summable.tendsto_atTop_zero.norm
    rw [norm_zero] at this
    exact p.le_radius_of_tendsto (l := 0) (this.congr fun n ↦ (hn n).symm)
  have h₂ : HasFPowerSeriesOnBall H p 0 ((2⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    { r_le := hr
      r_pos := by simp
      hasSum := fun {y} hy ↦ by
        have hy' : y ∈ ball (0 : ℂ) 1 := by
          rw [Metric.eball_coe] at hy
          exact ball_subset_ball (by norm_num) hy
        simpa [hp] using ha y hy' }
  have hH' : DiffContOnCl ℂ H (ball 0 ((1 : ℝ≥0) : ℝ)) := by simpa using hH
  have h₁ := hH'.hasFPowerSeriesOnBall one_pos
  have hc := congrArg (fun q ↦ q.coeff n)
    (h₁.hasFPowerSeriesAt.eq_formalMultilinearSeries h₂.hasFPowerSeriesAt)
  have hpc : p.coeff n = a n := by
    simp only [p, FormalMultilinearSeries.coeff, ContinuousMultilinearMap.mkPiRing_apply,
      Pi.one_apply, Finset.prod_const_one, one_smul]
  simp only [NNReal.coe_one, TauCeti.coeff_cauchyPowerSeries_zero_one, hpc] at hc
  exact hc

namespace TauCeti

/-- The Fourier coefficients of the boundary defect `θ ↦ e^{ikθ} conj (T(e^{iθ})) - T(e^{iθ})` of a
continuous function `T` are `conj (a (k - n)) - a n`, where `a` are the Fourier coefficients of
`θ ↦ T(e^{iθ})` on `[0, 2π]`. -/
theorem fourierCoeffOn_circleMap_zpow_mul_conj_sub {T : ℂ → ℂ} (hT : Continuous T) (k n : ℤ) :
    fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (T (circleMap 0 1 θ)) - T (circleMap 0 1 θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ)) (k - n)) -
        fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ)) n := by
  have hTc : Continuous fun x : AddCircle (2 * π) ↦ T (AddCircle.toCircle x) :=
    continuous_comp_toCircle (hT.comp (continuous_circleMap 0 1))
  have hTc' : Continuous fun x : AddCircle (2 * π) ↦
      fourier k x * conj (T (AddCircle.toCircle x)) :=
    (map_continuous (fourier k)).mul (continuous_conj.comp hTc)
  have hi {g : AddCircle (2 * π) → ℂ} (hg : Continuous g) :
      MeasureTheory.Integrable g AddCircle.haarAddCircle :=
    hg.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hfun : (fun x : AddCircle (2 * π) ↦ (AddCircle.toCircle x : ℂ) ^ k *
      conj (T (AddCircle.toCircle x)) - T (AddCircle.toCircle x)) =
      fun x ↦ fourier k x * conj (T (AddCircle.toCircle x)) - T (AddCircle.toCircle x) :=
    funext fun x ↦ by rw [fourier_apply_eq_coe_toCircle_zpow]
  rw [← fourierCoeff_comp_toCircle (fun w ↦ w ^ k * conj (T w) - T w), hfun,
    fourierCoeff_sub (hi hTc') (hi hTc), fourierCoeff_fourier_mul_conj, fourierCoeff_comp_toCircle,
    fourierCoeff_comp_toCircle]

end TauCeti
