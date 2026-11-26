/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.Laurent.Periodic
import TauCeti.Analysis.Complex.Periodic
import TauCeti.Analysis.Fourier.FourierCoeffOn

/-!
# Twisted Fourier analysis of quasi-periodic entire functions

Via the exponential coordinate `w = exp (2πiz)` (`Function.Periodic.qParam 1`) and Laurent
expansion on `ℂ \ {0}` (`DifferentiableOn.hasLaurentSeriesOnAnnulus`), every entire function
`s : ℂ → ℂ` satisfying `s (z + 1) = exp (2πiα) * s z` expands into a twisted Fourier series with
coefficients `thetaFourierCoeff α s m = fourierCoeffOn zero_lt_one (fun t => exp (-2πiαt) * s t) m`.

## Main definitions

* `TauCeti.thetaFourierCoeff`: the `m`-th twisted Fourier coefficient on `[0, 1]`.

## Main results

* `TauCeti.thetaFourierCoeff_eq_integral`: the explicit integral formula
  `∫ t in 0..1, exp (-2πi(m + α)t) * s t`.
* `TauCeti.thetaFourierCoeff_zero`, `TauCeti.thetaFourierCoeff_smul`,
  `TauCeti.thetaFourierCoeff_add`: linearity of `thetaFourierCoeff`.
* `TauCeti.hasSum_thetaFourierCoeff`: twisted Fourier expansion of quasi-periodic entire functions.
* `TauCeti.summable_norm_thetaFourierCoeff_mul_exp` and
  `TauCeti.summable_norm_thetaFourierCoeff`: exponential coefficient decay and absolute summability.
* `TauCeti.tendsto_thetaFourierCoeff_zero`: Riemann–Lebesgue decay of `thetaFourierCoeff`.
* `TauCeti.eq_zero_of_thetaFourierCoeff_eq_zero`: an entire function with all twisted Fourier
  coefficients zero vanishes identically.
* `TauCeti.periodic_cexp_mul_of_add_one`: `1`-periodicity of `z ↦ exp (-2πi(m + α)z) * s z` for
  quasi-periodic `s`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

open Complex Filter Metric Set
open scoped Real ENNReal Topology

namespace TauCeti

/-- The `m`-th twisted Fourier coefficient of `s : ℂ → ℂ` with real shift `α`, defined as the
`m`-th Fourier coefficient on `[0, 1]` of the untwisted restriction `t ↦ exp (-2πiαt) * s t`. -/
noncomputable def thetaFourierCoeff (α : ℝ) (s : ℂ → ℂ) (m : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun t : ℝ => cexp (-2 * π * I * α * t) * s t) m

/-- Unfolding `thetaFourierCoeff` in terms of `fourierCoeffOn`. -/
theorem thetaFourierCoeff_def (α : ℝ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α s m =
      fourierCoeffOn zero_lt_one (fun t : ℝ => cexp (-2 * π * I * α * t) * s t) m :=
  (rfl)

/-- Explicit integral formula `∫ t in 0..1, exp (-2πi(m + α)t) * s t` for `thetaFourierCoeff`. -/
theorem thetaFourierCoeff_eq_integral (α : ℝ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α s m = ∫ t in (0 : ℝ)..1, cexp (-2 * π * I * (m + α) * t) * s t := by
  rw [thetaFourierCoeff_def, fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [smul_eq_mul, fourier_coe_apply, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The twisted Fourier coefficients of the zero function vanish. -/
@[simp]
theorem thetaFourierCoeff_zero (α : ℝ) (m : ℤ) :
    thetaFourierCoeff α 0 m = 0 := by
  simp [thetaFourierCoeff_eq_integral]

/-- `thetaFourierCoeff` commutes with complex scalar multiplication. -/
@[simp]
theorem thetaFourierCoeff_smul (α : ℝ) (c : ℂ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α (c • s) m = c * thetaFourierCoeff α s m := by
  have hfun : (fun t : ℝ => cexp (-2 * π * I * α * t) * (c • s) t) =
      c • fun t : ℝ => cexp (-2 * π * I * α * t) * s t := by
    ext t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [thetaFourierCoeff_def, hfun, fourierCoeffOn.const_smul, smul_eq_mul, ← thetaFourierCoeff_def]

/-- `thetaFourierCoeff` is additive on functions interval-integrable on `[0, 1]`. -/
theorem thetaFourierCoeff_add {α : ℝ} {s₁ s₂ : ℂ → ℂ}
    (hs₁ : IntervalIntegrable (fun t : ℝ => s₁ t) MeasureTheory.volume 0 1)
    (hs₂ : IntervalIntegrable (fun t : ℝ => s₂ t) MeasureTheory.volume 0 1) (m : ℤ) :
    thetaFourierCoeff α (s₁ + s₂) m = thetaFourierCoeff α s₁ m + thetaFourierCoeff α s₂ m := by
  have hexp : ContinuousOn (fun t : ℝ => cexp (-2 * π * I * α * t)) (uIcc (0 : ℝ) 1) :=
    ((continuous_const.mul continuous_ofReal).cexp).continuousOn
  simp only [thetaFourierCoeff_def, Pi.add_apply, mul_add]
  exact fourierCoeffOn_add zero_lt_one (hs₁.continuousOn_mul hexp) (hs₂.continuousOn_mul hexp) m

/-- If `s (z + 1) = exp (2πiα) * s z`, then `z ↦ exp (-2πi(m + α)z) * s z` is `1`-periodic for
every integer `m : ℤ`. -/
theorem periodic_cexp_mul_of_add_one {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (m : ℤ) :
    Function.Periodic (fun z => cexp (-2 * π * I * (m + α) * z) * s z) 1 := by
  intro z
  simp only [h1, ← mul_assoc, ← Complex.exp_add]
  rw [show -2 * π * I * (m + α) * (z + 1) + 2 * π * I * α =
      -2 * π * I * (m + α) * z + (-m : ℤ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add _ ((-m : ℤ) * (2 * π * I)), Complex.exp_int_mul_two_pi_mul_I, mul_one]

private noncomputable def twistedPeriodic (α : ℝ) (s : ℂ → ℂ) (z : ℂ) : ℂ :=
  cexp (-2 * π * I * α * z) * s z

private noncomputable def twistedCusp (α : ℝ) (s : ℂ → ℂ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction 1 (twistedPeriodic α s)

private lemma periodic_twistedPeriodic {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    Function.Periodic (twistedPeriodic α s) 1 := by
  simpa [twistedPeriodic] using periodic_cexp_mul_of_add_one h1 0

private lemma twistedCusp_qParam {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (z : ℂ) :
    twistedCusp α s (Function.Periodic.qParam 1 z) = twistedPeriodic α s z :=
  Function.Periodic.eq_cuspFunction one_ne_zero (periodic_twistedPeriodic h1) z

private lemma differentiableOn_twistedCusp {α : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    DifferentiableOn ℂ (twistedCusp α s) (eball 0 ⊤ \ closedBall 0 0) := by
  have hdiff : Differentiable ℂ (twistedPeriodic α s) :=
    ((differentiable_id.const_mul _).cexp).mul hs
  intro w hw
  have hw0 : w ≠ 0 := fun h => hw.right (by simp [h])
  have hq : Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 w) = w :=
    Function.Periodic.qParam_right_inv one_ne_zero hw0
  rw [← hq]
  exact (Function.Periodic.differentiableAt_cuspFunction one_ne_zero
    (periodic_twistedPeriodic h1) (hdiff _)).differentiableWithinAt

private lemma thetaFourierCoeff_eq_circleLaurentCoeff {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (m : ℤ) :
    thetaFourierCoeff α s m = circleLaurentCoeff (twistedCusp α s) 0 1 m := by
  rw [thetaFourierCoeff_def]
  exact (circleLaurentCoeff_cuspFunction_eq_fourierCoeffOn zero_lt_one
    (periodic_twistedPeriodic h1) m).symm

private lemma hasLaurentSeriesOnAnnulus_twistedCusp {α : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    HasLaurentSeriesOnAnnulus (twistedCusp α s) (thetaFourierCoeff α s) 0 0 ⊤ := by
  have hL := (differentiableOn_twistedCusp hs h1).hasLaurentSeriesOnAnnulus le_rfl zero_lt_one
    (ENNReal.ofReal_lt_top)
  have hcoeff : circleLaurentCoeff (twistedCusp α s) 0 1 = thetaFourierCoeff α s :=
    funext fun m => (thetaFourierCoeff_eq_circleLaurentCoeff h1 m).symm
  rwa [hcoeff] at hL

/-- **Twisted Fourier expansion.** Every entire function `s : ℂ → ℂ` satisfying
`s (z + 1) = exp (2πiα) * s z` is the sum of its twisted Fourier series at every `z ∈ ℂ`. -/
theorem hasSum_thetaFourierCoeff {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (z : ℂ) :
    HasSum (fun m : ℤ => thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * z)) (s z) := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  have hq : Function.Periodic.qParam 1 z ∈ eball 0 ⊤ \ closedBall 0 0 := by
    refine ⟨by simp, fun hmem => ?_⟩
    exact Function.Periodic.qParam_ne_zero z (by simpa using hmem)
  have hsum := (hL.hasSum hq).mul_left (cexp (2 * π * I * α * z))
  have hrhs : cexp (2 * π * I * α * z) * twistedCusp α s (Function.Periodic.qParam 1 z) = s z := by
    rw [twistedCusp_qParam h1, twistedPeriodic, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [hrhs] at hsum
  refine hsum.congr_fun fun m => ?_
  simp only [sub_zero, smul_eq_mul, Periodic.qParam_one_zpow]
  symm
  calc
    cexp (2 * π * I * α * z) * (cexp (2 * π * I * m * z) * thetaFourierCoeff α s m) =
        thetaFourierCoeff α s m * (cexp (2 * π * I * α * z) * cexp (2 * π * I * m * z)) :=
      by ring
    _ = thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * z) := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- The twisted Fourier coefficients of a quasi-periodic entire function decay faster than every
exponential weight `exp (-2πmy)`. -/
theorem summable_norm_thetaFourierCoeff_mul_exp {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (y : ℝ) :
    Summable (fun m : ℤ => ‖thetaFourierCoeff α s m‖ * Real.exp (-2 * π * m * y)) := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  have hsum := hL.summable_norm_mul_zpow (ρ := Real.exp (-2 * π * y)) (Real.exp_pos _)
    (ENNReal.ofReal_lt_top)
  refine hsum.congr fun m => ?_
  congr 1
  exact Complex.ofReal_injective (by
    push_cast
    rw [← Complex.exp_intCast_mul]
    congr 1
    ring)

/-- The twisted Fourier coefficients of a quasi-periodic entire function are absolutely summable. -/
theorem summable_norm_thetaFourierCoeff {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    Summable (fun m : ℤ => ‖thetaFourierCoeff α s m‖) := by
  simpa using summable_norm_thetaFourierCoeff_mul_exp hs h1 0

/-- The twisted Fourier coefficients of any function `s : ℂ → ℂ` tend to `0` along the cofinite
filter on `ℤ` (by the Riemann–Lebesgue lemma). -/
theorem tendsto_thetaFourierCoeff_zero (α : ℝ) (s : ℂ → ℂ) :
    Tendsto (thetaFourierCoeff α s) cofinite (𝓝 0) := by
  let f : ℝ → ℂ := Set.indicator (Ioc (0 : ℝ) 1) fun t => cexp (-2 * π * I * α * t) * s t
  have htend : Tendsto (fun m : ℤ => (m : ℝ)) cofinite (cocompact ℝ) := by
    simpa [Filter.cocompact_eq_cofinite] using Int.isClosedEmbedding_coe_real.tendsto_cocompact
  refine ((Real.tendsto_integral_exp_smul_cocompact f).comp htend).congr fun m => ?_
  dsimp only [Function.comp_def, f]
  rw [thetaFourierCoeff_eq_integral, intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem ht, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp [Set.indicator_of_notMem ht]

/-- An entire function whose twisted Fourier coefficients all vanish is identically zero. -/
theorem eq_zero_of_thetaFourierCoeff_eq_zero {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h0 : ∀ m : ℤ, thetaFourierCoeff α s m = 0) : s = 0 := by
  let f : ℝ → ℂ := fun t => cexp (-2 * π * I * α * t) * s t
  have hf_cont : Continuous f :=
    ((continuous_const.mul continuous_ofReal).cexp).mul (hs.continuous.comp continuous_ofReal)
  have hf0 : EqOn f 0 (Icc (0 : ℝ) 1) :=
    eqOn_Icc_of_fourierCoeffOn_eq zero_lt_one hf_cont.continuousOn continuousOn_const fun m => by
      dsimp only [f]
      rw [← thetaFourierCoeff_def, h0, fourierCoeffOn_eq_integral]
      simp
  have hmem : (1 / 2 : ℝ) ∈ closure (Ioo (1 / 2 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num)]
    exact left_mem_Icc.mpr (by norm_num)
  have hsub : Complex.ofReal '' Ioo (1 / 2 : ℝ) 1 ⊆ {z : ℂ | s z = 0} \ {((1 / 2 : ℝ) : ℂ)} := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(mul_eq_zero.mp (hf0 ⟨by linarith [ht.1], ht.2.le⟩)).resolve_left
      (Complex.exp_ne_zero _), fun heq => ht.1.ne' (Complex.ofReal_injective heq)⟩
  have hcl : ((1 / 2 : ℝ) : ℂ) ∈ closure ({z : ℂ | s z = 0} \ {((1 / 2 : ℝ) : ℂ)}) :=
    closure_mono hsub (mem_closure_image continuous_ofReal.continuousAt hmem)
  ext z
  exact (analyticOnNhd_univ_iff_differentiable.mpr hs).eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_univ (mem_univ _) hcl (mem_univ z)

end TauCeti
