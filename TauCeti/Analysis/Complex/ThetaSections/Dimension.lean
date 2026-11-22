/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.ThetaSections.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.Laurent.Periodic
import TauCeti.Analysis.Complex.Periodic
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Twisted Fourier analysis, boundary vanishing, and level-0 theta sections

Via the exponential coordinate `w = exp (2πiz)` (`Function.Periodic.qParam 1`) and Laurent
expansion on `ℂ \ {0}` (`DifferentiableOn.hasLaurentSeriesOnAnnulus`), every entire function
quasi-periodic under `z ↦ z + 1` expands into a twisted Fourier series with coefficients
`thetaFourierCoeff α s m = ∫ t in 0..1, exp (-2πi(m + α)t) * s t`, and the `τ`-automorphy law is
equivalent to the exact shift-by-`k` recurrence
`c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m`.

Building on `TauCeti.NumberTheory.ModularForms.JacobiTheta.Sections` (which constructs the
characteristic theta basis `TauCeti.thetaSectionsBasis` and proves `TauCeti.finrank_thetaSections`
for `0 < k` and `0 < τ.im`) and `TauCeti.Analysis.Complex.ThetaLine`, this file establishes the
twisted Fourier expansion and recurrence, additional `characteristicTheta` identities, unconditional
lattice invariance of `thetaMetric k τ z * ‖s z‖²`, and the boundary dimension classifications
for `0 < k` with `τ.im ≤ 0` and for `k = 0` with `τ.im ≠ 0`.

## Main definitions

* `TauCeti.thetaFourierCoeff`: the `m`-th twisted Fourier coefficient on `[0, 1]`.

## Main results

* `TauCeti.hasSum_thetaFourierCoeff`, `TauCeti.summable_norm_thetaFourierCoeff_mul_exp`,
  `TauCeti.forall_add_tau_iff_forall_thetaFourierCoeff_add`, and
  `TauCeti.thetaFourierCoeff_add_of_mem_thetaSections`: twisted Fourier expansion and exponential
  coefficient decay for quasi-periodic entire functions, exact equivalence with the integer-level
  coefficient recurrence, and the recurrence for theta sections.
* `TauCeti.thetaSections_eq_bot_of_im_nonpos` and `TauCeti.finrank_thetaSections_of_im_nonpos`:
  vanishing of `thetaSections k τ α β` for `0 < k` and `τ.im ≤ 0`.
* `TauCeti.thetaMetric_mul_norm_sq_add_int_add_int_mul_tau`: unconditional lattice invariance of
  the pointwise Hermitian norm squared `thetaMetric k τ z * ‖s z‖²` for theta sections.
* `TauCeti.characteristicTheta_undef`, `TauCeti.characteristicTheta_index_add_level`,
  `TauCeti.hasSum_characteristicTheta`, `TauCeti.thetaFourierCoeff_characteristicTheta_add_mul`,
  `TauCeti.thetaFourierCoeff_characteristicTheta_eq_zero`, and
  `TauCeti.eq_sum_characteristicTheta_of_mem_thetaSections`: additional properties and full
  twisted Fourier expansions of characteristic theta functions.
* `TauCeti.mem_thetaSections_zero_iff_const`, `TauCeti.thetaSections_zero_eq_bot_of_not_int`, and
  `TauCeti.finrank_thetaSections_zero`: complete classification and dimension formula at level
  `k = 0` for `τ.im ≠ 0`.

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

/-! ### Twisted Fourier coefficients and Laurent expansion -/

/-- The `m`-th twisted Fourier coefficient of `s : ℂ → ℂ` with real shift `α`:
`thetaFourierCoeff α s m = ∫ t in 0..1, exp (-2πi(m + α)t) * s t`. -/
noncomputable def thetaFourierCoeff (α : ℝ) (s : ℂ → ℂ) (m : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, cexp (-2 * π * I * (m + α) * t) * s t

/-- Defining integral formula for `thetaFourierCoeff`. -/
theorem thetaFourierCoeff_def (α : ℝ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α s m = ∫ t in (0 : ℝ)..1, cexp (-2 * π * I * (m + α) * t) * s t :=
  (rfl)

/-- The twisted Fourier coefficients of the zero function vanish. -/
@[simp]
theorem thetaFourierCoeff_zero (α : ℝ) (m : ℤ) :
    thetaFourierCoeff α 0 m = 0 := by
  simp [thetaFourierCoeff_def]

/-- `thetaFourierCoeff` commutes with complex scalar multiplication. -/
@[simp]
theorem thetaFourierCoeff_smul (α : ℝ) (c : ℂ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α (c • s) m = c * thetaFourierCoeff α s m := by
  simp only [thetaFourierCoeff_def, Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

private lemma fourierCoeffOn_twistedPeriodic_eq_thetaFourierCoeff (α : ℝ) (s : ℂ → ℂ) (m : ℤ) :
    fourierCoeffOn zero_lt_one (fun t : ℝ => cexp (-2 * π * I * α * t) * s t) m =
      thetaFourierCoeff α s m := by
  rw [fourierCoeffOn_eq_integral, thetaFourierCoeff_def]
  simp only [sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [smul_eq_mul, fourier_coe_apply, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `thetaFourierCoeff` is additive on functions interval-integrable on `[0, 1]`. -/
theorem thetaFourierCoeff_add {α : ℝ} {s₁ s₂ : ℂ → ℂ}
    (hs₁ : IntervalIntegrable (fun t : ℝ => s₁ t) MeasureTheory.volume 0 1)
    (hs₂ : IntervalIntegrable (fun t : ℝ => s₂ t) MeasureTheory.volume 0 1) (m : ℤ) :
    thetaFourierCoeff α (s₁ + s₂) m = thetaFourierCoeff α s₁ m + thetaFourierCoeff α s₂ m := by
  have hexp : ContinuousOn (fun t : ℝ => cexp (-2 * π * I * α * t)) (uIcc (0 : ℝ) 1) :=
    ((continuous_const.mul continuous_ofReal).cexp).continuousOn
  simp only [← fourierCoeffOn_twistedPeriodic_eq_thetaFourierCoeff, Pi.add_apply, mul_add]
  exact fourierCoeffOn_add zero_lt_one (hs₁.continuousOn_mul hexp) (hs₂.continuousOn_mul hexp) m

private noncomputable def twistedPeriodic (α : ℝ) (s : ℂ → ℂ) (z : ℂ) : ℂ :=
  cexp (-2 * π * I * α * z) * s z

private noncomputable def twistedCusp (α : ℝ) (s : ℂ → ℂ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction 1 (twistedPeriodic α s)

private lemma periodic_twistedPeriodic {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    Function.Periodic (twistedPeriodic α s) 1 := by
  intro z
  simp only [twistedPeriodic, h1]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

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
  rw [← fourierCoeffOn_twistedPeriodic_eq_thetaFourierCoeff α s m]
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
  rw [thetaFourierCoeff_def, intervalIntegral.integral_of_le zero_le_one,
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
      rw [fourierCoeffOn_twistedPeriodic_eq_thetaFourierCoeff, h0, fourierCoeffOn_eq_integral]
      simp
  have hIoc : ∀ t ∈ Ioc (0 : ℝ) 1, s t = 0 := fun t ht =>
    (mul_eq_zero.mp (hf0 (Ioc_subset_Icc_self ht))).resolve_left (Complex.exp_ne_zero _)
  have hcl : ((1 / 2 : ℝ) : ℂ) ∈ closure ({z : ℂ | s z = 0} \ {((1 / 2 : ℝ) : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (1 / 4) (ε / 2)
    have hδpos : 0 < δ := lt_min (by norm_num) (half_pos hε)
    have hδle1 : δ ≤ 1 / 4 := min_le_left _ _
    have hδle2 : δ ≤ ε / 2 := min_le_right _ _
    refine ⟨(((1 / 2 : ℝ) + δ : ℝ) : ℂ), ⟨hIoc _ ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
    · intro hEq
      linarith [Complex.ofReal_injective (Set.mem_singleton_iff.mp hEq)]
    · rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
      have : (1 / 2 : ℝ) - ((1 / 2 : ℝ) + δ) = -δ := by ring
      rw [this, norm_neg, Real.norm_of_nonneg hδpos.le]
      linarith
  ext z
  exact (analyticOnNhd_univ_iff_differentiable.mpr hs).eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_univ (mem_univ _) hcl (mem_univ z)

private lemma twistedCusp_mul_qParam_eq {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    {w : ℂ} (hw0 : w ≠ 0) :
    twistedCusp α s (Function.Periodic.qParam 1 τ * w) =
      cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) * w ^ (-k) *
        twistedCusp α s w := by
  set z := Function.Periodic.invQParam 1 w
  have hqz : Function.Periodic.qParam 1 z = w := Function.Periodic.qParam_right_inv one_ne_zero hw0
  have hqadd : Function.Periodic.qParam 1 τ * w = Function.Periodic.qParam 1 (z + τ) := by
    rw [← hqz, Periodic.qParam_one, Periodic.qParam_one, Periodic.qParam_one, ← Complex.exp_add]
    congr 1
    ring
  rw [hqadd, twistedCusp_qParam h1, twistedPeriodic, hτ z, ← hqz, twistedCusp_qParam h1,
    twistedPeriodic, Periodic.qParam_one_zpow]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma thetaFourierCoeff_add_of_add_tau {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    (m : ℤ) :
    thetaFourierCoeff α s (m + k) =
      cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
        thetaFourierCoeff α s m := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  have hL₁ : HasLaurentSeriesOnAnnulus
      (fun w => twistedCusp α s (Function.Periodic.qParam 1 τ * w))
      (fun n : ℤ => Function.Periodic.qParam 1 τ ^ n * thetaFourierCoeff α s n) 0 0 ⊤ := by
    simpa [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] using
      hL.comp_mul (Function.Periodic.qParam_ne_zero τ)
  have hm : Function.Periodic.qParam 1 τ ^ m * thetaFourierCoeff α s m =
      cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) *
        thetaFourierCoeff α s (m + k) := by
    rw [← hL₁.circleLaurentCoeff_eq zero_lt_one ENNReal.ofReal_lt_top m,
      circleLaurentCoeff_congr zero_le_one
        (g := fun w => cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) •
          ((w - 0) ^ (-k) • twistedCusp α s w))
        (fun w hw => by
          simpa [smul_eq_mul, mul_assoc] using
            twistedCusp_mul_qParam_eq h1 hτ (fun h => by simp [h] at hw)) m,
      circleLaurentCoeff_smul, circleLaurentCoeff_sub_zpow_smul_apply, sub_neg_eq_add,
      ← thetaFourierCoeff_eq_circleLaurentCoeff h1, smul_eq_mul]
  have hinv : cexp (2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ) *
      cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) = 1 := by
    rw [← Complex.exp_add]
    have : 2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ +
        (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hsol := congrArg (cexp (2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ) * ·) hm.symm
  rw [← mul_assoc, hinv, one_mul] at hsol
  rw [hsol, Periodic.qParam_one_zpow, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **Fourier recurrence characterization.** For an entire function `s` satisfying
`s (z + 1) = exp (2πiα) * s z` and any integer level `k : ℤ`, the second automorphy relation
`s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z` holds for all `z ∈ ℂ` if and only if its twisted
Fourier coefficients satisfy `c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m` for all
`m ∈ ℤ`. -/
theorem forall_add_tau_iff_forall_thetaFourierCoeff_add {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    (∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) ↔
      ∀ m : ℤ, thetaFourierCoeff α s (m + k) =
        cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
          thetaFourierCoeff α s m := by
  refine ⟨fun hτ m => thetaFourierCoeff_add_of_add_tau hs h1 hτ m, fun hrec z => ?_⟩
  have hL := hasSum_thetaFourierCoeff hs h1 (z + τ)
  have hR := (hasSum_thetaFourierCoeff hs h1 z).mul_left
    (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z))
  rw [← (Equiv.addRight k).hasSum_iff] at hR
  have hR' : HasSum
      (fun m : ℤ => thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * (z + τ)))
      (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) := by
    refine hR.congr_fun fun m => ?_
    simp only [Function.comp_def, Equiv.coe_addRight, hrec m]
    calc
      thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * (z + τ)) =
          thetaFourierCoeff α s m *
            (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
              cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
              cexp (2 * π * I * ((m + k : ℤ) + α) * z)) := by
        simp only [← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
            (cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
              thetaFourierCoeff α s m * cexp (2 * π * I * ((m + k : ℤ) + α) * z)) := by ring
  exact hL.unique hR'

/-- The twisted Fourier coefficients of a level-`k` theta section satisfy the shift-by-`k`
recurrence `c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m`. -/
theorem thetaFourierCoeff_add_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m : ℤ) :
    thetaFourierCoeff α s (m + k) =
      cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
        thetaFourierCoeff α s m := by
  rcases mem_thetaSections_iff.mp hs with ⟨hd, h1, hτ⟩
  exact (forall_add_tau_iff_forall_thetaFourierCoeff_add (k := (k : ℤ)) hd h1).mp
    (by simpa only [Int.cast_natCast] using hτ) m

/-! ### Vanishing for `τ.im ≤ 0` and unconditional metric descent -/

private lemma norm_thetaFourierCoeff_add_level {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n : ℤ) :
    ‖thetaFourierCoeff α s (n + k)‖ =
      Real.exp (-2 * π * ((n : ℝ) + α + (k : ℝ) / 2) * τ.im) * ‖thetaFourierCoeff α s n‖ := by
  rw [thetaFourierCoeff_add_of_mem_thetaSections hs n, norm_mul, Complex.norm_exp]
  congr 2
  have hexp : 2 * π * I * ((n : ℂ) + α) * τ - 2 * π * I * β + π * I * k * τ =
      (↑(2 * π * ((n : ℝ) + α + (k : ℝ) / 2)) * τ - ↑(2 * π * β)) * I := by
    push_cast
    ring
  rw [hexp, Complex.mul_I_re, Complex.sub_im, Complex.im_ofReal_mul, Complex.ofReal_im]
  ring

private lemma thetaFourierCoeff_add_eq_zero_iff {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n : ℤ) :
    thetaFourierCoeff α s (n + k) = 0 ↔ thetaFourierCoeff α s n = 0 := by
  rw [thetaFourierCoeff_add_of_mem_thetaSections hs n, mul_eq_zero,
    or_iff_right (Complex.exp_ne_zero _)]

private lemma thetaFourierCoeff_add_int_mul_eq_zero_iff {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n q : ℤ) :
    thetaFourierCoeff α s (n + q * k) = 0 ↔ thetaFourierCoeff α s n = 0 := by
  induction q using Int.induction_on with
  | zero => simp only [zero_mul, add_zero]
  | succ i ih =>
    have hidx : n + ((i : ℤ) + 1) * k = (n + i * k) + k := by ring
    rw [hidx, thetaFourierCoeff_add_eq_zero_iff hs, ih]
  | pred i ih =>
    have hidx : n + (-(i : ℤ)) * k = (n + (-(i : ℤ) - 1) * k) + k := by ring
    rw [hidx, thetaFourierCoeff_add_eq_zero_iff hs] at ih
    exact ih

/-- When `k > 0` and `τ.im ≤ 0`, there are no nonzero holomorphic theta sections. -/
theorem thetaSections_eq_bot_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : thetaSections k τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α) (mem_thetaSections_iff.mp hs).left
    fun m => ?_
  have hzero_ge : ∀ n : ℤ, 0 ≤ (n : ℝ) + α + (k : ℝ) / 2 → thetaFourierCoeff α s n = 0 := by
    intro n hn
    have hle : ∀ j : ℕ, ‖thetaFourierCoeff α s n‖ ≤ ‖thetaFourierCoeff α s (n + j * k)‖ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hidx : n + ((j + 1 : ℕ) : ℤ) * k = (n + j * k) + k := by push_cast; ring
        rw [hidx, norm_thetaFourierCoeff_add_level hs]
        have hpos : 0 ≤ ((n + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2 := by
          push_cast
          have hjk : (0 : ℝ) ≤ (j : ℝ) * (k : ℝ) := by positivity
          linarith
        have harg : 0 ≤ -2 * π * (((n + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2) * τ.im :=
          mul_nonneg_of_nonpos_of_nonpos (by nlinarith [Real.pi_pos, hpos]) hτ
        exact ih.trans (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp harg))
    have hinj : Function.Injective (fun j : ℕ => n + (j : ℤ) * k) := fun j₁ j₂ h => by
      have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
      exact Int.natCast_inj.mp (mul_right_cancel₀ hk0 (add_left_cancel h))
    have htend : Tendsto (fun j : ℕ => ‖thetaFourierCoeff α s (n + j * k)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (tendsto_thetaFourierCoeff_zero α s).norm.comp
          (Nat.cofinite_eq_atTop ▸ hinj.tendsto_cofinite)
    have hnorm0 : ‖thetaFourierCoeff α s n‖ ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds htend hle
    exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
  obtain ⟨j, hj⟩ := exists_nat_gt (-(m : ℝ) - α - (k : ℝ) / 2)
  have hge : 0 ≤ ((m + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2 := by
    push_cast
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hj0 : thetaFourierCoeff α s (m + j * k) = 0 := hzero_ge _ hge
  exact (thetaFourierCoeff_add_int_mul_eq_zero_iff hs m j).mp hj0

/-- For positive level `k > 0` and `τ.im ≤ 0`, `thetaSections k τ α β` has dimension `0`. -/
theorem finrank_thetaSections_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : Module.finrank ℂ (thetaSections k τ α β) = 0 := by
  rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, finrank_bot]

/-- For every theta section `s`, the pointwise Hermitian norm squared `thetaMetric k τ z * ‖s z‖²`
is doubly periodic on the lattice `ℤ + τℤ`, unconditionally in `τ`. -/
theorem thetaMetric_mul_norm_sq_add_int_add_int_mul_tau {k : ℕ} {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  by_cases hτ : τ.im = 0
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [add_int_add_int_mul_tau_of_mem_thetaSections hs m n z, norm_mul, mul_pow,
        norm_thetaFactor]
      simp [thetaMetric_def]
    · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ.le α β, Submodule.mem_bot] at hs
      simp [hs]
  · exact thetaMetric_add_mul_norm_sq hτ
      (add_int_add_int_mul_tau_of_mem_thetaSections hs m n z)

/-! ### Additional properties of characteristic theta functions -/

/-- At level `k = 1`, zero characteristics, and `r = 0`, `characteristicTheta` reduces to
`jacobiTheta₂`. -/
@[simp]
theorem characteristicTheta_one_zero (τ z : ℂ) :
    characteristicTheta 1 τ 0 0 0 z = jacobiTheta₂ z τ := by
  simp [characteristicTheta_apply]

/-- When `k = 0` or `τ.im ≤ 0`, `characteristicTheta` vanishes identically (inheriting the
junk-value convention `jacobiTheta₂_undef`). -/
theorem characteristicTheta_undef {k : ℕ} {τ : ℂ} (h : k = 0 ∨ τ.im ≤ 0) (α β : ℝ) (r : ℤ)
    (z : ℂ) : characteristicTheta k τ α β r z = 0 := by
  have him : (k * τ).im ≤ 0 := by
    rw [← ofReal_natCast, im_ofReal_mul]
    rcases h with rfl | hτ
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hτ
  simp [characteristicTheta_apply, jacobiTheta₂_undef _ him]

/-- At level `k = 0`, `characteristicTheta` vanishes identically. -/
@[simp]
theorem characteristicTheta_zero (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta 0 τ α β r z = 0 :=
  characteristicTheta_undef (Or.inl rfl) α β r z

/-- When `τ.im ≤ 0`, `characteristicTheta` vanishes identically. -/
@[simp]
theorem characteristicTheta_of_im_nonpos (k : ℕ) {τ : ℂ} (hτ : τ.im ≤ 0) (α β : ℝ) (r : ℤ)
    (z : ℂ) : characteristicTheta k τ α β r z = 0 :=
  characteristicTheta_undef (Or.inr hτ) α β r z

/-- First generator automorphy law for `characteristicTheta`. -/
theorem characteristicTheta_add_one (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r (z + 1) =
      cexp (2 * π * I * α) * characteristicTheta k τ α β r z :=
  (mem_thetaSections_iff.mp (characteristicTheta_mem_thetaSections k τ α β r)).right.left z

/-- Second generator automorphy law for `characteristicTheta`. -/
theorem characteristicTheta_add_tau (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r (z + τ) =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
        characteristicTheta k τ α β r z :=
  (mem_thetaSections_iff.mp (characteristicTheta_mem_thetaSections k τ α β r)).right.right z

/-- Shifting the characteristic index `r` by the level `k` multiplies `characteristicTheta` by a
nonzero scalar depending only on `(k, τ, α, β, r)`. -/
theorem characteristicTheta_index_add_level (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β (r + k) z =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * (r + α) * τ) *
        characteristicTheta k τ α β r z := by
  have harg : k * z + ((r + k : ℤ) + α) * τ - β = (k * z + (r + α) * τ - β) + k * τ := by
    push_cast
    ring
  rw [characteristicTheta_apply, characteristicTheta_apply, harg, jacobiTheta₂_add_left',
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every `characteristicTheta k τ α β r` is an entire function of `z` (for all `k : ℕ` and
`τ : ℂ`). -/
theorem differentiable_characteristicTheta (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) :
    Differentiable ℂ (characteristicTheta k τ α β r) :=
  (mem_thetaSections_iff.mp (characteristicTheta_mem_thetaSections k τ α β r)).left

/-- Mathlib's `jacobiTheta₂ · τ` is a level-`1` theta section with zero characteristics for every
`τ : ℂ`. -/
theorem jacobiTheta₂_mem_thetaSections (τ : ℂ) :
    (fun z => jacobiTheta₂ z τ) ∈ thetaSections 1 τ 0 0 := by
  have hfun : (fun z => jacobiTheta₂ z τ) = characteristicTheta 1 τ 0 0 0 :=
    funext fun z => (characteristicTheta_one_zero τ z).symm
  rw [hfun]
  exact characteristicTheta_mem_thetaSections 1 τ 0 0 0

/-- Explicit `ℤ`-indexed Fourier series of `characteristicTheta k τ α β r` supported on the
congruence class `r + kℤ`, for `0 < k` and `0 < τ.im`. -/
theorem hasSum_characteristicTheta {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : ℤ) (z : ℂ) :
    HasSum
      (fun n : ℤ =>
        cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ) *
          cexp (2 * π * I * ((r + n * k : ℤ) + α) * z))
      (characteristicTheta k τ α β r z) := by
  have hkτ : 0 < (k * τ).im := by
    rw [← ofReal_natCast, im_ofReal_mul]
    exact mul_pos (Nat.cast_pos.mpr hk) hτ
  have hsum := (hasSum_jacobiTheta₂_term (k * z + (r + α) * τ - β) hkτ).mul_left
    (cexp (2 * π * I * (r + α) * z))
  rw [← characteristicTheta_apply] at hsum
  refine hsum.congr_fun fun n => ?_
  simp only [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma thetaFourierCoeff_characteristicTheta_eq {k : ℕ} (hk : 0 < k) {τ : ℂ}
    (hτ : 0 < τ.im) (α β : ℝ) (r m : ℤ) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) m =
      if (k : ℤ) ∣ m - r then
        let n : ℤ := (m - r) / k
        cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ)
      else 0 := by
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hkτ : 0 < ((k : ℂ) * τ).im := by
    rw [← ofReal_natCast, im_ofReal_mul]
    exact mul_pos (Nat.cast_pos.mpr hk) hτ
  have hint := integral_cexp_mul_jacobiTheta₂_mul_add hk0 (r - m) ((r + α) * τ - β) hkτ
  have hcongr :
      thetaFourierCoeff α (characteristicTheta k τ α β r) m =
        ∫ x in (0 : ℝ)..1,
          cexp (2 * π * I * (r - m : ℤ) * x) *
            jacobiTheta₂ (((k : ℤ) : ℂ) * x + ((r + α) * τ - β)) (k * τ) := by
    rw [thetaFourierCoeff_def]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [characteristicTheta_apply, ← mul_assoc, ← Complex.exp_add]
    congr 2
    · push_cast; ring
    · push_cast; ring
  have hdvd : ((k : ℤ) ∣ r - m) ↔ ((k : ℤ) ∣ m - r) := by
    rw [← dvd_neg, neg_sub]
  rw [hcongr, hint]
  simp only [hdvd]
  split_ifs with h
  · obtain ⟨n, hn⟩ := h
    have hrm : r - m = (k : ℤ) * (-n) := by linarith
    rw [hn, hrm, Int.mul_ediv_cancel_left _ hk0, Int.mul_ediv_cancel_left _ hk0, neg_neg,
      jacobiTheta₂_term]
    congr 1
    ring
  · rfl

/-- On the congruence class `r + kℤ`, the twisted Fourier coefficients of `characteristicTheta`
are given by the explicit Gaussian exponentials. -/
theorem thetaFourierCoeff_characteristicTheta_add_mul {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r n : ℤ) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) (r + n * k) =
      cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ) := by
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hdvd : (k : ℤ) ∣ (r + n * k) - r := by
    rw [add_sub_cancel_left]
    exact dvd_mul_left (k : ℤ) n
  have hdiv : ((r + n * (k : ℤ)) - r) / (k : ℤ) = n := by
    rw [add_sub_cancel_left, Int.mul_ediv_cancel n hk0]
  rw [thetaFourierCoeff_characteristicTheta_eq hk hτ α β r (r + n * k)]
  simp only [hdvd, ↓reduceIte, hdiv]

/-- Off the congruence class `r + kℤ`, all twisted Fourier coefficients of `characteristicTheta`
vanish. -/
theorem thetaFourierCoeff_characteristicTheta_eq_zero (k : ℕ) (τ : ℂ) (α β : ℝ) {r m : ℤ}
    (h : ¬ (k : ℤ) ∣ m - r) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) m = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hzero : characteristicTheta 0 τ α β r = 0 :=
      funext fun z => characteristicTheta_undef (Or.inl rfl) α β r z
    simp [hzero]
  · rcases le_or_gt τ.im 0 with hτ | hτ
    · have hzero : characteristicTheta k τ α β r = 0 :=
        funext fun z => characteristicTheta_undef (Or.inr hτ) α β r z
      simp [hzero]
    · rw [thetaFourierCoeff_characteristicTheta_eq hk hτ α β r m, ite_eq_right h]

/-- Duality between the `k` characteristic theta functions and the first `k` twisted Fourier
coefficients. -/
@[simp]
theorem thetaFourierCoeff_characteristicTheta_fin {k : ℕ} {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r r' : Fin k) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) r' = if r' = r then 1 else 0 := by
  by_cases hrr : r' = r
  · subst hrr
    simpa using thetaFourierCoeff_characteristicTheta_add_mul r'.pos hτ α β (r' : ℤ) 0
  · rw [ite_eq_right hrr]
    refine thetaFourierCoeff_characteristicTheta_eq_zero k τ α β ?_
    rintro ⟨q, hq⟩
    have hr1 : (r : ℤ) < k := Int.ofNat_lt.mpr r.isLt
    have hr2 : (r' : ℤ) < k := Int.ofNat_lt.mpr r'.isLt
    have hq0 : q = 0 := by nlinarith [Int.natCast_nonneg (r : ℕ), Int.natCast_nonneg (r' : ℕ)]
    rw [hq0, mul_zero] at hq
    have heq : (r' : ℤ) = r := sub_eq_zero.mp hq
    exact hrr (Fin.ext (Int.natCast_inj.mp heq))

/-- Every level-`k` theta section (`0 < k`) is the finite linear combination of the `k`
characteristic theta functions weighted by its first `k` twisted Fourier coefficients. -/
theorem eq_sum_characteristicTheta_of_mem_thetaSections {k : ℕ} (hk : 0 < k) {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s z = ∑ r : Fin k, thetaFourierCoeff α s r * characteristicTheta k τ α β r z := by
  rcases lt_or_ge 0 τ.im with hτ | hτ
  · have hrepr := (thetaSectionsBasis hk hτ α β).sum_repr ⟨s, hs⟩
    have hval := congrFun (congrArg Subtype.val hrepr.symm) z
    rw [Submodule.coe_sum, Finset.sum_apply] at hval
    refine hval.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, thetaSectionsBasis_repr_apply,
      thetaSectionsBasis_apply, thetaFourierCoeff_def, Int.cast_natCast]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    congr 2
    ring
  · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, Submodule.mem_bot] at hs
    simp [hs]

/-! ### Level-`0` classification -/

private lemma thetaFourierCoeff_zero_level_eq_zero_of_ne {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections 0 τ α β) {m : ℤ} (hm : thetaFourierCoeff α s m ≠ 0) :
    (m : ℝ) + α = 0 ∧ ∃ b : ℤ, (b : ℝ) = β := by
  have hrec := thetaFourierCoeff_add_of_mem_thetaSections hs m
  simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul] at hrec
  have hexp : cexp (2 * π * I * (m + α) * τ - 2 * π * I * β) = 1 :=
    mul_right_cancel₀ hm (by simpa only [one_mul] using hrec.symm)
  have hnorm_eq := norm_thetaFourierCoeff_add_level hs m
  simp only [Nat.cast_zero, add_zero, zero_div] at hnorm_eq
  have hnorm : Real.exp (-2 * π * ((m : ℝ) + α) * τ.im) = 1 :=
    mul_right_cancel₀ (norm_ne_zero_iff.mpr hm) (by simpa only [one_mul] using hnorm_eq.symm)
  have hma : (m : ℝ) + α = 0 := by
    have hmul : -2 * π * ((m : ℝ) + α) * τ.im = 0 :=
      Real.exp_injective (by simpa only [Real.exp_zero] using hnorm)
    have hne : -2 * π * τ.im ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Real.pi_pos.ne') hτ
    have : (-2 * π * τ.im) * ((m : ℝ) + α) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hne
  have hmaC : ((m : ℂ) + α) = 0 := by exact_mod_cast hma
  have hneg : 2 * π * I * (m + α) * τ - 2 * π * I * β = -(2 * π * I * (β : ℂ)) := by
    rw [hmaC]
    ring
  rw [hneg, Complex.exp_neg, inv_eq_one,
    Complex.exp_two_pi_mul_I_mul_ofReal_eq_one_iff] at hexp
  exact ⟨hma, hexp⟩

/-- At level `k = 0` with `τ.im ≠ 0` and integer characteristics `(α, β) ∈ ℤ × ℤ`, the theta
sections are precisely the constant functions. -/
theorem mem_thetaSections_zero_iff_const {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (hα : ∃ a : ℤ, (a : ℝ) = α) (hβ : ∃ b : ℤ, (b : ℝ) = β) {s : ℂ → ℂ} :
    s ∈ thetaSections 0 τ α β ↔ ∃ c : ℂ, s = fun _ => c := by
  rcases hα with ⟨a, rfl⟩
  rcases hβ with ⟨b, rfl⟩
  constructor
  · intro hs
    rcases mem_thetaSections_iff.mp hs with ⟨hd, h1, _⟩
    refine ⟨thetaFourierCoeff a s (-a), ?_⟩
    ext z
    have hsum := hasSum_thetaFourierCoeff hd h1 z
    have hsingle : HasSum
        (fun m : ℤ => thetaFourierCoeff a s m * cexp (2 * π * I * (m + a) * z))
        (thetaFourierCoeff a s (-a)) := by
      have hterm : thetaFourierCoeff a s (-a) * cexp (2 * π * I * (((-a : ℤ) : ℂ) + a) * z) =
          thetaFourierCoeff a s (-a) := by
        simp
      rw [← hterm]
      refine hasSum_ite_eq (-a) _ |>.congr_fun fun m => ?_
      by_cases hm : m = -a
      · subst hm; simp
      · rw [ite_eq_right hm]
        by_contra hne
        have hcne : thetaFourierCoeff a s m ≠ 0 := left_ne_zero_of_mul hne
        have hma := (thetaFourierCoeff_zero_level_eq_zero_of_ne hτ hs hcne).left
        have hmaZ : m + a = 0 := by exact_mod_cast hma
        exact hm (eq_neg_of_add_eq_zero_left hmaZ)
    exact hsum.unique hsingle
  · rintro ⟨c, rfl⟩
    refine mem_thetaSections_iff.mpr ⟨differentiable_const c, fun _ => ?_, fun _ => ?_⟩
    · have ha : cexp (2 * π * I * (a : ℂ)) = 1 := by
        simpa [mul_comm] using Complex.exp_int_mul_two_pi_mul_I a
      simp [ha]
    · have hb : cexp (2 * π * I * (b : ℂ)) = 1 := by
        simpa [mul_comm] using Complex.exp_int_mul_two_pi_mul_I b
      simp [hb]

/-- At level `k = 0` with `τ.im ≠ 0`, non-trivial flat characteristics (`α ∉ ℤ` or `β ∉ ℤ`) admit
no nonzero holomorphic theta sections. -/
theorem thetaSections_zero_eq_bot_of_not_int {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (h : ¬ ((∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β))) :
    thetaSections 0 τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α) (mem_thetaSections_iff.mp hs).left
    fun m => ?_
  by_contra hm
  obtain ⟨hma, hb⟩ := thetaFourierCoeff_zero_level_eq_zero_of_ne hτ hs hm
  exact h ⟨⟨-m, by push_cast; linarith⟩, hb⟩

open scoped Classical in
/-- **Complete dimension formula at level `k = 0`.** For any non-real period `τ` (`τ.im ≠ 0`), the
space `thetaSections 0 τ α β` has dimension `1` when both characteristics are integers (the
trivial flat line bundle) and dimension `0` otherwise. -/
theorem finrank_thetaSections_zero (τ : ℂ) (hτ : τ.im ≠ 0) (α β : ℝ) :
    Module.finrank ℂ (thetaSections 0 τ α β) =
      if (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β) then 1 else 0 := by
  by_cases h : (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β)
  · rw [ite_eq_left h]
    have h1 : (fun _ : ℂ => (1 : ℂ)) ∈ thetaSections 0 τ α β :=
      (mem_thetaSections_zero_iff_const hτ h.left h.right).mpr ⟨1, rfl⟩
    refine finrank_eq_one ⟨fun _ => 1, h1⟩ ?_ fun s => ?_
    · intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      exact one_ne_zero this
    · obtain ⟨c, hc⟩ := (mem_thetaSections_zero_iff_const hτ h.left h.right).mp s.property
      refine ⟨c, Subtype.ext ?_⟩
      ext z
      simp [hc]
  · rw [ite_eq_right h, thetaSections_zero_eq_bot_of_not_int hτ h, finrank_bot]

end TauCeti
