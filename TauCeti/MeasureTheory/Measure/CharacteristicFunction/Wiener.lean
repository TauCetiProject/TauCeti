/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Wiener's lemma and atomic-mass inversion for characteristic functions

For a finite Borel measure `σ` on `ℝ`, the Cesàro time averages of its characteristic function
`charFun σ t = ∫ ξ, exp (t * ξ * I) ∂σ` twisted by `exp (-ω * t * I)` recover the point mass
`σ.real {ω}` at any frequency `ω : ℝ`:

`(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) * charFun σ t → (σ.real {ω} : ℂ)` as `T → ∞`.

Applying this inversion at `ω = 0` to the difference convolution `μ ∗ ν.map (-·)` yields the
bilinear Wiener identity for two finite Borel measures `μ` and `ν`, and setting `μ = ν` gives
Wiener's lemma on the real line:

`T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2 → ∑' ξ : ℝ, σ.real {ξ} ^ 2` as `T → ∞`.

In particular, the mean-square time average of `charFun σ` vanishes if and only if `σ` assigns zero
mass to every singleton.

## Main results

* `MeasureTheory.tendsto_average_exp_mul_charFun`: recovery of the point mass `σ.real {ω}` from
  twisted time averages of `charFun σ`.
* `MeasureTheory.tendsto_average_charFun_mul_conj`: bilinear Wiener lemma for two finite Borel
  measures on `ℝ`.
* `MeasureTheory.tendsto_average_norm_charFun_sq`: **Wiener's lemma** on `ℝ`.
* `MeasureTheory.tendsto_average_norm_charFun_sq_zero_iff`: vanishing of the mean-square average
  of `charFun σ` if and only if every singleton is `σ`-null.

## References

* N. Wiener, *The Fourier Integral and Certain of Its Applications*, Cambridge University Press
  (1933).
* Y. Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University Press
  (2004), Section I.7.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate Topology

namespace MeasureTheory

/-- Fubini swap turning a twisted time average of `charFun σ` over `[0, T]` (`T > 0`) into the
`σ`-integral of the exponential averaging kernel at shifted frequencies `ξ - ω`. -/
private theorem average_exp_mul_charFun_eq_integral (σ : Measure ℝ) [IsFiniteMeasure σ] (ω : ℝ)
    {T : ℝ} (hT : 0 < T) :
    (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t =
      ∫ ξ, ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)) ∂σ := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) T)) := ⟨by simp [Real.volume_Ioc]⟩
  have hint : Integrable
      (fun p : ℝ × ℝ ↦ Complex.exp ((p.1 : ℂ) * ((p.2 - ω : ℝ) : ℂ) * Complex.I))
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod σ) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun p ↦ ?_)
    rw [Complex.norm_exp]
    simp
  calc (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t
      = (T⁻¹ : ℂ) * ∫ t in Set.Ioc (0 : ℝ) T,
          (∫ ξ, Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I) ∂σ) := by
        rw [intervalIntegral.integral_of_le hT.le]
        congr 2 with t
        rw [charFun_apply_real, ← integral_const_mul]
        congr 1 with ξ
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = (T⁻¹ : ℂ) * ∫ ξ, (∫ t in Set.Ioc (0 : ℝ) T,
          Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)) ∂σ := by
        rw [integral_integral_swap hint]
    _ = ∫ ξ, ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
          Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)) ∂σ := by
        rw [← integral_const_mul]
        congr 1 with ξ
        rw [intervalIntegral.integral_of_le hT.le]

/-- **Atomic-mass inversion for characteristic functions.** For a finite Borel measure `σ` on `ℝ`
and any frequency `ω : ℝ`, the twisted time averages
`(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) * charFun σ t` converge to `(σ.real {ω} : ℂ)`
as `T → ∞`. -/
theorem tendsto_average_exp_mul_charFun (σ : Measure ℝ) [IsFiniteMeasure σ] (ω : ℝ) :
    Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t)
      atTop (𝓝 (σ.real {ω} : ℂ)) := by
  let K : ℝ → ℝ → ℂ := fun T ξ ↦
    (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I)
  have hmeas : ∀ᶠ T : ℝ in atTop, AEStronglyMeasurable (K T) σ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) T)) := ⟨by simp [Real.volume_Ioc]⟩
    have hcont : Continuous fun p : ℝ × ℝ ↦
        Complex.exp ((p.1 : ℂ) * ((p.2 - ω : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hK : K T = fun ξ : ℝ ↦ (T⁻¹ : ℂ) *
        ∫ t in Set.Ioc (0 : ℝ) T, Complex.exp ((t : ℂ) * ((ξ - ω : ℝ) : ℂ) * Complex.I) := by
      funext ξ
      simp only [K, intervalIntegral.integral_of_le hT.le]
    rw [hK]
    exact (stronglyMeasurable_const.mul
      hcont.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ ξ ∂σ, ‖K T ξ‖ ≤ 1 :=
    Eventually.of_forall fun T ↦ Eventually.of_forall fun ξ ↦
      TauCeti.norm_inv_mul_integral_cexp_mul_I_le_one (ξ - ω) T
  have hlim : ∀ᵐ ξ ∂σ, Tendsto (fun T : ℝ ↦ K T ξ) atTop
      (𝓝 (({ω} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) ξ)) :=
    Eventually.of_forall fun ξ ↦ by
      have h := TauCeti.tendsto_inv_mul_integral_cexp_mul_I (ξ - ω)
      have heq : (if ξ - ω = 0 then (1 : ℂ) else 0) =
          ({ω} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) ξ := by
        by_cases hξω : ξ = ω
        · simp [hξω]
        · simp [hξω, sub_ne_zero.mpr hξω]
      rwa [heq] at h
  have htend := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    hmeas hbound (integrable_const (1 : ℝ)) hlim
  have hind : ∫ ξ, ({ω} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) ξ ∂σ = (σ.real {ω} : ℂ) := by
    rw [integral_indicator_const _ (measurableSet_singleton ω), Complex.real_smul, mul_one]
  rw [hind] at htend
  refine htend.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (average_exp_mul_charFun_eq_integral σ ω hT).symm

/-- **Bilinear Wiener lemma on `ℝ`.** For finite Borel measures `μ` and `ν` on `ℝ`, the time
averages `(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, charFun μ t * conj (charFun ν t)` converge to the
common-atom sum `∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ}` as `T → ∞`. -/
theorem tendsto_average_charFun_mul_conj (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, charFun μ t * conj (charFun ν t))
      atTop (𝓝 ((∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ} : ℝ) : ℂ)) := by
  let νneg : Measure ℝ := ν.map fun x : ℝ ↦ -x
  let τ : Measure ℝ := μ ∗ νneg
  have hchar : ∀ t : ℝ, charFun τ t = charFun μ t * conj (charFun ν t) := fun t ↦ by
    rw [charFun_conv, ← charFun_neg]
    congr 1
    have hneg : (fun x : ℝ ↦ -x) = ((-1 : ℝ) * ·) := by
      funext x
      ring
    have hν : νneg = ν.map ((-1 : ℝ) * ·) := congrArg (ν.map ·) hneg
    rw [hν, charFun_map_mul, neg_one_mul]
  have hτ_eq : τ = (μ.prod ν).map fun p : ℝ × ℝ ↦ p.1 - p.2 := by
    dsimp only [τ, νneg]
    rw [Measure.conv, ← Measure.map_id (μ := μ),
      Measure.map_prod_map _ _ measurable_id measurable_neg,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1 with p
    simp
  have hmass : τ.real {0} = ∑' ξ : ℝ, μ.real {ξ} * ν.real {ξ} := by
    rw [hτ_eq, map_measureReal_apply (by fun_prop) (measurableSet_singleton 0)]
    have hpre : (fun p : ℝ × ℝ ↦ p.1 - p.2) ⁻¹' {0} = Set.diagonal ℝ := by
      ext ⟨x, y⟩
      simp [sub_eq_zero]
    rw [hpre, Measure.prod_real_diagonal]
  simpa [hchar, hmass] using tendsto_average_exp_mul_charFun τ 0

/-- **Wiener's lemma on `ℝ`.** For a finite Borel measure `σ` on `ℝ`, the mean-square time averages
`T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2` converge as `T → ∞` to the sum
`∑' ξ : ℝ, σ.real {ξ} ^ 2` of the squared masses of its atoms. -/
theorem tendsto_average_norm_charFun_sq (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2)
      atTop (𝓝 (∑' ξ : ℝ, σ.real {ξ} ^ 2)) := by
  have h := (Complex.continuous_re.continuousAt.tendsto).comp
    (tendsto_average_charFun_mul_conj σ σ)
  have hterm (t : ℝ) : charFun σ t * conj (charFun σ t) = ((‖charFun σ t‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hfun : (fun T : ℝ ↦
      ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, charFun σ t * conj (charFun σ t)).re) =
      fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2 := by
    funext T
    simp_rw [hterm, intervalIntegral.integral_ofReal]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Function.comp_def, hfun, Complex.ofReal_re] at h
  simpa only [sq] using h

/-- For a finite Borel measure `σ` on `ℝ`, the mean-square time averages of `charFun σ` vanish as
`T → ∞` if and only if `σ` assigns zero mass to every singleton. -/
theorem tendsto_average_norm_charFun_sq_zero_iff (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2) atTop (𝓝 0) ↔
      ∀ ξ : ℝ, σ {ξ} = 0 := by
  have hsum : Summable fun ξ : ℝ ↦ σ.real {ξ} ^ 2 := by
    simpa only [sq] using (Measure.hasSum_prod_real_diagonal σ σ).summable
  constructor
  · intro h0 ξ
    have htsum : ∑' x : ℝ, σ.real {x} ^ 2 = 0 :=
      tendsto_nhds_unique (tendsto_average_norm_charFun_sq σ) h0
    have hle : σ.real {ξ} ^ 2 ≤ 0 :=
      (hsum.le_tsum ξ fun _ _ ↦ sq_nonneg _).trans_eq htsum
    have hreal : σ.real {ξ} = 0 := sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
    exact (measureReal_eq_zero_iff (measure_ne_top σ _)).mp hreal
  · intro hnull
    have htsum : ∑' ξ : ℝ, σ.real {ξ} ^ 2 = 0 := by
      simp [measureReal_def, hnull]
    simpa only [htsum] using tendsto_average_norm_charFun_sq σ

end MeasureTheory

end
