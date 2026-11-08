/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Brownian motion and its compensated square as martingales

For a real pre-Brownian motion relative to a filtration, both `B` and `B² - t` are
martingales on that filtration. The compensated square has every finite `Lᵖ` moment, even
without a filtration. The conditional second moment of an increment is its elapsed time, and
`E[B_t² | F_s] = B_s² + (t - s)` for `s ≤ t`.

These identities are the elementary square decomposition behind Brownian quadratic variation.
Only finite-dimensional Brownian laws, adaptation and independence from the filtration's past
are used: path continuity and usual conditions on the filtration are not required. In
particular, the results do not infer independence from Brownian marginal laws alone.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The compensated Brownian square has every finite `Lᵖ` moment. -/
theorem memLp_sq_sub (hB : IsPreBrownianReal B P) (t : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun ω => B t ω ^ 2 - (t : ℝ)) p P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h := (hB.hasLaw_eval t).memLp (memLp_id_gaussianReal' (p * 2) (by finiteness))
  have hsquare : MemLp (fun ω => B t ω ^ 2) p P := by
    simpa [ENNReal.mul_div_cancel_right, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      h.norm_rpow_div 2
  exact hsquare.sub (memLp_const (t : ℝ))

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0}

/-- A future Brownian increment has conditional mean zero given the past. -/
theorem condExp_sub (hB : IsFilteredPreBrownianReal ℱ B P) (hst : s ≤ t) :
    P[B t - B s | ℱ s] =ᵐ[P] fun _ => 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h := condExp_indep_eq
    (hB.adapted.measurable.sub hB.adapted.measurable).comap_le (ℱ.le s)
    (comap_measurable (B t - B s)).stronglyMeasurable (hB.indep_sub hst)
  simpa only [Pi.sub_apply, integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
    hB.integral_eval, sub_self] using h

/-- A future Brownian increment has conditional second moment equal to its elapsed time. -/
theorem condExp_sq_sub (hB : IsFilteredPreBrownianReal ℱ B P) (hst : s ≤ t) :
    P[fun ω => (B t ω - B s ω) ^ 2 | ℱ s] =ᵐ[P] fun _ => (t : ℝ) - s := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h := condExp_indep_eq
    (hB.adapted.measurable.sub hB.adapted.measurable).comap_le (ℱ.le s)
    ((comap_measurable (B t - B s)).pow_const 2).stronglyMeasurable (hB.indep_sub hst)
  have hi : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - s := by
    calc
      _ = ∫ x, x ^ 2 ∂gaussianReal 0 (t - s) := by
        simpa only [Function.comp_apply, Pi.sub_apply] using
          (hB.hasLaw_sub_of_le hst).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
      _ = _ := by simp [integral_sq_gaussianReal, NNReal.coe_sub hst]
  simpa only [Pi.sub_apply, hi] using h

/-- A real Brownian motion relative to a filtration is a martingale on that filtration. -/
theorem martingale (hB : IsFilteredPreBrownianReal ℱ B P) : Martingale B ℱ P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨hB.adapted.stronglyAdapted, fun s t hst => ?_⟩
  have hsub := condExp_sub (s := s) (t := t) hB hst
  have hlin := MeasureTheory.condExp_sub (m := ℱ s) (hB.integrable_eval t) (hB.integrable_eval s)
  filter_upwards [hsub, hlin] with ω hzero hdiff
  rw [condExp_of_stronglyMeasurable (ℱ.le s) (hB.adapted s).stronglyMeasurable
    (hB.integrable_eval s)] at hdiff
  simp only [Pi.sub_apply] at hdiff
  linarith

/-- The conditional second moment of Brownian motion is its current square plus elapsed time. -/
theorem condExp_sq (hB : IsFilteredPreBrownianReal ℱ B P) (hst : s ≤ t) :
    P[fun ω => B t ω ^ 2 | ℱ s] =ᵐ[P] fun ω => B s ω ^ 2 + ((t : ℝ) - s) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let D := B t - B s
  have hD : MemLp D 2 P := (hB.hasLaw_sub_of_le hst).memLp
    (memLp_id_gaussianReal' 2 (by simp))
  have hS : MemLp (B s) 2 P := (hB.hasLaw_eval s).memLp
    (memLp_id_gaussianReal' 2 (by simp))
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ s)
    (hB.adapted s).stronglyMeasurable (hS.integrable_mul hD) (hD.integrable (by norm_num))
  have hcross : P[B s * D | ℱ s] =ᵐ[P] fun _ => 0 := by
    filter_upwards [hpull, hB.condExp_sub hst] with ω hp hz
    rw [hp, Pi.mul_apply, hz, mul_zero]
  have heq : (fun ω => B t ω ^ 2) =
      (fun ω => B s ω ^ 2) + (2 : ℝ) • (B s * D) + (fun ω => D ω ^ 2) := by
    ext ω
    simp only [D, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hsum := condExp_add (m := ℱ s)
    (hS.integrable_sq.add ((hS.integrable_mul hD).const_mul 2)) hD.integrable_sq
  have hsum' := condExp_add (m := ℱ s) hS.integrable_sq
    ((hS.integrable_mul hD).const_mul 2)
  have hscale := condExp_smul (μ := P) (2 : ℝ) (B s * D) (ℱ s)
  simp only [Pi.add_def, Pi.smul_def, Pi.mul_def, smul_eq_mul] at heq hsum hsum' hscale hcross
  rw [heq]
  filter_upwards [hsum, hsum', hscale, hcross, hB.condExp_sq_sub hst]
    with ω h₁ h₂ h₃ hcross' hsquare
  rw [h₁, h₂, h₃, hcross', mul_zero, add_zero,
    condExp_of_stronglyMeasurable (ℱ.le s)
      ((hB.adapted s).pow_const 2).stronglyMeasurable hS.integrable_sq]
  exact congrArg (B s ω ^ 2 + ·) hsquare

/-- The compensated Brownian square `B_t² - t` is a martingale. -/
theorem martingale_sq_sub (hB : IsFilteredPreBrownianReal ℱ B P) :
    Martingale (fun t ω => B t ω ^ 2 - (t : ℝ)) ℱ P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => ((hB.adapted t).pow_const 2 |>.sub measurable_const).stronglyMeasurable,
    fun s t hst => ?_⟩
  have hi := ((hB.hasLaw_eval t).memLp (memLp_id_gaussianReal' 2 (by simp))).integrable_sq
  have hlin := MeasureTheory.condExp_sub (m := ℱ s) hi (integrable_const (t : ℝ))
  simp only [Pi.sub_def] at hlin
  filter_upwards [hlin, hB.condExp_sq hst] with ω h₁ h₂
  rw [h₁, condExp_const (ℱ.le s), h₂]
  ring

end TauCeti.Probability.IsFilteredPreBrownianReal
