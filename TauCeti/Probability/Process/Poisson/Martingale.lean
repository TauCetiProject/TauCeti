/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Filtered
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Martingale.Basic

/-!
# Compensated Poisson martingales

For a rate-`α` Poisson process relative to a filtration, the compensated count
`M t = N t - α * t` and its compensated square `M t ^ 2 - α * t` are martingales.
Both processes have every finite moment. The conditional mean and conditional square
of a compensated increment are zero and `α * (t - s)`, respectively.

These identities identify the deterministic compensator of a Poisson count and the
predictable bracket of its compensated martingale once path regularity is available.
They use independence from the
entire earlier sigma algebra, not just the Poisson marginal laws. No path regularity,
completeness or right continuity of the filtration is assumed. In particular the results
apply after ambient-null augmentation through `IsFilteredPoissonProcess.ambientNullAugmentation`.
The conditional square follows from the martingale identity
`MeasureTheory.Martingale.condExp_sq`, shared with
`TauCeti.Probability.IsFilteredPreBrownianReal.condExp_sq`, using centered Poisson increments.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Springer, 2005, Chapter I, §3.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0}

/-- The compensated Poisson count has every finite moment. -/
theorem memLp_compensated (hN : IsFilteredPoissonProcess ℱ α N P) (t p : ℝ≥0) :
    MemLp (fun ω ↦ N t ω - (α : ℝ) * t) p P := by
  have := hN.isProbabilityMeasure
  exact (hN.memLp_eval t p).sub (memLp_const _)

/-- The compensated square of the compensated Poisson count has every finite moment. -/
theorem memLp_compensated_sq_sub (hN : IsFilteredPoissonProcess ℱ α N P) (t p : ℝ≥0) :
    MemLp (fun ω ↦ (N t ω - (α : ℝ) * t) ^ 2 - (α : ℝ) * t) p P := by
  have := hN.isProbabilityMeasure
  have h := hN.memLp_compensated t (p * 2)
  have hsquare : MemLp (fun ω ↦ (N t ω - (α : ℝ) * t) ^ 2) p P := by
    simpa [ENNReal.mul_div_cancel_right, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      h.norm_rpow_div 2
  exact hsquare.sub (memLp_const _)

/-- The second moment of the compensated count equals the elapsed Poisson intensity. -/
theorem integral_compensated_sq (hN : IsFilteredPoissonProcess ℱ α N P) (t : ℝ≥0) :
    ∫ ω, (N t ω - (α : ℝ) * t) ^ 2 ∂P = (α : ℝ) * t := by
  simpa only [NNReal.coe_mul] using
    (hN.hasLaw_eval t).integral_sub_sq_map_cast_poissonMeasure

/-- The centered second moment of a Poisson increment equals its intensity. -/
theorem integral_sub_sub_mul_sq (hN : IsFilteredPoissonProcess ℱ α N P) (hst : s ≤ t) :
    ∫ ω, (N t ω - N s ω - (α : ℝ) * ((t : ℝ) - s)) ^ 2 ∂P =
      (α : ℝ) * ((t : ℝ) - s) := by
  simpa only [Pi.sub_apply, NNReal.coe_mul, NNReal.coe_sub hst] using
    (hN.hasLaw_sub hst).integral_sub_sq_map_cast_poissonMeasure

/-- A strongly measurable function of a future Poisson increment has conditional expectation
equal to its mean given the past. -/
theorem condExp_comp_sub_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hN : IsFilteredPoissonProcess ℱ α N P) (hst : s ≤ t)
    {f : ℝ → E} (hf : StronglyMeasurable f) :
    P[fun ω ↦ f (N t ω - N s ω) | ℱ s] =ᵐ[P] fun _ ↦ ∫ ω, f (N t ω - N s ω) ∂P := by
  have := hN.isProbabilityMeasure
  exact condExp_indep_eq (hN.measurable t |>.sub (hN.measurable s)).comap_le
    (ℱ.le s) (hf.comp_measurable (comap_measurable (N t - N s))) (hN.indep_sub hst)

/-- A future Poisson increment has conditional mean equal to its intensity given the past. -/
theorem condExp_sub (hN : IsFilteredPoissonProcess ℱ α N P) (hst : s ≤ t) :
    P[N t - N s | ℱ s] =ᵐ[P] fun _ ↦ (α : ℝ) * ((t : ℝ) - s) := by
  have h := hN.condExp_comp_sub_eq_integral hst stronglyMeasurable_id
  have hi : ∫ ω, N t ω - N s ω ∂P = (α : ℝ) * ((t : ℝ) - s) := by
    simpa only [Pi.sub_apply, NNReal.coe_mul, NNReal.coe_sub hst] using
      integral_of_hasLaw_map_cast_poissonMeasure (hN.hasLaw_sub hst)
  exact h.trans (Filter.Eventually.of_forall fun _ ↦ hi)

/-- A compensated Poisson increment has conditional second moment equal to its intensity. -/
theorem condExp_sub_sub_mul_sq (hN : IsFilteredPoissonProcess ℱ α N P) (hst : s ≤ t) :
    P[fun ω ↦ (N t ω - N s ω - (α : ℝ) * ((t : ℝ) - s)) ^ 2 | ℱ s] =ᵐ[P]
      fun _ ↦ (α : ℝ) * ((t : ℝ) - s) := by
  have h := hN.condExp_comp_sub_eq_integral hst
    (f := fun x : ℝ ↦ (x - (α : ℝ) * ((t : ℝ) - s)) ^ 2) (by fun_prop)
  exact h.trans (Filter.Eventually.of_forall fun _ ↦ hN.integral_sub_sub_mul_sq hst)

/-- The compensated Poisson process `N t - α * t` is a martingale. -/
theorem martingale_compensated (hN : IsFilteredPoissonProcess ℱ α N P) :
    Martingale (fun t ω ↦ N t ω - (α : ℝ) * t) ℱ P := by
  have := hN.isProbabilityMeasure
  refine ⟨fun t ↦ (hN.stronglyAdapted t).sub stronglyMeasurable_const, fun s t hst ↦ ?_⟩
  have hi (u : ℝ≥0) := (hN.memLp_eval u 1).integrable (by simp)
  have hdiff := MeasureTheory.condExp_sub (m := ℱ s) (hi t) (hi s)
  have hlin := MeasureTheory.condExp_sub (m := ℱ s) (hi t)
    (integrable_const ((α : ℝ) * t))
  simp only [Pi.sub_def] at hlin
  filter_upwards [hN.condExp_sub hst, hdiff, hlin] with ω hinc hdiff hlin
  rw [condExp_of_stronglyMeasurable (ℱ.le s) (hN.stronglyAdapted s) (hi s)] at hdiff
  rw [hlin, condExp_const (ℱ.le s)]
  simp only [Pi.sub_apply] at hdiff
  linarith

/-- A compensated Poisson increment has conditional mean zero given the past. -/
theorem condExp_sub_sub_mul (hN : IsFilteredPoissonProcess ℱ α N P) (hst : s ≤ t) :
    P[fun ω ↦ N t ω - N s ω - (α : ℝ) * ((t : ℝ) - s) | ℱ s] =ᵐ[P] fun _ ↦ 0 := by
  have := hN.isProbabilityMeasure
  have hi := ((hN.memLp_eval t 1).sub (hN.memLp_eval s 1)).integrable (by simp)
  have hlin := MeasureTheory.condExp_sub (m := ℱ s) hi
    (integrable_const ((α : ℝ) * ((t : ℝ) - s)))
  simp only [Pi.sub_def] at hlin
  filter_upwards [hlin, hN.condExp_sub hst] with ω hlin hinc
  simp only [Pi.sub_def] at hinc
  rw [hlin, condExp_const (ℱ.le s), hinc, sub_self]

/-- The conditional square of the compensated count is its current square plus the future
increment intensity. -/
theorem condExp_compensated_sq (hN : IsFilteredPoissonProcess ℱ α N P) (hst : s ≤ t) :
    P[fun ω ↦ (N t ω - (α : ℝ) * t) ^ 2 | ℱ s] =ᵐ[P]
      fun ω ↦ (N s ω - (α : ℝ) * s) ^ 2 + (α : ℝ) * ((t : ℝ) - s) := by
  have := hN.isProbabilityMeasure
  have hsq := hN.martingale_compensated.condExp_sq hst (hN.memLp_compensated t 2)
  have hinc : (fun ω ↦ (N t ω - (α : ℝ) * t - (N s ω - (α : ℝ) * s)) ^ 2) =
      fun ω ↦ (N t ω - N s ω - (α : ℝ) * ((t : ℝ) - s)) ^ 2 :=
    funext fun ω ↦ by ring
  simp only [hinc] at hsq
  filter_upwards [hsq, hN.condExp_sub_sub_mul_sq hst] with ω h₁ h₂
  rw [h₁, h₂]

/-- The compensated square `(N t - α * t)² - α * t` is a martingale. -/
theorem martingale_compensated_sq_sub (hN : IsFilteredPoissonProcess ℱ α N P) :
    Martingale (fun t ω ↦ (N t ω - (α : ℝ) * t) ^ 2 - (α : ℝ) * t) ℱ P := by
  have := hN.isProbabilityMeasure
  refine ⟨fun t ↦ ((hN.martingale_compensated.stronglyAdapted t).pow 2).sub
    stronglyMeasurable_const, fun s t hst ↦ ?_⟩
  have hi := (hN.memLp_compensated t 2).integrable_sq
  have hlin := MeasureTheory.condExp_sub (m := ℱ s) hi (integrable_const ((α : ℝ) * t))
  simp only [Pi.sub_def] at hlin
  filter_upwards [hlin, hN.condExp_compensated_sq hst] with ω h₁ h₂
  rw [h₁, condExp_const (ℱ.le s), h₂]
  ring

end TauCeti.Probability.IsFilteredPoissonProcess
