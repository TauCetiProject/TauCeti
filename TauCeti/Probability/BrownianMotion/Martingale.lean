/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Filtered
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Martingale.Basic
import TauCeti.Probability.Martingale.Local.Dominated
import TauCeti.Probability.Martingale.MaximalInequality.Lp

/-!
# Brownian motion and its compensated square as martingales

For a real pre-Brownian motion relative to a filtration, both `B` and `B² - t` are
martingales on that filtration. The compensated square has every finite `Lᵖ` moment, even
without a filtration. The conditional second moment of an increment is its elapsed time, and
`E[B_t² | F_s] = B_s² + (t - s)` for `s ≤ t`. Moreover, any real Brownian motion that is adapted
to a filtration `ℱ` and is a native local martingale on `ℱ` is already a true `ℱ`-martingale
(`ProbabilityTheory.IsBrownianReal.martingale_of_locally_martingale`).

These identities are the elementary square decomposition behind Brownian quadratic variation.
Only finite-dimensional Brownian laws, adaptation and independence from the filtration's past
are used for the pre-Brownian results: path continuity and usual conditions on the filtration
are not required, and they do not infer independence from Brownian marginal laws alone.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Each Brownian marginal has every finite `Lᵖ` moment. -/
theorem memLp_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (B t) p P :=
  (hB.hasLaw_eval t).memLp (memLp_id_gaussianReal' p hp)

/-- The compensated Brownian square has every finite `Lᵖ` moment. -/
theorem memLp_sq_sub_time (hB : IsPreBrownianReal B P) (t : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun ω => B t ω ^ 2 - (t : ℝ)) p P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact (hB.memLp_pow_eval t 2 hp).sub (memLp_const (t : ℝ))

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0}

/-- A strongly measurable function of a future Brownian increment has conditional expectation
equal to its mean given the past. -/
theorem condExp_comp_sub_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hB : IsFilteredPreBrownianReal ℱ B P) (hst : s ≤ t)
    {f : ℝ → E} (hf : StronglyMeasurable f) :
    P[fun ω => f (B t ω - B s ω) | ℱ s] =ᵐ[P] fun _ => ∫ ω, f (B t ω - B s ω) ∂P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact condExp_indep_eq
    (hB.adapted.measurable.sub hB.adapted.measurable).comap_le (ℱ.le s)
    (hf.comp_measurable (comap_measurable (B t - B s))) (hB.indep_sub hst)

/-- A future Brownian increment has conditional mean zero given the past. -/
theorem condExp_sub (hB : IsFilteredPreBrownianReal ℱ B P) (hst : s ≤ t) :
    P[B t - B s | ℱ s] =ᵐ[P] fun _ => 0 := by
  have h := hB.condExp_comp_sub_eq_integral hst stronglyMeasurable_id
  simpa only [id_eq, Pi.sub_def, integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
    hB.integral_eval, sub_self] using h

/-- A future Brownian increment has conditional second moment equal to its elapsed time. -/
theorem condExp_sub_sq (hB : IsFilteredPreBrownianReal ℱ B P) (hst : s ≤ t) :
    P[fun ω => (B t ω - B s ω) ^ 2 | ℱ s] =ᵐ[P] fun _ => (t : ℝ) - s := by
  have h := hB.condExp_comp_sub_eq_integral hst (f := fun x : ℝ => x ^ 2) (by fun_prop)
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
  filter_upwards [hB.martingale.condExp_sq hst (hB.memLp_eval t (by simp)),
    hB.condExp_sub_sq hst] with ω h₁ h₂
  rw [h₁, h₂]

/-- The compensated Brownian square `B_t² - t` is a martingale. -/
theorem martingale_sq_sub (hB : IsFilteredPreBrownianReal ℱ B P) :
    Martingale (fun t ω => B t ω ^ 2 - (t : ℝ)) ℱ P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => ((hB.adapted t).pow_const 2 |>.sub measurable_const).stronglyMeasurable,
    fun s t hst => ?_⟩
  have hi := (hB.memLp_eval t (p := 2) (by simp)).integrable_sq
  have hlin := MeasureTheory.condExp_sub (m := ℱ s) hi (integrable_const (t : ℝ))
  simp only [Pi.sub_def] at hlin
  filter_upwards [hlin, hB.condExp_sq hst] with ω h₁ h₂
  rw [h₁, condExp_const (ℱ.le s), h₂]
  ring

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- A real Brownian motion that is adapted to a filtration `ℱ` and is a native local martingale on
`ℱ` is a true `ℱ`-martingale. -/
theorem martingale_of_locally_martingale (hB : IsBrownianReal B P) (hA : Adapted ℱ B)
    (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) : Martingale B ℱ P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hnat := hB.toIsPreBrownianReal.isFilteredPreBrownianReal_natural
    fun t ↦ (hA.stronglyAdapted t).mono (ℱ.le t)
  refine hA.stronglyAdapted.martingale_of_locally_martingale_of_dominated hloc fun T ↦ ?_
  have hrc : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ B u ω) (Set.Ioi t) t :=
    hB.cont.mono fun _ hω _ _ ↦ hω.continuousWithinAt
  refine ⟨fun ω ↦ (⨆ s ≤ T, ‖B s ω‖ₑ).toReal,
    (hnat.martingale.memLp_toReal_iSup_eNorm hrc (by norm_num) ENNReal.ofNat_ne_top
      (hB.memLp_eval T ENNReal.ofNat_ne_top)).integrable one_le_two, ?_⟩
  filter_upwards [hnat.martingale.ae_iSup_eNorm_lt_top hrc] with ω hfin s hs
  rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
  exact ENNReal.toReal_mono hfin.ne (le_iSup₂_of_le s hs le_rfl)

end ProbabilityTheory.IsBrownianReal
