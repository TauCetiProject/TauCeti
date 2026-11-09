/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Progressive time integrals

Time integration of a strongly progressive process remains strongly progressive on the
original filtration. This applies to signed and Banach-valued drift integrals, without
integrability in the sample variable or usual conditions on the filtration.

The integral is the ordinary Bochner integral, including its zero value for nonintegrable
sections. Path regularity requires pathwise integrability; measurability alone makes no
continuity assertion.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, for progressive measurability.
-/

public section

open Set MeasureTheory

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Filtration ι ‹MeasurableSpace Ω›} {H : ι → Ω → E}

/-- Integrating a strongly progressive process over `(a,t]` preserves strong progressivity.
No pathwise or expected integrability is required for this measurability assertion. -/
theorem IsStronglyProgressive.integral_Ioc (hH : IsStronglyProgressive F H)
    (μ : Measure ι) [SFinite μ] (a : ι) :
    IsStronglyProgressive F (fun t ω => ∫ s in Ioc a t, H s ω ∂μ) := by
  intro T
  let : MeasurableSpace Ω := F T
  let G : (Iic T × Ω) × ι → E := fun p =>
    (Ioc a (p.1.1 : ι)).indicator (fun s => H (min s T) p.1.2) p.2
  have hG : StronglyMeasurable G := by
    have hinput : Measurable (fun p : (Iic T × Ω) × ι =>
        (⟨min p.2 T, min_le_right _ _⟩, p.1.2) : (Iic T × Ω) × ι → Iic T × Ω) :=
      ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst.snd
    exact ((hH T).comp_measurable hinput).indicator
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.fst.subtype_val))
  have h := hG.integral_prod_right' (ν := μ)
  convert h using 1
  ext p
  dsimp only
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hs : s ∈ Ioc a (p.1 : ι)
  · simp only [G, indicator_of_mem hs, min_eq_left (hs.2.trans p.1.prop)]
  · simp only [G, indicator_of_notMem hs]

end MeasureTheory
