/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Progressive time integrals

Time integration of a strongly progressive process remains strongly progressive on the
original filtration. The integrating measure may depend on the sample, provided its restriction
to each time horizon is an s-finite kernel measurable at that horizon. This applies to signed
and Banach-valued drift integrals, without integrability in the sample variable or usual
conditions on the filtration.

The integral is the ordinary Bochner integral, including its zero value for nonintegrable
sections. Path regularity requires pathwise integrability; measurability alone makes no
continuity assertion.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, for progressive measurability.
-/

public section

open Set MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι]
  [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Filtration ι ‹MeasurableSpace Ω›} {H : ι → Ω → E}

/-- Integration over `(a,t]` against a sample-dependent measure preserves strong
progressivity if each finite-horizon restriction is an s-finite kernel measurable at that
horizon. No pathwise or expected integrability is required. -/
theorem IsStronglyProgressive.integral_Ioc_kernel (hH : IsStronglyProgressive F H)
    (μ : Ω → Measure ι) (a : ι)
    (hμ : ∀ T, Measurable[F T] fun ω ↦ (μ ω).restrict (Ioc a T))
    (hκ : ∀ T, letI : MeasurableSpace Ω := F T
      IsSFiniteKernel (⟨fun ω ↦ (μ ω).restrict (Ioc a T), hμ T⟩ : Kernel Ω ι)) :
    IsStronglyProgressive F (fun t ω ↦ ∫ s in Ioc a t, H s ω ∂μ ω) := by
  intro T
  let : MeasurableSpace Ω := F T
  let κ : Kernel Ω ι := ⟨fun ω ↦ (μ ω).restrict (Ioc a T), hμ T⟩
  have : IsSFiniteKernel κ := hκ T
  let η : Kernel (Iic T × Ω) ι := κ.prodMkLeft (Iic T)
  have hG : StronglyMeasurable (fun p : (Iic T × Ω) × ι ↦
      (Iic (p.1.1 : ι)).indicator (fun s ↦ H (min s T) p.1.2) p.2) := by
    have hinput : Measurable (fun p : (Iic T × Ω) × ι ↦
        (⟨min p.2 T, min_le_right _ _⟩, p.1.2) : (Iic T × Ω) × ι → Iic T × Ω) :=
      ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst.snd
    exact ((hH T).comp_measurable hinput).indicator
      (measurableSet_le measurable_snd measurable_fst.fst.subtype_val)
  have hm := hG.integral_kernel_prod_right' (κ := η)
  convert hm using 1
  ext p
  simp only [η, Kernel.prodMkLeft_apply, κ, Kernel.coe_mk]
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioc_of_le p.1.prop]
  exact setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
    rw [min_eq_left (hs.2.trans p.1.prop)]

/-- Integrating a strongly progressive process over `(a,t]` preserves strong progressivity.
No pathwise or expected integrability is required for this measurability assertion. -/
theorem IsStronglyProgressive.integral_Ioc (hH : IsStronglyProgressive F H)
    (μ : Measure ι) [SFinite μ] (a : ι) :
    IsStronglyProgressive F (fun t ω => ∫ s in Ioc a t, H s ω ∂μ) :=
  hH.integral_Ioc_kernel (fun _ ↦ μ) a (fun _ ↦ measurable_const)
    (fun _ ↦ Kernel.const.instIsSFiniteKernel)

end MeasureTheory
