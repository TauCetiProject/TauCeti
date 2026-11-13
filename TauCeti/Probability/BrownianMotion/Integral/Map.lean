/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.Process.Predictable.Map
import TauCeti.Probability.Process.ElementaryDensity
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv

/-!
# Sample-space transport of the predictable L² Brownian integral

Pulling an integrand and its Brownian integrator back along a filtered measure-preserving
sample-space map commutes with the finite-horizon L² integral. This compares integrals
constructed on different probability spaces, including different ambient measurable spaces.
It is an equality of L² classes, not a claim about simultaneous-time representatives.

Brownian increment independence is required relative to both filtrations: measurability
of a sample map alone does not preserve Brownian motion in a larger source filtration.
The pullbacks are Mathlib's native `Lp.compMeasurePreservingₗᵢ`; no new integrand
carrier or integral is introduced. The comparison follows from the existing rectangle
formula and density, and includes zero horizons and arbitrary predictable L² classes.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2, for the predictable L² construction.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'} {ℱ : Filtration ℝ≥0 m} {𝒢 : Filtration ℝ≥0 m'}
  {W : ℝ≥0 → Ω' → ℝ} {f : Ω → Ω'}

/-- Predictable L² Brownian integration commutes with filtered measure-preserving
sample-space pullback. Brownian increment independence must hold in both filtrations;
no completeness, right continuity or path continuity is required. -/
theorem l2Integral_compMeasurePreserving
    (hW : IsFilteredPreBrownianReal 𝒢 W Q)
    (hB : IsFilteredPreBrownianReal ℱ (fun t ω ↦ W t (f ω)) P)
    (hf : MeasurePreserving f P Q) (hℱ : ∀ t, Measurable[ℱ t, 𝒢 t] f)
    (T : ℝ≥0) (H : Lp ℝ 2 (𝒢.predictableMeasure Q T)) :
    letI := hB.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    letI : MeasurableSpace (ℝ≥0 × Ω') := 𝒢.predictable
    hB.l2Integral T
        (Lp.compMeasurePreservingₗᵢ ℝ (Prod.map id f)
          (ℱ.measurePreserving_prodMap_predictableMeasure 𝒢 hf hℱ T) H) =
      Lp.compMeasurePreservingₗᵢ ℝ f hf (hW.l2Integral T H) := by
  let := hB.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : MeasurableSpace (ℝ≥0 × Ω') := 𝒢.predictable
  let hp := ℱ.measurePreserving_prodMap_predictableMeasure 𝒢 hf hℱ T
  have heq : (hB.l2Integral T).toContinuousLinearMap.comp
        (Lp.compMeasurePreservingₗᵢ ℝ (Prod.map id f) hp).toContinuousLinearMap =
      (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap.comp
        (hW.l2Integral T).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
    intro s t hst ht A hA
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      Lp.coe_compMeasurePreservingₗᵢ, Lp.indicatorConstLp_compMeasurePreserving]
    have hpre : (Prod.map id f) ⁻¹' (Ioc s t ×ˢ A) = Ioc s t ×ˢ (f ⁻¹' A) := by
      ext p
      simp
    simp only [hpre]
    apply Lp.ext
    have hright := (Lp.coeFn_compMeasurePreserving _ hf).trans
      (hf.quasiMeasurePreserving.ae_eq_comp
        (hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht hA 1))
    filter_upwards [hB.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le
      hst.le ht (hℱ s hA) 1, hright] with ω hleft hright
    rw [hleft, hright]
    by_cases hω : f ω ∈ A <;> simp [hω]
  exact congrArg (fun J : Lp ℝ 2 (𝒢.predictableMeasure Q T) →L[ℝ] Lp ℝ 2 P ↦ J H) heq

end TauCeti.Probability.IsFilteredPreBrownianReal
