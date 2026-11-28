/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.TimeAverage
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Probability.Process.Progressive
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Progressive inputs for local Brownian integration

A real progressive process with finite pathwise square energy on every finite horizon has
one predictable representative in `TauCeti.LocallyBrownianIntegrable`. This is the input
adapter needed to interpret progressive diffusion coefficients as stochastic integrands.
The hypothesis uses the nonnegative lower integral, so divergent energy is not mistaken
for the default zero value of a nonintegrable Bochner integral.

The representative agrees with the original at almost every positive time on every path.
This stronger pathwise statement preserves pathwise coefficient identities and time integrals,
but does not imply equality at each fixed time or indistinguishability. The domain conclusion
uses one sample-full event for all finite horizons. Neither sample moments nor completeness,
right continuity, or even s-finiteness of the sample measure is required.

The selection reuses
`MeasureTheory.IsStronglyProgressive.exists_isStronglyPredictable_ae_time`; this file supplies
the local square-energy domain, not a construction of the stochastic integral itself.
Both the energy hypothesis and the pathwise agreement use nonnegative time with pullback
Lebesgue measure. Under s-finiteness of the sample measure,
`MeasureTheory.IsStronglyProgressive.exists_locallyBrownianIntegrable_ae_prod` supplies one
locally Brownian-integrable representative agreeing product-a.e. across all finite horizons.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D and §5.6.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace MeasureTheory.IsStronglyProgressive

/-- A progressive real process with finite pathwise square energy admits a predictable
locally Brownian-integrable representative. The same representative works for all horizons
and agrees with the input at almost every positive time on every path, not just almost
surely in the sample variable. Finite energy is only required separately at each integer
horizon; the conclusion has a single sample-full event for all finite horizons. -/
theorem exists_locallyBrownianIntegrable_ae_time
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyProgressive ℱ H)
    (henergy : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫⁻ t, ‖H t ω‖ₑ ^ 2 ∂((volume.restrict (Ioc 0 (n : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ))) < ∞) :
    ∃ G : ℝ≥0 → Ω → ℝ, TauCeti.LocallyBrownianIntegrable ℱ P G ∧
      ∀ ω, (fun t ↦ G t ω) =ᵐ[TauCeti.nnvolume] (fun t ↦ H t ω) := by
  obtain ⟨G, hG, heq⟩ := hH.exists_isStronglyPredictable_ae_time
  have heq' (ω : Ω) : (fun t ↦ G t ω) =ᵐ[TauCeti.nnvolume] (fun t ↦ H t ω) := by
    have hcoe : MeasurePreserving ((↑) : ℝ≥0 → ℝ) TauCeti.nnvolume
        (volume.restrict (Ici (0 : ℝ))) :=
      ⟨measurable_coe_nnreal_real, TauCeti.map_coe_nnvolume⟩
    have hω := ae_restrict_of_ae_eq_of_ae_restrict Ioi_ae_eq_Ici (heq ω)
    filter_upwards [hcoe.quasiMeasurePreserving.ae hω] with t ht
    simpa only [Real.toNNReal_coe] using ht
  refine ⟨G, TauCeti.locallyBrownianIntegrable_iff_nat.2 ⟨hG, fun n ↦ ?_⟩, heq'⟩
  have hm : StronglyMeasurable (Function.uncurry G) := hG.mono ℱ.predictable_le_prod
  filter_upwards [henergy n] with ω hω
  have heqn : (fun t ↦ G t ω) =ᵐ[((volume.restrict (Ioc 0 (n : ℝ))).comap
      ((↑) : ℝ≥0 → ℝ))] (fun t ↦ H t ω) := by
    rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← TauCeti.nnvolume_def]
    exact ae_restrict_of_ae (heq' ω)
  have hfinite : (∫⁻ t, ‖G t ω‖ₑ ^ 2 ∂((volume.restrict (Ioc 0 (n : ℝ))).comap
      ((↑) : ℝ≥0 → ℝ))) < ∞ := by
    simpa only [Function.comp_apply] using
      (lintegral_congr_ae (heqn.fun_comp (fun x : ℝ ↦ ‖x‖ₑ ^ 2))).trans_lt hω
  exact (hm.of_uncurry_right (y := ω)).aestronglyMeasurable
    |>.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr hfinite

/-- A progressive real process with finite pathwise square energy has one locally
Brownian-integrable predictable representative agreeing product-a.e. on every finite
horizon. S-finiteness is needed only for this product-measure conclusion. -/
theorem exists_locallyBrownianIntegrable_ae_prod
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} [SFinite P] {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyProgressive ℱ H)
    (henergy : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫⁻ t, ‖H t ω‖ₑ ^ 2 ∂((volume.restrict (Ioc 0 (n : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ))) < ∞) :
    ∃ G : ℝ≥0 → Ω → ℝ, TauCeti.LocallyBrownianIntegrable ℱ P G ∧ ∀ T : ℝ≥0,
      Function.uncurry G =ᵐ[((volume.restrict (Ioc 0 (T : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ)).prod P] Function.uncurry H := by
  obtain ⟨G, hG, heq⟩ := hH.exists_locallyBrownianIntegrable_ae_time henergy
  refine ⟨G, hG, fun T ↦ ?_⟩
  rw [NNReal.comap_volume_restrict_Ioc, ← TauCeti.nnvolume_def]
  exact hG.isStronglyPredictable.isStronglyProgressive.isProgressive.ae_eq_prod_of_ae_eq
    hH.isProgressive (Eventually.of_forall fun ω ↦ ae_restrict_of_ae (heq ω))

end MeasureTheory.IsStronglyProgressive
