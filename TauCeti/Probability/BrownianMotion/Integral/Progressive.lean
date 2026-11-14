/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.TimeAverage
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
      (∫⁻ t in Ioc 0 (n : ℝ), ‖H t.toNNReal ω‖ₑ ^ 2) < ∞) :
    ∃ G : ℝ≥0 → Ω → ℝ, TauCeti.LocallyBrownianIntegrable ℱ P G ∧
      ∀ ω, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        G t.toNNReal ω = H t.toNNReal ω := by
  obtain ⟨G, hG, heq⟩ := hH.exists_isStronglyPredictable_ae_time
  refine ⟨G, TauCeti.locallyBrownianIntegrable_iff_nat.2 ⟨hG, fun n ↦ ?_⟩, heq⟩
  -- Inclusion of nonnegative time preserves the finite-horizon Lebesgue measure.
  have hcoe : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ))
      (volume.restrict (Ioc 0 (n : ℝ))) := by
    refine ⟨measurable_coe_nnreal_real, ?_⟩
    rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.map_comap, NNReal.range_coe,
      Measure.restrict_restrict measurableSet_Ici,
      inter_eq_right.mpr (fun (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) (n : ℝ)) ↦ ht.1.le)]
  filter_upwards [henergy n] with ω hω
  -- Cap at n solely to make the real-time section literally measurable everywhere.
  have hm : StronglyMeasurable (fun t : ℝ ↦ G (min t.toNNReal n) ω) :=
    (hG.isStronglyProgressive n).comp_measurable
      ((measurable_real_toNNReal.min measurable_const).subtype_mk
        (h := fun _ ↦ min_le_right _ _) |>.prodMk measurable_const)
  have hcap : (fun t : ℝ ↦ G (min t.toNNReal n) ω) =ᵐ[
      volume.restrict (Ioc 0 (n : ℝ))] (fun t ↦ G t.toNNReal ω) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [min_eq_left (by simpa using Real.toNNReal_le_toNNReal ht.2)]
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ G t.toNNReal ω)
      (volume.restrict (Ioc 0 (n : ℝ))) := hm.aestronglyMeasurable.congr hcap
  have heq' : (fun t : ℝ ↦ G t.toNNReal ω) =ᵐ[
      volume.restrict (Ioc 0 (n : ℝ))] (fun t ↦ H t.toNNReal ω) :=
    (heq ω).filter_mono (ae_mono (Measure.restrict_mono_set volume Ioc_subset_Ioi_self))
  have hfinite : (∫⁻ t in Ioc 0 (n : ℝ), ‖G t.toNNReal ω‖ₑ ^ 2) < ∞ := by
    simpa only [Function.comp_apply] using
      (lintegral_congr_ae (heq'.fun_comp (fun x : ℝ ↦ ‖x‖ₑ ^ 2))).trans_lt hω
  have hLp := hmeas.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr hfinite
  simpa only [Function.comp_def, Real.toNNReal_coe] using hLp.comp_measurePreserving hcoe

end MeasureTheory.IsStronglyProgressive
