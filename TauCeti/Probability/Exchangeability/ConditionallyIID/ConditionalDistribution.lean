/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import Mathlib.Probability.Kernel.CondDistrib
import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Conditional laws of blocks in a conditionally i.i.d. family

Given a directing measure, the conditional law of any finite selection of distinct coordinates
is its finite product. This reads the joint disintegration in `ConditionallyIIDWith` as a regular
conditional distribution. It is the block form needed when conditional independence is applied to
the visible entries of an exchangeable array.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The conditional law of a finite block of distinct coordinates, given the directing measure,
is the product of that measure. The equality holds for almost every directing-measure value. -/
theorem ConditionallyIIDWith.condDistrib_block_ae_eq_pi [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure (μ : Measure Ω)]
    {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) {m : ℕ} (k : Fin m → ι) (hk : Function.Injective k) :
    ∀ᵐ P ∂μ.map ν,
      condDistrib (fun ω => fun i : Fin m => X (k i) ω) ν μ P =
        (ProbabilityMeasure.pi fun _ : Fin m => P).toMeasure := by
  let K : Kernel (ProbabilityMeasure α) (Fin m → α) :=
    TauCeti.MeasureTheory.iidBlockKernel m
  have hK : μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) = μ.map ν ⊗ₘ K := by
    apply Measure.ext_prod
    intro S B hS hB
    rw [h.jointLaw_eq_disintegration k hk, Measure.compProd_apply_prod hS hB]
    rw [Measure.bind_apply (MeasurableSet.prod hS hB)]
    · simp only [Measure.prod_prod, Measure.dirac_apply' _ hS]
      rw [← lintegral_indicator hS]
      have hf : Measurable fun P : ProbabilityMeasure α =>
          S.indicator (fun P => K P B) P :=
        (K.measurable_coe hB).indicator hS
      rw [lintegral_map hf h.measurable_directing]
      apply lintegral_congr
      intro ω
      by_cases hSω : ν ω ∈ S
      · simp [Set.indicator, hSω, K]
      · simp [Set.indicator, hSω]
    · exact (TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure
        ν h.measurable_directing).aemeasurable
  have hblock : AEMeasurable (fun ω => fun i : Fin m => X (k i) ω) μ :=
    AEMeasurable.of_eval fun i => h.aemeasurable (k i)
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd
    h.measurable_directing.aemeasurable hblock hK
  filter_upwards [hcond] with P hP
  simpa only [K, TauCeti.MeasureTheory.iidBlockKernel_apply] using hP

end TauCeti.Probability
