/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import Mathlib.Probability.Kernel.CondDistrib
import TauCeti.MeasureTheory.Measure.GiryMonad
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
    rw [h.jointLaw_eq_disintegration k hk, Measure.compProd_eq_comp_prod,
      TauCeti.MeasureTheory.bind_map h.measurable_directing.aemeasurable
        (Kernel.id ×ₖ K).measurable.aemeasurable]
    congr 1
    funext ω
    simp [K, Kernel.prod_apply, Kernel.id_apply, TauCeti.MeasureTheory.iidBlockKernel_apply]
  have hblock : AEMeasurable (fun ω => fun i : Fin m => X (k i) ω) μ :=
    AEMeasurable.of_eval fun i => h.aemeasurable (k i)
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd
    h.measurable_directing.aemeasurable hblock hK
  filter_upwards [hcond] with P hP
  simpa only [K, TauCeti.MeasureTheory.iidBlockKernel_apply] using hP

end TauCeti.Probability
