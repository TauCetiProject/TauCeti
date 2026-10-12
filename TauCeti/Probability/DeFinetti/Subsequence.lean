/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.Theorem
import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
import TauCeti.Probability.Exchangeability.ConditionallyIID.Implications
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding

/-!
# Recovering a directing measure from an infinite subsequence

Every infinite injective selection from a conditionally i.i.d. family determines its directing
measure almost surely. More precisely, the directing measure is almost surely a measurable
function of the selected path. This lets an infinite hidden part of an exchangeable family
supply the directing measure for the whole family, including its visible coordinates.

We apply de Finetti on the selected path space and use uniqueness of the joint law of a directing
measure and its process. This works for finite base measures and a.e.-measurable coordinates,
without a standard Borel assumption on the sample space.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, §1.1.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [StandardBorelSpace α] [Nonempty α]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → α}
  {ν : Ω → ProbabilityMeasure α}

/-- A directing measure is almost surely a measurable function of any infinite injective
selection of the process. The selection need not preserve an order, and the original family may
have an arbitrary index type. -/
theorem ConditionallyIIDWith.exists_measurable_directing_eq_comp
    (h : ConditionallyIIDWith μ X ν) {k : ℕ → ι} (hk : Function.Injective k) :
    ∃ F : (ℕ → α) → ProbabilityMeasure α, Measurable F ∧
      ν =ᵐ[μ] fun ω ↦ F (fun n ↦ X (k n) ω) := by
  let Y := fun n ↦ X (k n)
  have hY : ConditionallyIIDWith μ Y ν := h.comp_injective hk
  have : IsFiniteMeasure (pathLaw μ Y) := by rw [pathLaw_def]; infer_instance
  obtain ⟨F, hF⟩ := (conditionallyIID_of_contractable
    ((ConditionallyIID.of_directing hY).contractable.coordinate_pathLaw hY.aemeasurable)
    (fun n ↦ (measurable_pi_apply n).aemeasurable)).exists_directing
  refine ⟨F, hF.measurable_directing, ?_⟩
  have hjoint := hY.jointPathLaw_eq_of_pathLaw_eq hF (pathLaw_coord _).symm
  have hid : IdentDistrib (fun ω ↦ (ν ω, fun n ↦ Y n ω))
      (fun p ↦ (F p, p)) μ (pathLaw μ Y) :=
    ⟨h.measurable_directing.aemeasurable.prodMk (AEMeasurable.of_eval hY.aemeasurable),
      (hF.measurable_directing.prodMk measurable_id).aemeasurable,
      by simpa only [jointPathLaw_def] using hjoint⟩
  -- Probability measures have a measurable injective evaluation code; no topology on their
  -- Giry measurable space is needed to transfer the graph event across the joint-law identity.
  have hcode := TauCeti.MeasureTheory.measurable_probabilityMeasureCode (α := α)
  have heq := hid.symm.ae_snd
    (measurableSet_eq_fun (hcode.comp measurable_fst)
      (hcode.comp (hF.measurable_directing.comp measurable_snd)))
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  exact heq.mono fun _ hω ↦ TauCeti.MeasureTheory.probabilityMeasureCode_injective hω

end TauCeti.Probability
