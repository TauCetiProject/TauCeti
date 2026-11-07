/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import TauCeti.Dynamics.Ergodic.MeasurePreserving

/-!
# Conditional expectations under measure-preserving maps

Pulling an observable back along a measure-preserving map commutes with conditional expectation,
provided the conditioning σ-algebra is pulled back as well. The map need not be invertible or
injective. In particular, adjoining an independent probability space preserves conditional
expectations of old observables given old information.

The results hold for Banach-valued observables, including finite vectors and matrices. Only the
measure trimmed to the conditioning σ-algebra needs to be sigma-finite. Nonintegrable observables
are covered using Mathlib's convention that their conditional expectation is zero.

The proof uses the characterization of conditional expectation by integrals over measurable
sets, as in Tao, *Topics in Random Matrix Theory* (2012), §1.1.
-/

public section

open MeasureTheory

namespace MeasureTheory.MeasurePreserving

variable {α β E : Type*} {m : MeasurableSpace β}
  [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} {g : α → β}

/-- Conditional expectation commutes with pullback along a measure-preserving map when the
conditioning σ-algebra is also pulled back. No injectivity or inverse for the map is required. -/
theorem condExp_comap (hg : MeasurePreserving g μ ν) (hm : m ≤ mβ)
    [SigmaFinite (ν.trim hm)] {f : β → E} (hf : AEStronglyMeasurable f ν) :
    μ[f ∘ g | m.comap g] =ᵐ[μ] (ν[f | m]) ∘ g := by
  have hmg : m.comap g ≤ mα := (MeasurableSpace.comap_mono hm).trans hg.measurable.comap_le
  have htrim := hg.trim_comap hm
  have : SigmaFinite (μ.trim hmg) := by
    let : MeasurableSpace α := m.comap g
    let : MeasurableSpace β := m
    exact htrim.sigmaFinite
  by_cases hfi : Integrable f ν
  · have hcomp : Integrable (f ∘ g) μ := hg.integrable_comp_of_integrable hfi
    have hce : Integrable ((ν[f | m]) ∘ g) μ :=
      hg.integrable_comp_of_integrable integrable_condExp
    refine (ae_eq_condExp_of_forall_setIntegral_eq hmg hcomp
      (fun _ _ _ ↦ hce.integrableOn) ?_
      ((stronglyMeasurable_condExp.comp_measurable
        (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable)).symm
    rintro _ ⟨s, hs, rfl⟩ _
    have hset (k : β → E) (hk : AEStronglyMeasurable k ν) :
        ∫ x in g ⁻¹' s, k (g x) ∂μ = ∫ y in s, k y ∂ν := by
      rw [← hg.map_eq] at hk ⊢
      exact (setIntegral_map (hm s hs) hk hg.aemeasurable).symm
    exact (hset _ integrable_condExp.aestronglyMeasurable).trans
      ((setIntegral_condExp hm hfi hs).trans (hset f hf).symm)
  · have hcomp : ¬ Integrable (f ∘ g) μ := fun h ↦ hfi ((hg.integrable_comp hf).mp h)
    rw [condExp_of_not_integrable hcomp, condExp_of_not_integrable hfi]
    exact Filter.EventuallyEq.rfl

end MeasureTheory.MeasurePreserving

namespace TauCeti

variable {α β E : Type*} {m : MeasurableSpace α}
  [mα : MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β}

/-- Adjoining an independent probability space preserves conditional expectations of old
observables given the pullback of the old conditioning σ-algebra. The old measure need not be a
probability measure or even finite. -/
theorem condExp_prod_fst [IsProbabilityMeasure ν] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (μ.prod ν)[f ∘ Prod.fst | m.comap Prod.fst] =ᵐ[μ.prod ν] (μ[f | m]) ∘ Prod.fst :=
  (measurePreserving_fst (μ := μ) (ν := ν)).condExp_comap hm hf

end TauCeti
