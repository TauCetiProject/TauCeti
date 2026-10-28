/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable

/-!
# Predictable elementary processes

A random variable measurable at time `s`, held over `(s,t]`, gives a predictable process.
This is the elementary building block for predictable trading positions and stochastic
integrands. The coefficient need not be bounded or integrable.
-/

public section

open Set TopologicalSpace

namespace MeasureTheory.StronglyMeasurable

variable {Ω ι E : Type*} {m : MeasurableSpace Ω} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace E] [PseudoMetrizableSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [Zero E]
  {ℱ : Filtration ι m} {s : ι} {f : Ω → E}

/-- A coefficient known at `s`, used on `(s,t]`, is predictable. -/
theorem isStronglyPredictable_indicator_Ioc (hf : StronglyMeasurable[ℱ s] f) (t : ι) :
    IsStronglyPredictable ℱ (fun u ω ↦ (Ioc s t).indicator (fun _ ↦ f ω) u) := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  apply Measurable.stronglyMeasurable
  apply measurable_of_isOpen
  intro U hU
  have hrect := measurableSet_predictable_Ioc_prod s t (hf.measurable hU.measurableSet)
  by_cases hzero : (0 : E) ∈ U
  · have heq : (Function.uncurry (fun u ω ↦ (Ioc s t).indicator (fun _ ↦ f ω) u)) ⁻¹' U =
        (Ioc s t ×ˢ (f ⁻¹' U)) ∪ (Ioc s t ×ˢ (univ : Set Ω))ᶜ := by
      ext ⟨u, ω⟩
      by_cases hu : u ∈ Ioc s t <;> simp [hu, hzero]
    rw [heq]
    exact hrect.union (measurableSet_predictable_Ioc_prod s t MeasurableSet.univ).compl
  · have heq : (Function.uncurry (fun u ω ↦ (Ioc s t).indicator (fun _ ↦ f ω) u)) ⁻¹' U =
        Ioc s t ×ˢ (f ⁻¹' U) := by
      ext ⟨u, ω⟩
      by_cases hu : u ∈ Ioc s t <;> simp [hu, hzero]
    rw [heq]
    exact hrect

end MeasureTheory.StronglyMeasurable
