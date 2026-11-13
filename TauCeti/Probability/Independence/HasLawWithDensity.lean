/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PiWithDensity
public import Mathlib.Probability.HasLaw

/-!
# Product-density laws of independent families

Finite independent families with densities have joint density equal to the product of
those densities. The reference measures may be any sigma-finite measures.
This combines `iIndepFun.hasLaw_pi` with `TauCeti.pi_withDensity₀`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {α : ι → Type*} [∀ i, MeasurableSpace (α i)] {P : Measure Ω}
  {X : ∀ i, Ω → α i} {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]
  {p : ∀ i, α i → ℝ≥0∞}

/-- Independent coordinates with almost everywhere measurable densities have the product
of those densities as their joint density. Independence supplies finiteness of the laws. -/
theorem hasLaw_pi_withDensity₀ (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) ((μ i).withDensity (p i)) P)
    (hp : ∀ i, AEMeasurable (p i) (μ i)) :
    HasLaw (fun ω i ↦ X i ω)
      ((Measure.pi μ).withDensity fun x ↦ ∏ i, p i (x i)) P := by
  have := hind.isProbabilityMeasure
  have (i : ι) : IsFiniteMeasure ((μ i).withDensity (p i)) :=
    (hX i).isFiniteMeasure_iff.mp inferInstance
  simpa only [TauCeti.pi_withDensity₀ μ hp] using hind.hasLaw_pi hX

/-- Independent coordinates with measurable densities have their product as joint density. -/
theorem hasLaw_pi_withDensity (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) ((μ i).withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) :
    HasLaw (fun ω i ↦ X i ω)
      ((Measure.pi μ).withDensity fun x ↦ ∏ i, p i (x i)) P :=
  hind.hasLaw_pi_withDensity₀ hX (fun i ↦ (hp i).aemeasurable)

/-- Independent real coordinates with Lebesgue densities have the product Lebesgue density. -/
theorem hasLaw_pi_volume_withDensity {X : ι → Ω → ℝ} {p : ι → ℝ → ℝ≥0∞}
    (hind : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (volume.withDensity (p i)) P)
    (hp : ∀ i, Measurable (p i)) :
    HasLaw (fun ω i ↦ X i ω) (volume.withDensity fun x : ι → ℝ ↦ ∏ i, p i (x i)) P := by
  simpa only [← volume_pi] using hind.hasLaw_pi_withDensity hX hp

end ProbabilityTheory.iIndepFun
