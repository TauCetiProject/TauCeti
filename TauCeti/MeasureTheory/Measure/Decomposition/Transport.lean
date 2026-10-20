/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Decomposition.Atomic
public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel.Transport
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Transport from mixed atomic and diffuse measures

A finite standard Borel measure can be transported to another measure of the same mass
exactly when its point masses can be assigned to target points without exceeding the target
measure. Different source atoms may be sent to the same target point, so the condition concerns
the sum of their images, not just the individual point masses.

`exists_measurePreserving_of_atomic_assignment` extends any such assignment to a measurable
transport map. The complementary diffuse measure is transported to the remainder of the target
using `MeasureTheory.Measure.exists_measurePreserving_of_nullSingleton_of_measure_univ_eq`.
`exists_hasLaw_iff_exists_atomic_assignment` gives the corresponding feasibility criterion for
a.e.-measurable maps. There is no topology or transport cost in these statements.
-/

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

/-- Extend an assignment of the source atoms to a measurable transport map. The sum of the
assigned point masses must be dominated by the target law. The map agrees with the assignment
at every positive-mass point, and transports the diffuse part to the exact target remainder. -/
theorem exists_measurePreserving_of_atomic_assignment
    (hmass : μ univ = ν univ) (f : positiveSingletons μ → Y)
    (hf : (Measure.sum fun x : positiveSingletons μ ↦
      μ {(x : X)} • Measure.dirac (f x)) ≤ ν) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      (∀ x : positiveSingletons μ, T x = f x) ∧
      MeasurePreserving T (diffusePart μ)
        (ν - Measure.sum fun x : positiveSingletons μ ↦
          μ {(x : X)} • Measure.dirac (f x)) := by
  classical
  let ρ := Measure.sum fun x : positiveSingletons μ ↦
    μ {(x : X)} • Measure.dirac (f x)
  have hρ : ρ ≤ ν := hf
  have : IsFiniteMeasure ν := ⟨hmass ▸ measure_lt_top μ univ⟩
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le ν hρ
  have hcount := (countable_positiveSingletons μ).to_subtype
  have hρmass : ρ univ = atomicPart μ univ := by
    rw [atomicPart_eq_sum_dirac]
    simp [ρ, Measure.sum_apply]
  have hdiffmass : diffusePart μ univ = (ν - ρ) univ := by
    have hsplit := congrArg (fun m : Measure X ↦ m univ) (atomicPart_add_diffusePart μ)
    simp only [Measure.add_apply] at hsplit
    rw [Measure.sub_apply MeasurableSet.univ hρ, ← hmass, hsplit.symm, ← hρmass]
    exact (ENNReal.add_sub_cancel_left (measure_ne_top ρ univ)).symm
  obtain ⟨g, hg⟩ := exists_measurePreserving_of_nullSingleton_of_measure_univ_eq
    (diffusePart μ) (ν - ρ) hdiffmass
  let T : X → Y := fun x ↦ if hx : x ∈ positiveSingletons μ then f ⟨x, hx⟩ else g x
  have hTm : Measurable T := (measurable_of_countable f).dite
    (hg.measurable.comp measurable_subtype_coe) (measurableSet_positiveSingletons μ)
  have hTf (x : positiveSingletons μ) : T x = f x := by
    simp only [T, dite_eq_left x.property]
  have hTdiff : MeasurePreserving T (diffusePart μ) (ν - ρ) := by
    apply hg.congr hTm
    have hae : ∀ᵐ x ∂diffusePart μ, x ∉ positiveSingletons μ :=
      measure_eq_zero_iff_ae_notMem.1 diffusePart_apply_positiveSingletons
    exact hae.mono fun x hx ↦ by simp only [T, dite_eq_right hx]
  have hTatomic : (atomicPart μ).map T = ρ := by
    simpa only [ρ, hTf] using (map_atomicPart_eq_sum_dirac (μ := μ) hTm)
  refine ⟨T, ⟨hTm, ?_⟩, hTf, hTdiff⟩
  rw [← atomicPart_add_diffusePart μ, Measure.map_add _ _ hTm,
    hTatomic, hTdiff.map_eq, add_comm, Measure.sub_add_cancel_of_le hρ]

/-- A finite standard Borel measure admits a transport map to a standard Borel target law
exactly when their masses agree and its point masses can be assigned to target points without
exceeding the target law. This permits a diffuse remainder on either side and merging atoms. -/
theorem exists_hasLaw_iff_exists_atomic_assignment :
    (∃ T : X → Y, HasLaw T ν μ) ↔
      μ univ = ν univ ∧ ∃ f : positiveSingletons μ → Y,
        (Measure.sum fun x : positiveSingletons μ ↦
          μ {(x : X)} • Measure.dirac (f x)) ≤ ν := by
  constructor
  · rintro ⟨T, hT⟩
    let S := hT.aemeasurable.mk T
    have hSm : Measurable S := hT.aemeasurable.measurable_mk
    have hS : μ.map S = ν := by rw [← Measure.map_congr hT.aemeasurable.ae_eq_mk, hT.map_eq]
    refine ⟨?_, fun x ↦ S x, ?_⟩
    · rw [← hT.map_eq, Measure.map_apply_of_aemeasurable hT.aemeasurable MeasurableSet.univ,
        preimage_univ]
    rw [← map_atomicPart_eq_sum_dirac hSm, ← hS]
    exact Measure.map_mono (atomicPart_le μ) hSm
  · rintro ⟨hmass, f, hf⟩
    obtain ⟨T, hT, -⟩ := exists_measurePreserving_of_atomic_assignment hmass f hf
    exact ⟨T, hT.hasLaw⟩

end TauCeti
