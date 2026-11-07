/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Extension
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Exact mass of Borel restrictions

For a current of locally finite mass, restriction to a measurable set restricts its mass
measure exactly: `‖T ⌞ A‖ = ‖T‖ ⌞ A`. In particular, its total mass is `‖T‖ A`, and the
restriction vanishes exactly on sets of zero mass measure. These identities apply to the
native vector-valued test functions, including test forms, without a finite total mass
assumption. They do not assert any regularity of the boundary of a Borel restriction.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 and §4.1.7.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {n : ℕ∞}
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ]
  {T : 𝓕} {A : Set Ω}

/-- A current is the sum of its restrictions to a measurable set and its complement. -/
theorem massRestrict_add_massRestrict_compl_apply (hT : HasLocallyFiniteMass T)
    (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T hA φ + massRestrict T hA.compl φ = T φ := by
  have h := congrArg (fun S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ => S φ)
    (massRestrict_union (T := T) hA hA.compl disjoint_compl_right)
  simpa [massRestrict_univ_apply hT] using h.symm

/-- Restricting a current of locally finite mass restricts its mass measure exactly.
No finiteness of the total mass or regularity of the boundary is required. -/
@[simp]
theorem massMeasure_massRestrict (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A) :
    massMeasure (massRestrict T hA) = (massMeasure T).restrict A := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let μ := massMeasure (massRestrict T hA)
  let ν := massMeasure (massRestrict T hA.compl)
  have hsplit : massMeasure T ≤ μ + ν := by
    apply massMeasure_le_of_enorm_apply_le
    intro φ
    rw [lintegral_add_measure,
      ← massRestrict_add_massRestrict_compl_apply hT hA φ]
    exact (enorm_add_le _ _).trans (add_le_add
      (enorm_apply_le_lintegral_massMeasure (hasLocallyFiniteMass_massRestrict hA) φ)
      (enorm_apply_le_lintegral_massMeasure (hasLocallyFiniteMass_massRestrict hA.compl) φ))
  have hzero : ν.restrict A = 0 := by
    apply le_antisymm _ bot_le
    calc ν.restrict A ≤ ((massMeasure T).restrict Aᶜ).restrict A :=
          Measure.restrict_mono_measure (massMeasure_massRestrict_le hA.compl) A
      _ = 0 := by rw [Measure.restrict_restrict hA]; simp
  apply le_antisymm (massMeasure_massRestrict_le hA)
  calc (massMeasure T).restrict A ≤ (μ + ν).restrict A :=
        Measure.restrict_mono_measure hsplit A
    _ = μ.restrict A := by rw [Measure.restrict_add, hzero, add_zero]
    _ ≤ μ := Measure.restrict_le_self

/-- The total mass of a Borel restriction is the mass measure of its restricting set,
including when that value is infinite. -/
@[simp]
theorem mass_massRestrict (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A) :
    mass (massRestrict T hA) = massMeasure T A := by
  rw [← massMeasure_univ (hasLocallyFiniteMass_massRestrict hA),
    massMeasure_massRestrict hT hA, Measure.restrict_apply_univ]

/-- A Borel restriction of a locally finite-mass current vanishes if and only if the
restricting set has zero mass measure. -/
@[simp]
theorem massRestrict_eq_zero_iff (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A) :
    massRestrict T hA = 0 ↔ massMeasure T A = 0 := by
  rw [← mass_massRestrict hT hA, mass_eq_zero_iff]
  exact ⟨fun h => by simp [h], fun h => ContinuousLinearMap.ext fun φ => congrFun h φ⟩

end Distribution
