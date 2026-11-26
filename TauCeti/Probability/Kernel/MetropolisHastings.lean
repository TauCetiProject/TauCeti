/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Invariance
import TauCeti.Probability.Kernel.Invariance

/-!
# Metropolis–Hastings kernels on measurable spaces

Given a proposal kernel and an acceptance function, `Kernel.mhKernel` uses
`Kernel.withDensity` for accepted proposals and puts the remaining mass at the current state.
The result is Markov exactly when the accepted mass is at most one at each state. Reversibility
is equivalent to reversibility of the accepted part for any reference measure. On disjoint
source and destination sets the rejection part contributes no mass.

## References

* L. Tierney, *A note on Metropolis-Hastings kernels for general state spaces*,
  Ann. Appl. Probab. 8 (1998), §§1–2, equations (1)–(3).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {X : Type*} [MeasurableSpace X]

/-- Accept a proposal from `Q` with weight `a x y`, and put the remaining mass at `x`.
The remaining mass is `1 - Q.withDensity a x univ`, using truncated subtraction. -/
noncomputable def mhKernel (Q : Kernel X X) [IsSFiniteKernel Q] (a : X → X → ℝ≥0∞) :
    Kernel X X :=
  Q.withDensity a + Kernel.id.withDensity (fun x _ ↦ 1 - Q.withDensity a x univ)

/-- The law at `x` is the accepted proposal measure plus a Dirac mass weighted by the
rejection probability. -/
theorem mhKernel_apply (Q : Kernel X X) [IsSFiniteKernel Q] (a : X → X → ℝ≥0∞) (x : X) :
    Q.mhKernel a x = Q.withDensity a x + (1 - Q.withDensity a x univ) • Measure.dirac x := by
  have hr : Measurable (Function.uncurry fun y (_ : X) ↦ 1 - Q.withDensity a y univ) :=
    (measurable_const.sub ((Q.withDensity a).measurable_coe .univ)).comp measurable_fst
  rw [mhKernel, add_apply, Kernel.withDensity_apply _ hr, id_apply,
    dirac_withDensity' measurable_const]

/-- For jointly measurable `a`, the mass of a measurable set is the accepted proposal
integral over that set, plus the rejection probability if the set contains `x`. -/
theorem mhKernel_apply_of_measurable (Q : Kernel X X) [IsSFiniteKernel Q]
    {a : X → X → ℝ≥0∞} (ha : Measurable (Function.uncurry a)) (x : X)
    {B : Set X} (hB : MeasurableSet B) :
    Q.mhKernel a x B = (∫⁻ y in B, a x y ∂Q x) +
      (1 - ∫⁻ y, a x y ∂Q x) * B.indicator 1 x := by
  simp [mhKernel_apply, Measure.dirac_apply' _ hB,
    Kernel.withDensity_apply' _ ha x B, Kernel.withDensity_apply' _ ha x univ]

/-- If `a` is not jointly measurable, the accepted part is zero and the kernel stays at
the current state. -/
@[simp]
theorem mhKernel_of_not_measurable (Q : Kernel X X) [IsSFiniteKernel Q]
    {a : X → X → ℝ≥0∞} (ha : ¬ Measurable (Function.uncurry a)) : Q.mhKernel a = Kernel.id := by
  simp [mhKernel, withDensity_of_not_measurable _ ha]

/-- If every proposal is rejected, the chain stays at the current state. -/
@[simp]
theorem mhKernel_zero (Q : Kernel X X) [IsSFiniteKernel Q] : Q.mhKernel 0 = Kernel.id := by
  simp [mhKernel]

/-- Accepting every proposal from a Markov kernel recovers that kernel. -/
@[simp]
theorem mhKernel_one (Q : Kernel X X) [IsMarkovKernel Q] : Q.mhKernel 1 = Q := by
  simp [mhKernel]

/-- The Metropolis–Hastings kernel is Markov exactly when the accepted part has mass at most
one at every state. -/
theorem isMarkovKernel_mhKernel_iff (Q : Kernel X X) [IsSFiniteKernel Q] (a : X → X → ℝ≥0∞) :
    IsMarkovKernel (Q.mhKernel a) ↔ ∀ x, Q.withDensity a x univ ≤ 1 := by
  have hmass (x : X) : Q.mhKernel a x univ =
      Q.withDensity a x univ + (1 - Q.withDensity a x univ) := by
    simp [mhKernel_apply]
  refine ⟨fun h x ↦ ?_, fun h ↦ ⟨fun x ↦ ⟨?_⟩⟩⟩
  · calc
      Q.withDensity a x univ ≤ Q.mhKernel a x univ := by
        rw [hmass]
        exact le_self_add
      _ = 1 := (h.isProbabilityMeasure x).measure_univ
  · rw [hmass, add_tsub_cancel_of_le (h x)]

/-- A Markov proposal and acceptance weights at most one give a Markov kernel. -/
theorem isMarkovKernel_mhKernel (Q : Kernel X X) [IsMarkovKernel Q] {a : X → X → ℝ≥0∞}
    (ha : ∀ x y, a x y ≤ 1) : IsMarkovKernel (Q.mhKernel a) := by
  rw [isMarkovKernel_mhKernel_iff]
  intro x
  by_cases hmeas : Measurable (Function.uncurry a)
  · simpa [Kernel.withDensity_apply' _ hmeas] using
      (lintegral_mono (μ := Q x) (ha x) : (∫⁻ y, a x y ∂Q x) ≤ ∫⁻ _, 1 ∂Q x)
  · simp [withDensity_of_not_measurable _ hmeas]

/-- A Metropolis–Hastings kernel is reversible exactly when its accepted part is reversible. -/
theorem mhKernel_isReversible_iff (Q : Kernel X X) [IsSFiniteKernel Q] (a : X → X → ℝ≥0∞)
    (π : Measure X) : (Q.mhKernel a).IsReversible π ↔ (Q.withDensity a).IsReversible π := by
  have offDiagonal {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hAB : Disjoint A B) :
      ∫⁻ x in A, Q.mhKernel a x B ∂π = ∫⁻ x in A, Q.withDensity a x B ∂π := by
    refine setLIntegral_congr_fun hA fun x hx ↦ ?_
    have hxB : x ∉ B := fun hxB ↦ Set.disjoint_left.mp hAB hx hxB
    simp [mhKernel_apply, Measure.dirac_apply' _ hB, hxB]
  simp_rw [isReversible_iff_on_disjoint]
  constructor <;> intro h A B hA hB hAB <;>
    simpa only [offDiagonal hA hB hAB, offDiagonal hB hA hAB.symm] using h hA hB hAB

end ProbabilityTheory.Kernel
