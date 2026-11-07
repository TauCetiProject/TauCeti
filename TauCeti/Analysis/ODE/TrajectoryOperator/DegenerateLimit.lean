/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.Degenerate

/-!
# Noninjective limits of trajectory operators

An operator limit with a nonzero kernel supplies the vanishing direction required by the
canonical non-Fredholm criterion in `TrajectoryOperator.Degenerate`.
-/

public section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti.WeakDerivStep

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : ℝ → E →L[ℝ] E}

/-- **A noninjective limit at `+∞` destroys the Fredholm property.** If `A` converges at `+∞` to
an operator which is not injective, then the trajectory operator `D_A u = u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atTop
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aplus : E →L[ℝ] E}
    (htop : Tendsto A atTop (𝓝 Aplus)) (hinj : ¬ Function.Injective Aplus) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨v, hAv, hv⟩ : ∃ v : E, _ ∧ v ≠ 0 := by simpa [injective_iff_map_eq_zero] using hinj
  refine not_isFredholm_trajectoryOperator_of_tendsto_atTop hv ?_ AL hAL
  simpa [Function.comp_def, hAv] using
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto Aplus).comp htop

/-- **A noninjective limit at `-∞` destroys the Fredholm property.** If `A` converges at `-∞` to
an operator which is not injective, then the trajectory operator `D_A u = u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atBot
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aminus : E →L[ℝ] E}
    (hbot : Tendsto A atBot (𝓝 Aminus)) (hinj : ¬ Function.Injective Aminus) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨v, hAv, hv⟩ : ∃ v : E, _ ∧ v ≠ 0 := by simpa [injective_iff_map_eq_zero] using hinj
  refine not_isFredholm_trajectoryOperator_of_tendsto_atBot hv ?_ AL hAL
  simpa [Function.comp_def, hAv] using
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto Aminus).comp hbot

end Complete

end TauCeti.WeakDerivStep
