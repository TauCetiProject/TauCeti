/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Probability.LargeDeviations.Basic

/-!
# The large deviation principle for a constant family of Dirac masses

The constant family `δ_{x₀}` satisfies the large deviation principle at every positive speed with
the rate function that is `0` at `x₀` and `∞` elsewhere. The case of a point not in a closed set
`F` shows why logarithms must be extended-real: `log 0 = ⊥`, not `0`.

## Main results

* `TauCeti.Probability.hasLDP_dirac`: the large deviation principle for `δ_{x₀}`.
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T1Space X] [DecidableEq X]

/-- The constant family `δ_{x₀}` satisfies a large deviation principle at any positive speed with
rate `0` at `x₀` and `∞` elsewhere. -/
theorem hasLDP_dirac (l : Filter ι) [l.NeBot] {ε : ι → ℝ≥0} (hε : ∀ i, 0 < ε i) (x₀ : X) :
    HasLDP l ε (fun _ => Measure.dirac x₀) (fun x => if x = x₀ then 0 else ∞) := by
  have hpos : ∀ i, (0 : EReal) < ((ε i : ℝ) : EReal) := fun i => by exact_mod_cast hε i
  have hbot : ∀ i, ((ε i : ℝ) : EReal) * ⊥ = ⊥ := fun i => EReal.mul_bot_of_pos (hpos i)
  have hinf : ∀ A : Set X, x₀ ∉ A → (⨅ x ∈ A, if x = x₀ then (0 : ℝ≥0∞) else ∞) = ∞ := by
    intro A hA
    exact le_antisymm le_top (le_iInf₂ fun x hx => by simp [show x ≠ x₀ from fun h => hA (h ▸ hx)])
  have hinf0 : ∀ A : Set X, x₀ ∈ A → (⨅ x ∈ A, if x = x₀ then (0 : ℝ≥0∞) else ∞) = 0 :=
    fun A hA => le_antisymm (iInf₂_le_of_le x₀ hA (by simp)) bot_le
  refine ⟨?_, fun G hG => ?_, fun F hF => ?_⟩
  · refine lowerSemicontinuous_iff_isClosed_preimage.mpr fun c => ?_
    by_cases hc : c = ∞
    · simp [hc]
    · have : (fun x => if x = x₀ then (0 : ℝ≥0∞) else ∞) ⁻¹' Set.Iic c = {x₀} := by
        ext x
        by_cases hx : x = x₀ <;> simp [hx, hc]
      rw [this]
      exact isClosed_singleton
  · by_cases hx : x₀ ∈ G
    · simp [hinf0 G hx, Measure.dirac_apply' _ hG.measurableSet, hx]
    · simp [hinf G hx]
  · by_cases hx : x₀ ∈ F
    · simp [hinf0 F hx, Measure.dirac_apply' _ hF.measurableSet, hx]
    · simp [hinf F hx, Measure.dirac_apply' _ hF.measurableSet, hx, hbot]

end TauCeti.Probability
