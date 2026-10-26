/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Derivatives of lifts of circle maps

A map of the circle `AddCircle T` of degree one is described by a lift `F : ℝ → ℝ` with
`F (x + T) = F x + T` (see `TauCeti.Topology.Instances.AddCircle.Lift`). The derivative of a
differentiable lift is `T`-periodic, so a lift with continuous positive derivative, the lift of an
orientation-preserving `C¹` diffeomorphism, has derivative bounded between two positive
constants.

## Main declarations

* `AddCircle.periodic_deriv_of_lift`: the derivative of a lift is `T`-periodic.
* `AddCircle.exists_pos_le_deriv_le_of_lift`: a lift with continuous positive derivative has
  derivative in some interval `[c, M]` with `0 < c`.
-/

public section

namespace AddCircle

variable {T : ℝ} {F F' : ℝ → ℝ}

/-- The derivative of a lift `F` with `F (x + T) = F x + T` is `T`-periodic. -/
theorem periodic_deriv_of_lift (hF : ∀ x, HasDerivAt F (F' x) x)
    (hper : ∀ x, F (x + T) = F x + T) : Function.Periodic F' T := fun x ↦ by
  have h₁ : HasDerivAt (fun y ↦ F (y + T)) (F' (x + T)) x := (hF (x + T)).comp_add_const x T
  have h₂ : HasDerivAt (fun y ↦ F (y + T)) (F' x) x := by
    simpa only [hper] using (hF x).add_const T
  exact h₁.unique h₂

variable [hT : Fact (0 < T)]

/-- A lift with continuous positive derivative has derivative bounded above and below by
positive constants: a `C¹` lift of an orientation-preserving diffeomorphism of the circle has
derivative in some `[c, M]` with `0 < c`. -/
theorem exists_pos_le_deriv_le_of_lift (hF : ∀ x, HasDerivAt F (F' x) x)
    (hper : ∀ x, F (x + T) = F x + T) (hF' : Continuous F') (hpos : ∀ x, 0 < F' x) :
    ∃ c M : ℝ, 0 < c ∧ (∀ x, c ≤ F' x) ∧ ∀ x, F' x ≤ M := by
  have hK := (periodic_deriv_of_lift hF hper).compact_of_continuous hT.out.ne' hF'
  obtain ⟨_, ⟨x₀, rfl⟩, hmin⟩ := hK.exists_isLeast (Set.range_nonempty F')
  obtain ⟨M, hM⟩ := hK.isBounded.bddAbove
  exact ⟨F' x₀, M, hpos x₀, fun x ↦ hmin ⟨x, rfl⟩, fun x ↦ hM ⟨x, rfl⟩⟩

end AddCircle
