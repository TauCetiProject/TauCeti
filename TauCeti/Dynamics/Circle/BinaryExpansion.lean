/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Binary expansion as a factor map onto the circle

Binary expansion `x ↦ ∑ xᵢ 2^(-(i+1))` (Mathlib's `Real.ofDigits`), read in `UnitAddCircle`, is a
continuous surjection from the one-sided full shift on `Fin 2` onto the circle which
semiconjugates the shift to the doubling map `z ↦ 2 • z`. So the doubling map is a factor of the
one-sided full shift on two symbols.

## Main results

* `TauCeti.binaryExpansion`: the point of the circle with given binary digits, the class of
  `Real.ofDigits x` (`TauCeti.binaryExpansion_apply`).
* `TauCeti.continuous_binaryExpansion`, `TauCeti.surjective_binaryExpansion`: it is a continuous
  surjection.
* `TauCeti.semiconj_binaryExpansion`: it turns the shift into the doubling map.
-/

public section

namespace TauCeti

open Set

/-- The point of the circle with binary digits `x`, that is, the class of `Real.ofDigits x`. -/
noncomputable def binaryExpansion (x : ℕ → Fin 2) : UnitAddCircle :=
  (Real.ofDigits x : UnitAddCircle)

/-- Binary expansion is the class of `Real.ofDigits x` in the circle. -/
@[simp]
theorem binaryExpansion_apply (x : ℕ → Fin 2) :
    binaryExpansion x = (Real.ofDigits x : UnitAddCircle) :=
  (rfl)

/-- Binary expansion is `Real.ofDigits` followed by the projection onto the circle. -/
theorem binaryExpansion_eq_comp :
    binaryExpansion = ((↑) : ℝ → UnitAddCircle) ∘ Real.ofDigits :=
  funext binaryExpansion_apply

/-- Binary expansion is continuous for the product of discrete topologies on `ℕ → Fin 2`. -/
theorem continuous_binaryExpansion : Continuous binaryExpansion := by
  rw [binaryExpansion_eq_comp]
  exact (AddCircle.continuous_mk' 1).comp Real.continuous_ofDigits

/-- Every point of the circle has a binary expansion. -/
theorem surjective_binaryExpansion : Function.Surjective binaryExpansion := by
  rw [← Set.surjOn_univ, binaryExpansion_eq_comp]
  have hcoe : SurjOn ((↑) : ℝ → UnitAddCircle) (Icc 0 1) univ := by
    have := AddCircle.coe_image_Icc_eq (1 : ℝ) 0
    rw [zero_add] at this
    exact this.symm.subset
  exact hcoe.comp (Real.ofDigits_SurjOn one_lt_two)

/-- Binary expansion turns the shift into the doubling map. -/
theorem semiconj_binaryExpansion :
    Function.Semiconj binaryExpansion (SymbolicDynamics.FullShift.shift (1 : ℕ))
      (fun z : UnitAddCircle ↦ 2 • z) := by
  intro x
  have h := Real.ofDigits_eq_sum_add_ofDigits x 1
  simp only [Finset.range_one, Finset.sum_singleton, Real.ofDigitsTerm, zero_add, pow_one,
    Nat.cast_ofNat] at h
  have hx : 2 * Real.ofDigits x = ((x 0 : ℕ) : ℝ) +
      Real.ofDigits (SymbolicDynamics.FullShift.shift (1 : ℕ) x) := by
    have : SymbolicDynamics.FullShift.shift (1 : ℕ) x = fun i ↦ x (i + 1) := by
      funext i
      simp [SymbolicDynamics.FullShift.shift_apply, add_comm]
    rw [this, h]
    ring
  have hzero : ((((x 0 : ℕ) : ℝ)) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨((x 0 : ℕ) : ℤ), by simp⟩
  simp [← AddCircle.coe_nsmul, hx, hzero]

end TauCeti
