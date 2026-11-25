/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Unitization

/-!
# Checks for the unitization extension of a positive functional

The faithfulness transfer
`PositiveContinuousLinearMap.eq_zero_of_unitization_map_star_mul_self_eq_zero` assumes that `A` has
no unit. For the unital algebra `A = ℂ` the hypothesis cannot be dropped: the projection
`e = 1 - 1_A` of `Unitization ℂ ℂ ≅ ℂ ⊕ ℂ` is nonzero, but the extension `τ⁺¹` of every positive
functional `τ` of `ℂ` (for instance the identity, a faithful tracial state) vanishes at
`e⋆e = e`, because `τ⁺¹(1) = ‖τ‖ = τ(1)`.
-/

public section

open scoped ComplexOrder

namespace TauCeti.UnitizationTraceExample

/-- The projection `e = 1 - 1_A` of `Unitization ℂ ℂ`. -/
noncomputable abbrev e : Unitization ℂ ℂ := 1 - (1 : ℂ)

/-- The projection `e = 1 - 1_A` is nonzero: its scalar part is `1`. -/
theorem e_ne_zero : e ≠ 0 := by
  intro h
  simpa [e] using congrArg (fun x : Unitization ℂ ℂ ↦ x.fst) h

/-- `e = 1 - 1_A` is a projection: `e⋆e = e`. -/
theorem star_e_mul_e : star e * e = e := by
  ext <;> simp [e]

/-- The unitization extension of any positive functional `τ` of the unital algebra `ℂ` vanishes
at `e⋆e` for the nonzero `e = 1 - 1_A`: it is not faithful, even when `τ` is. -/
theorem unitization_map_star_e_mul_e_eq_zero (τ : ℂ →P[ℂ] ℂ) :
    τ.unitization (star e * e) = 0 := by
  rw [star_e_mul_e, PositiveContinuousLinearMap.unitization_apply]
  simp [e, τ.ofReal_opNorm_eq_map_one]

end TauCeti.UnitizationTraceExample
