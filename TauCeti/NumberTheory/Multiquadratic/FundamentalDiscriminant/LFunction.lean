/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.LSeries.Quadratic.Character

/-!
# Positive continued L-values for fundamental discriminants

For a fundamental discriminant `D ≠ 1`, the complex realization of its primitive quadratic
character has positive real continued L-values on the real interval `[1, ∞)`. The endpoint
uses the continued `DirichletCharacter.LFunction`, not the Dirichlet series, whose convergence
at `1` is not assumed.

The theorem `fundamentalDiscriminantCharCast_LFunction_pos` gives `0 < L(s, χ_D)` for
`s ≥ 1` and `D ≠ 1`, providing the nonvanishing input for the class-number formula.
-/

public section

namespace TauCeti.Multiquadratic

open scoped ComplexOrder

/-- The continued L-function of the fundamental-discriminant character is positive real on
`[1, ∞)`, for every fundamental discriminant other than `1`. -/
theorem fundamentalDiscriminantCharCast_LFunction_pos {D : ℤ} [NeZero D.natAbs]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) {s : ℝ} (hs : 1 ≤ s) :
    0 < (fundamentalDiscriminantCharCast ℂ D hD).LFunction s := by
  exact DirichletCharacter.LFunction_pos_of_one_le
    (fundamentalDiscriminantCharCast_isQuadratic hD)
    (fun h ↦ hD1 ((fundamentalDiscriminantCharCast_eq_one_iff hD).mp h)) hs

end TauCeti.Multiquadratic
