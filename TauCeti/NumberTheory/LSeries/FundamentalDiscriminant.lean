/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.LSeries.QuadraticCharacter

/-!
# Positive continued L-values for fundamental discriminants

For a fundamental discriminant `D ≠ 1`, the complex realization of its primitive quadratic
character has positive real continued L-values on the real interval `[1, ∞)`. The endpoint
uses the continued `DirichletCharacter.LFunction`, not the Dirichlet series, whose convergence
at `1` is not assumed.

The character is the scalar realization of the prime-discriminant product. Its conductor and
nonprincipality comparisons supply the hypotheses of the native nonvanishing theorem at `1`,
as used in `DirichletCharacter.LFunction_apply_one_pos`.
-/

public section

namespace TauCeti.Multiquadratic

open scoped ComplexOrder

/-- The continued L-function of the fundamental-discriminant character is positive real on
`[1, ∞)`, for every fundamental discriminant other than `1`. -/
theorem fundamentalDiscriminantCharCast_LFunction_pos {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) {s : ℝ} (hs : 1 ≤ s) :
    let _ : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
    0 < (fundamentalDiscriminantCharCast ℂ D hD).LFunction s := by
  let _ : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
  have hχ := fundamentalDiscriminantCharCast_isQuadratic (R := ℂ) hD
  rcases hs.eq_or_lt with rfl | hs
  · simpa using DirichletCharacter.LFunction_apply_one_pos hχ
      (fun h ↦ hD1 ((fundamentalDiscriminantCharCast_eq_one_iff hD).mp h))
  · exact DirichletCharacter.LFunction_pos_of_one_lt hχ hs

end TauCeti.Multiquadratic
