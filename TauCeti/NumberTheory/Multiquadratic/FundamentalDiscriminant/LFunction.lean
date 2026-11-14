/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Positive continued L-values and lower bounds at one for fundamental discriminants

For a fundamental discriminant `D ≠ 1`, the complex realization of its primitive quadratic
character has positive real continued L-values on the real interval `[1, ∞)`. The endpoint
uses the continued `DirichletCharacter.LFunction`, not the Dirichlet series, whose convergence
at `1` is not assumed.

Realizing `D` as the discriminant of `QuadraticAlgebra ℚ D 0`
(`QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr`) transfers the analytic class-number and
golden-ratio regulator lower bound of `TauCeti.NumberField.Quadratic.DedekindZeta` directly to
every fundamental discriminant `D ≠ 1` (`[NeZero D.natAbs]`): `2 log φ / √|D| ≤ Re L(1, χ_D)`.

## Main results

* `TauCeti.Multiquadratic.fundamentalDiscriminantCharCast_LFunction_pos`: `0 < L(s, χ_D)` for
  `s ≥ 1` and `D ≠ 1`.
* `TauCeti.Multiquadratic.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re`:
  `2 log φ / √|D| ≤ Re L(1, χ_D)` for every fundamental discriminant `D ≠ 1`.
-/

public section

namespace TauCeti.Multiquadratic

open scoped ComplexOrder Real

/-- The continued L-function of the fundamental-discriminant character is positive real on
`[1, ∞)`, for every fundamental discriminant other than `1`. -/
theorem fundamentalDiscriminantCharCast_LFunction_pos {D : ℤ} [NeZero D.natAbs]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) {s : ℝ} (hs : 1 ≤ s) :
    0 < (fundamentalDiscriminantCharCast ℂ D hD).LFunction s := by
  exact DirichletCharacter.LFunction_pos_of_one_le
    (fundamentalDiscriminantCharCast_isQuadratic hD)
    (fun h ↦ hD1 ((fundamentalDiscriminantCharCast_eq_one_iff hD).mp h)) hs

/-- **Sharp effective lower bound on `L(1, χ_D)` for fundamental discriminants.** For every
fundamental discriminant `D ≠ 1`, `2 log φ / √|D| ≤ Re L(1, χ_D)` (attained at `D = 5`). -/
theorem two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re
    {D : ℤ} [NeZero D.natAbs] (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    2 * Real.log Real.goldenRatio / √|(D : ℝ)| ≤
      ((fundamentalDiscriminantCharCast ℂ D hD).LFunction 1).re := by
  have : Fact (¬ IsSquare D) := ⟨fun h ↦ hD.not_isSquare_rat hD1 (h.map (Int.castRingHom ℚ))⟩
  obtain ⟨d, _, rfl⟩ : ∃ (d : ℤ) (_ : Fact (¬ IsSquare d)),
      NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = D :=
    ⟨D, inferInstance, QuadraticAlgebra.discr_eq_iff_isFundamentalDiscr.mpr hD⟩
  convert TauCeti.NumberField.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re
    (QuadraticAlgebra.finrank_eq_two (d : ℚ) 0) using 3
  ext a
  simp

end TauCeti.Multiquadratic
