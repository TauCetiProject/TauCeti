/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.Algebra.Squarefree
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.Model

/-!
# Positive continued L-values and lower bounds at one for fundamental discriminants

For a fundamental discriminant `D ≠ 1`, the complex realization of its primitive quadratic
character has positive real continued L-values on the real interval `[1, ∞)`. The endpoint
uses the continued `DirichletCharacter.LFunction`, not the Dirichlet series, whose convergence
at `1` is not assumed.

Realizing `D` as the discriminant of `QuadraticAlgebra ℚ d 0` transfers the analytic class-number
and golden-ratio regulator lower bound of `TauCeti.NumberField.Quadratic.DedekindZeta` directly to
every fundamental discriminant `D ≠ 1`: `2 log φ / √|D| ≤ Re L(1, χ_D)`.

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

/-- Every fundamental discriminant `D ≠ 1` is the discriminant of a rational quadratic field
`QuadraticAlgebra ℚ (d : ℚ) 0`. -/
private theorem exists_quadraticAlgebra_discr_eq {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hD1 : D ≠ 1) :
    ∃ (d : ℤ) (_ : Fact (¬ IsSquare d)),
      NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = D := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨hd4, hsf⟩ | ⟨h0, hmsf, hm4⟩
  · have hns : Fact (¬ IsSquare D) := ⟨fun h ↦
      not_isSquare_intCast_of_squarefree_of_ne_one hsf hD1 (Rat.isSquare_intCast_iff.mpr h)⟩
    exact ⟨D, hns, QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hd4⟩
  · obtain ⟨m, rfl⟩ : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero h0
    rw [Int.mul_ediv_cancel_left m (by norm_num : (4 : ℤ) ≠ 0)] at hmsf hm4
    have hm1 : m ≠ 1 := by rcases hm4 with h | h <;> omega
    have hns : Fact (¬ IsSquare m) := ⟨fun h ↦
      not_isSquare_intCast_of_squarefree_of_ne_one hmsf hm1 (Rat.isSquare_intCast_iff.mpr h)⟩
    exact ⟨m, hns, QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hmsf
      (by rcases hm4 with h | h <;> omega)⟩

/-- **Sharp effective lower bound on `L(1, χ_D)` for every fundamental discriminant `D ≠ 1`.**
Realizing `D` as the discriminant of a quadratic number field gives
`2 log φ / √|D| ≤ Re L(1, χ_D)` (attained at `D = 5`). -/
theorem two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re
    {D : ℤ} [NeZero D.natAbs] (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    2 * Real.log Real.goldenRatio / √|(D : ℝ)| ≤
      ((fundamentalDiscriminantCharCast ℂ D hD).LFunction 1).re := by
  obtain ⟨d, _, hdiscr⟩ := exists_quadraticAlgebra_discr_eq hD hD1
  subst hdiscr
  convert TauCeti.NumberField.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re
    (QuadraticAlgebra.finrank_eq_two (d : ℚ) 0) using 3
  ext a
  simp

end TauCeti.Multiquadratic
