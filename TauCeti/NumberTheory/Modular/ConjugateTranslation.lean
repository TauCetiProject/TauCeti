/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Conjugates of integral translations

For `γ = [a,b;c,d]` in `SL₂(ℤ)`, the conjugate `γ Tʲ γ⁻¹` depends only on the first
column `(a,c)`. Its lower-left entry is `-j c²`. This calculation describes the
translations fixing the rational cusp `γ ∞` and turns congruence-subgroup membership
into a divisibility condition on the translation exponent.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §2.4.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

/-- Conjugating the translation `Tʲ` by `γ = [a,b;c,d]` gives
`[1-jac, ja²; -jc², 1+jac]`. -/
theorem _root_.Matrix.SpecialLinearGroup.coe_conj_T_zpow (γ : SL(2, ℤ)) (j : ℤ) :
    (↑(γ * ModularGroup.T ^ j * γ⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - j * γ 0 0 * γ 1 0, j * γ 0 0 ^ 2;
        -j * γ 1 0 ^ 2, 1 + j * γ 0 0 * γ 1 0] := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [det_fin_two] using γ.det_coe
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T_zpow, adjugate_fin_two, mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> nlinarith [hdet]

end TauCeti
