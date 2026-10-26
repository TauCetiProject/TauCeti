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
into a divisibility condition on the translation exponent. An element of `SL₂(ℤ)` with
vanishing lower-left entry, that is one fixing `∞` itself, is a signed translation `±Tʲ`.

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

/-- An element of `SL₂(ℤ)` with vanishing lower-left entry fixes the cusp `∞`, so it is a
translation up to sign: `Tᵇ` when its diagonal entries are `1`, and `-T⁻ᵇ` when they are `-1`,
where `b` is its upper-right entry. Adapted from the proof of
`ModularGroup.exists_eq_T_zpow_of_c_eq_zero` in Mathlib. -/
theorem ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero {g : SL(2, ℤ)}
    (hc : g 1 0 = 0) :
    g = ModularGroup.T ^ g 0 1 ∨ g = -ModularGroup.T ^ (-g 0 1) := by
  have had : g 0 0 * g 1 1 = 1 := by
    simpa only [det_fin_two, hc, mul_zero, sub_zero] using g.det_coe
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, ModularGroup.coe_T_zpow]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, ModularGroup.coe_T_zpow]

end TauCeti
