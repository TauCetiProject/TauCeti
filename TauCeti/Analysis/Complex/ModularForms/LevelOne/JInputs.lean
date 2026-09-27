/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The level-one modular invariant

The classical modular invariant is the quotient `E₄³ / Δ`.  The denominator has no zeros in
the upper half-plane, so the quotient is holomorphic there.  Its weight is zero: the weight
factors of its numerator and denominator cancel under the modular group.  The identity
`j - 1728 = E₆² / Δ` identifies the fibres above `0` and `1728` with the zero loci of
`E₄` and `E₆`, respectively.

The normalization and identity follow the level-one Eisenstein and discriminant identities in
Serre, *A Course in Arithmetic*, VII.3.
-/

public noncomputable section

open UpperHalfPlane MatrixGroups ModularForm Matrix.SpecialLinearGroup
open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

/-- The normalized modular invariant `j = E₄³ / Δ` on the upper half-plane. -/
def j (z : ℍ) : ℂ := E₄ z ^ 3 / discriminant z

@[simp]
theorem j_apply (z : ℍ) : j z = E₄ z ^ 3 / discriminant z := by rfl

/-- The modular invariant is holomorphic on the upper half-plane. -/
theorem j_holo : MDiff j := by
  exact (ModularForm.holo' E₄).pow 3 |>.div (CuspForm.discriminant.holo') discriminant_ne_zero

/-- The weight factors cancel, so `j` is invariant under `SL₂(ℤ)`. -/
theorem j_smul (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have hγ : mapGL ℝ γ ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨γ, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' E₄ hγ z
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ z
  have hd : denom (mapGL ℝ γ) z ≠ 0 := denom_ne_zero _ _
  have hE' : E₄ (γ • z) = denom (mapGL ℝ γ) z ^ (4 : ℤ) * E₄ z := by
    simpa only [MulAction.compHom_smul_def] using hE
  have hΔ' : discriminant (γ • z) =
      denom (mapGL ℝ γ) z ^ (12 : ℤ) * discriminant z := by
    simpa only [MulAction.compHom_smul_def, CuspForm.coe_discriminant] using hΔ
  have hp : (denom (mapGL ℝ γ) z ^ (4 : ℤ)) ^ 3 =
      denom (mapGL ℝ γ) z ^ (12 : ℤ) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  rw [j_apply, j_apply, hE', hΔ']
  rw [mul_pow, hp]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ hd)

/-- The other standard expression for the modular invariant. -/
theorem j_sub_1728 (z : ℍ) : j z - 1728 = E₆ z ^ 2 / discriminant z := by
  have hΔ : (1728 : ℂ) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [j_apply]
  field_simp [discriminant_ne_zero z]
  linear_combination -hΔ

/-- The zero fibre of `j` is exactly the zero locus of `E₄`. -/
theorem j_eq_zero_iff (z : ℍ) : j z = 0 ↔ E₄ z = 0 := by
  simp [j_apply, discriminant_ne_zero z]

/-- The fibre of `j` above `1728` is exactly the zero locus of `E₆`. -/
theorem j_eq_1728_iff (z : ℍ) : j z = 1728 ↔ E₆ z = 0 := by
  rw [← sub_eq_zero, j_sub_1728]
  simp [discriminant_ne_zero z]

end TauCeti.ModularForm
