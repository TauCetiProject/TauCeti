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

-- A simp attribute here would make the `j_smul` and fibre simp lemmas fail `simpNF`.
theorem j_apply (z : ℍ) : j z = E₄ z ^ 3 / discriminant z := by rfl

/-- The modular invariant is holomorphic on the upper half-plane. -/
theorem j_mdifferentiable : MDiff j := by
  exact (ModularForm.holo' E₄).pow 3 |>.div (CuspForm.discriminant.holo') discriminant_ne_zero

-- A direct-action `@[simp]` variant fails `simpNF`:
-- `ModularGroup.sl_moeb` simplifies its left side.
/-- The weight factors cancel, so `j` is invariant under `SL₂(ℤ)`. -/
@[simp]
theorem j_smul (γ : SL(2, ℤ)) (z : ℍ) :
    j ((map (Int.castRingHom ℝ) γ) • z) = j z := by
  have hγ : mapGL ℝ γ ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨γ, rfl⟩
  have hE : (⇑(E₄.pow 3) ∣[(12 : ℤ)] (mapGL ℝ γ)) = ⇑(E₄.pow 3) := by
    simpa using SlashInvariantForm.slash_action_eqn (E₄.pow 3) _ hγ
  have hΔ : (⇑CuspForm.discriminant ∣[(12 : ℤ)] (mapGL ℝ γ)) =
      ⇑CuspForm.discriminant := by
    simpa using SlashInvariantForm.slash_action_eqn CuspForm.discriminant _ hγ
  have h : (⇑(E₄.pow 3) / ⇑CuspForm.discriminant) ∣[(12 : ℤ) - 12] γ =
      ⇑(E₄.pow 3) / ⇑CuspForm.discriminant := by
    rw [div_slash_SL2]
    -- The `SL₂` slash action uses `mapGL ℝ γ` definitionally, as in `hE` and `hΔ`.
    change (⇑(E₄.pow 3) ∣[(12 : ℤ)] (mapGL ℝ γ)) /
      (⇑CuspForm.discriminant ∣[(12 : ℤ)] (mapGL ℝ γ)) = _
    rw [hE, hΔ]
  have hpow (w : ℍ) : (E₄.pow 3) w = E₄ w ^ 3 := by
    exact congrFun (ModularForm.coe_pow E₄ 3) w
  have hz := congrFun h z
  have hinv : j (γ • z) = j z := by
    simpa [SL_slash_apply, j, hpow] using hz
  have hAction : (map (Int.castRingHom ℝ) γ) • z = γ • z := by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    have hMap : mapGL ℝ (map (Int.castRingHom ℝ) γ) = mapGL ℝ γ := by
      ext i j
      simp [mapGL_coe_matrix]
    exact congrArg (· • z) hMap
  rw [hAction]
  exact hinv

/-- The identity `j - 1728 = E₆² / Δ`. -/
theorem j_sub_1728 (z : ℍ) : j z - 1728 = E₆ z ^ 2 / discriminant z := by
  have hΔ : (1728 : ℂ) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [j_apply]
  field_simp [discriminant_ne_zero z]
  linear_combination -hΔ

/-- The zero fibre of `j` is exactly the zero locus of `E₄`. -/
@[simp]
theorem j_eq_zero_iff (z : ℍ) : j z = 0 ↔ E₄ z = 0 := by
  simp [j_apply, discriminant_ne_zero z]

/-- The fibre of `j` above `1728` is exactly the zero locus of `E₆`. -/
@[simp]
theorem j_eq_1728_iff (z : ℍ) : j z = 1728 ↔ E₆ z = 0 := by
  rw [← sub_eq_zero, j_sub_1728]
  simp [discriminant_ne_zero z]

end TauCeti.ModularForm
