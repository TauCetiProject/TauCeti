/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.NumberTheory.NumberField.CMType.GaussianRationals
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Norm

/-!
# The reflex norm of `ℚ(i)`

For `E = ℚ(i)` and `Φ = {i ↦ I}`, the reflex field is `ℚ(I) ⊆ ℂ` and the reflex norm
`N_Φ : E* → E` inverts the selected embedding: `N_Φ(φ c) = c` (`reflexNorm_Φ`), so
`N_Φ(2 + I) = 2 + i` (`reflexNorm_Φ_two_add_I`). For the complementary type `ιΦ = {i ↦ -I}`,
`N_{ιΦ}(2 + I) = 2 - i`, not `2 + i` (`reflexNorm_star_Φ_two_add_I`,
`reflexNorm_star_Φ_two_add_I_ne`): conjugating the type conjugates the norm.
-/

public section

namespace TauCeti.GaussianRationalsCMType

theorem φ_two_add_ζ : φ (2 + ζ) = 2 + Complex.I := by
  simp [map_ofNat]

theorem star_φ_two_sub_ζ : star φ (2 - ζ) = 2 + Complex.I := by
  simp [RingHom.star_apply, map_sub, φ_ζ, map_ofNat]

theorem coe_star_Φ : ((star Φ : CMType K) : Set (K →+* ℂ)) = {star φ} := by
  rw [CMType.coe_star_eq_image, coe_Φ, Set.image_singleton]

/-- **`N_Φ` inverts the selected embedding** `φ : i ↦ I`. -/
theorem reflexNorm_Φ (c : K) :
    Φ.reflexNorm le_rfl ⟨φ c, CMType.typeTrace_eq_of_coe_eq_singleton coe_Φ c ▸
      Φ.typeTrace_mem_reflexField c⟩ = c :=
  CMType.reflexNorm_apply_of_coe_eq_singleton coe_Φ c

/-- **The Check `N_Φ(2 + I) = 2 + i`.** -/
theorem reflexNorm_Φ_two_add_I (h : 2 + Complex.I ∈ Φ.reflexField) :
    Φ.reflexNorm le_rfl ⟨2 + Complex.I, h⟩ = 2 + ζ := by
  convert reflexNorm_Φ (2 + ζ) using 3
  exact φ_two_add_ζ.symm

/-- **The Check `N_{ιΦ}(2 + I) = 2 - i`.** -/
theorem reflexNorm_star_Φ_two_add_I (h : 2 + Complex.I ∈ (star Φ).reflexField) :
    (star Φ).reflexNorm le_rfl ⟨2 + Complex.I, h⟩ = 2 - ζ := by
  convert CMType.reflexNorm_apply_of_coe_eq_singleton coe_star_Φ (2 - ζ) using 3
  exact star_φ_two_sub_ζ.symm

/-- Conjugating the type conjugates the norm: `N_{ιΦ}(2 + I) ≠ 2 + i`. -/
theorem reflexNorm_star_Φ_two_add_I_ne (h : 2 + Complex.I ∈ (star Φ).reflexField) :
    (star Φ).reflexNorm le_rfl ⟨2 + Complex.I, h⟩ ≠ 2 + ζ := by
  rw [reflexNorm_star_Φ_two_add_I]
  intro hne
  have : φ ζ = 0 := by
    have := congrArg φ hne
    simp only [map_sub, map_add] at this
    linear_combination -this / 2
  simp at this

end TauCeti.GaussianRationalsCMType
