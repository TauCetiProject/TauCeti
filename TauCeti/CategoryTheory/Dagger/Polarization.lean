/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Polarization identities in complex conjugate-linear dagger categories

In any complex conjugate-linear dagger category (`[DaggerLinear ℂ C]`), products of the form
`f ≫ dagger g` and `dagger f ≫ g` for parallel morphisms `f g : X ⟶ Y` are complex linear
combinations of self-daggers `h ≫ dagger h` and `dagger h ≫ h`. These purely algebraic
identities require no norm, completeness, or positivity structure.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] {X Y : C}

/-- Algebraic polarization identity expressing `4 • (f ≫ dagger g)` in terms of self-daggers
`h ≫ dagger h`. -/
theorem four_smul_comp_dagger (f g : X ⟶ Y) :
    (4 : ℂ) • (f ≫ dagger g) =
      (f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g)) -
        Complex.I • ((f - Complex.I • g) ≫ dagger (f - Complex.I • g)) := by
  simp only [dagger_add, dagger_sub, dagger_smul, Complex.star_def, Complex.conj_I,
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp, Preadditive.comp_sub,
    neg_smul, Preadditive.comp_neg, Linear.smul_comp, Linear.comp_smul, smul_add, smul_sub,
    smul_neg, smul_smul, Complex.I_mul_I]
  module

/-- Polarization identity expressing `f ≫ dagger g` in terms of self-daggers `h ≫ dagger h`. -/
theorem comp_dagger_eq_polarization (f g : X ⟶ Y) :
    f ≫ dagger g =
      (4 : ℂ)⁻¹ • ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g)) -
        Complex.I • ((f - Complex.I • g) ≫ dagger (f - Complex.I • g))) := by
  rw [← four_smul_comp_dagger, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- Algebraic polarization identity expressing `4 • (dagger f ≫ g)` in terms of self-daggers
`dagger h ≫ h`. -/
theorem four_smul_dagger_comp (f g : X ⟶ Y) :
    (4 : ℂ) • (dagger f ≫ g) =
      dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g)) +
        Complex.I • (dagger (f - Complex.I • g) ≫ (f - Complex.I • g)) := by
  simp only [dagger_add, dagger_sub, dagger_smul, Complex.star_def, Complex.conj_I,
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp, Preadditive.comp_sub,
    neg_smul, Preadditive.neg_comp, Linear.smul_comp, Linear.comp_smul, smul_add, smul_sub,
    smul_neg, smul_smul, Complex.I_mul_I]
  module

/-- Polarization identity expressing `dagger f ≫ g` in terms of self-daggers `dagger h ≫ h`. -/
theorem dagger_comp_eq_polarization (f g : X ⟶ Y) :
    dagger f ≫ g =
      (4 : ℂ)⁻¹ • (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g)) +
        Complex.I • (dagger (f - Complex.I • g) ≫ (f - Complex.I • g))) := by
  rw [← four_smul_dagger_comp, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

end TauCeti
