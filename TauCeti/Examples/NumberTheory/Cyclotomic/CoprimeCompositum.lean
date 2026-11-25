/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Cyclotomic.CoprimeCompositum

/-!
# Checks for cyclotomic fields of coprime orders

* `ℚ(ζ₄) ⊓ ℚ(ζ₃) = ℚ` and `ℚ(ζ₄) ⊔ ℚ(ζ₃) = ℚ(ζ₁₂)`.
* Coprimality is needed: `ℚ(ζ₄) ⊓ ℚ(ζ₈) = ℚ(ζ₄) = ℚ(i)`, which is not `ℚ`.
-/

namespace TauCeti.Examples.CyclotomicCoprimeCompositum

open IntermediateField TauCeti.Cyclotomic

example : complexField 4 ⊓ complexField 3 = ⊥ :=
  complexField_inf_eq_bot (by norm_num)

example : complexField 4 ⊔ complexField 3 = complexField 12 :=
  complexField_sup_eq (by norm_num)

example : complexField 4 ⊓ complexField 8 = ℚ⟮Complex.I⟯ := by
  have complexRoot_four : complexRoot 4 = Complex.I := by
    rw [complexRoot_def, show 2 * Real.pi * Complex.I / (4 : ℕ) = Real.pi / 2 * Complex.I by
      push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I
  rw [inf_eq_left.2 (complexField_le_of_dvd (by norm_num) (by norm_num)), complexField_def,
    complexRoot_four]

example : complexField 4 ⊓ complexField 8 ≠ ⊥ := by
  rw [inf_eq_left.2 (complexField_le_of_dvd (by norm_num) (by norm_num))]
  intro h
  have h4 : Module.finrank ℚ (complexField 4) = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank 4]
    decide
  rw [h, IntermediateField.finrank_bot] at h4
  exact absurd h4 (by norm_num)

end TauCeti.Examples.CyclotomicCoprimeCompositum
