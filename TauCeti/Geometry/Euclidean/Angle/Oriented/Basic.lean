/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Oriented angles between three vectors with positive sign

For three nonzero vectors `x`, `y`, `z` of an oriented real inner product space of dimension two,
the oriented angles satisfy `oangle x y + oangle y z = oangle x z` (Mathlib's
`Orientation.oangle_add`). When all three angles have positive sign, i.e. lie in `(0, π)`, the
identity holds for their real representatives in `(-π, π]` as well
(`Orientation.oangle_toReal_add_of_sign_eq_one`, from Mathlib's
`Real.Angle.toReal_add_eq_toReal_add_toReal`), and the sign of `oangle y z` is the order of
the real angles of `y` and `z` measured from `x` (`Orientation.oangle_sign_eq_one_iff_toReal_lt`).
-/

public section

open Real

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
  (o : Orientation ℝ V (Fin 2))

/-- Three oriented angles of positive sign add as real numbers. -/
theorem oangle_toReal_add_of_sign_eq_one {x y z : V} (h₁ : (o.oangle x y).sign = 1)
    (h₂ : (o.oangle y z).sign = 1) (h₃ : (o.oangle x z).sign = 1) :
    (o.oangle x z).toReal = (o.oangle x y).toReal + (o.oangle y z).toReal := by
  have hπ : ∀ {θ : Real.Angle}, θ.sign = 1 → θ ≠ π := fun h hθ ↦ by
    rw [hθ, Real.Angle.sign_coe_pi] at h
    exact zero_ne_one h
  rw [← o.oangle_add (o.left_ne_zero_of_oangle_sign_eq_one h₁)
    (o.right_ne_zero_of_oangle_sign_eq_one h₁) (o.right_ne_zero_of_oangle_sign_eq_one h₂)] at h₃ ⊢
  exact Real.Angle.toReal_add_eq_toReal_add_toReal (hπ h₁) (hπ h₂) (.inr (h₁.trans h₃.symm))

/-- For two vectors `y`, `z` making positive oriented angles with `x`, the oriented angle from `y`
to `z` is positive exactly when the angle of `y` from `x` is smaller than that of `z`. -/
theorem oangle_sign_eq_one_iff_toReal_lt {x y z : V} (h₁ : (o.oangle x y).sign = 1)
    (h₂ : (o.oangle x z).sign = 1) :
    (o.oangle y z).sign = 1 ↔ (o.oangle x y).toReal < (o.oangle x z).toReal := by
  rw [← o.oangle_sub_left (o.left_ne_zero_of_oangle_sign_eq_one h₁)
    (o.right_ne_zero_of_oangle_sign_eq_one h₁) (o.right_ne_zero_of_oangle_sign_eq_one h₂)]
  obtain ⟨ha₀, haπ⟩ := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 h₁
  obtain ⟨hb₀, hbπ⟩ := Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 h₂
  have hreal : (o.oangle x z - o.oangle x y).toReal =
      (o.oangle x z).toReal - (o.oangle x y).toReal := by
    conv_lhs => rw [← Real.Angle.coe_toReal (o.oangle x z), ← Real.Angle.coe_toReal (o.oangle x y),
      ← Real.Angle.coe_sub]
    exact Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩
  rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos, hreal, Set.mem_Ioo, sub_pos, and_iff_left_iff_imp]
  exact fun _ ↦ by linarith

end Orientation
