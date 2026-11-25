/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The Cauchy transform commutes with rotations

Multiplication by a complex number `c` of modulus one is a rotation of `ℂ`, so it preserves
Lebesgue measure (`Complex.integral_comp_mul_left_of_norm_eq_one`). Substituting `c z` for `z` in
the Cauchy integral `T f(w) = π⁻¹ ∫ (w - z)⁻¹ f(z) dz` gives

`T (f ∘ (c ·))(w) = c T f(c w)`

(`TauCeti.cauchyTransform_comp_mul_left`). Equivalently, `T` intertwines the action
`f ↦ c⁻¹ f(c ·)` of the circle group on sources with the action `g ↦ g(c ·)` on solutions of
`\bar∂ g = f`, as it must, since `\bar∂ (g(c ·)) = conj c (\bar∂ g)(c ·)`
(`TauCeti.conjWirtingerDeriv_comp_mul_left`) and `conj c = c⁻¹`.
This is the symmetry behind rotation-equivariant constructions with the Cauchy transform, such as
pseudoholomorphic discs normalized by their first jet.
-/

public section

open MeasureTheory

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The Cauchy transform commutes with rotations.** For `‖c‖ = 1`,
`T (f ∘ (c ·))(w) = c T f(c w)`. No integrability of `f` is needed: both sides use the same
integral up to the measure-preserving substitution `z ↦ c z`. -/
theorem cauchyTransform_comp_mul_left {c : ℂ} (hc : ‖c‖ = 1) (f : ℂ → F) (w : ℂ) :
    cauchyTransform (fun z ↦ f (c * z)) w = c • cauchyTransform f (c * w) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have h : ∀ z : ℂ, (w - z)⁻¹ • f (c * z) = c • ((c * w - c * z)⁻¹ • f (c * z)) := fun z ↦ by
    rw [smul_smul, ← mul_sub, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [cauchyTransform_apply, cauchyTransform_apply, smul_comm c, funext h, integral_smul,
    Complex.integral_comp_mul_left_of_norm_eq_one hc fun z ↦ (c * w - z)⁻¹ • f z]

end TauCeti
