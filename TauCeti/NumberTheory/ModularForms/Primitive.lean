/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Primitives and the modular slash action

This file records how primitives on the upper half-plane transform under the modular slash
action: pulling a primitive of `F` back along the Möbius transformation `z ↦ g • z` gives a
primitive of the weight-`2` slash `F ∣[2] g`. This is what lets a single primitive of `F` compute
the integrals of `F(z) dz` along all geodesics `g • (0, i∞)` at once, by comparing its limits at
the transformed cusps `g • 0` and `g • ∞`; see
`TauCeti.NumberTheory.ModularForms.GeodesicIntegral.BetweenCusps`.
-/

public section

open Complex Matrix.GeneralLinearGroup UpperHalfPlane
open scoped ModularForm

namespace TauCeti

/-- **Primitives pull back along Möbius transformations.** If `Φ` is a primitive of `F` on `ℍ`,
then `z ↦ Φ (g • z)` is a primitive of the weight-`2` slash `F ∣[2] g`, for `g` of positive
determinant: the weight-`2` automorphy factor `det g · (cz + d)⁻²` is the derivative of
`z ↦ g • z`. -/
theorem hasDerivAt_comp_smul {F : ℍ → ℂ} {Φ : ℂ → ℂ}
    (hΦ : ∀ z : ℍ, HasDerivAt Φ (F z) z) {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : ℍ) :
    HasDerivAt (fun z ↦ Φ (g • ofComplex z : ℍ)) ((F ∣[(2 : ℤ)] g) τ) τ := by
  have h := (hΦ (g • τ)).comp_of_eq (τ : ℂ) (hasStrictDerivAt_smul hg τ).hasDerivAt
    (by rw [ofComplex_apply])
  refine h.congr_deriv ?_
  have hden : denom g τ ≠ 0 := denom_ne_zero g τ
  rw [ModularForm.slash_apply_of_det_pos 2 hg, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hg]
  push_cast
  field_simp

end TauCeti
