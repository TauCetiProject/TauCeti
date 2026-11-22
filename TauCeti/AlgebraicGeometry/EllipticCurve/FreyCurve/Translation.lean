/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
import Mathlib.Algebra.CubicDiscriminant

/-!
# Translation to a Frey curve

A Weierstrass equation in the form `y² = (x - e₀)(x - e₁)(x - e₂)` over a commutative
ring becomes a Frey curve after translating the first root to the origin. This coefficient
calculation does not require ellipticity or distinctness of the roots.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve

/-- Translating the first root of the split cubic to the origin gives the Frey equation with
ordered roots `0`, `e₁ - e₀`, `e₂ - e₀`. No distinctness assumption is needed for this
coefficient identity. -/
theorem translate_smul_eq_freyCurve_of_f_eq_prod {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) [W.IsCharNeTwoNF] {e₀ e₁ e₂ : R}
    (h : W.toAffine.f = (X - C e₀) * (X - C e₁) * (X - C e₂)) :
    (⟨1, e₀, 0, 0⟩ : VariableChange R) • W = freyCurve (e₁ - e₀) (e₀ - e₂) := by
  have hpoly : (⟨1, W.a₂, W.a₄, W.a₆⟩ : Cubic R).toPoly = W.toAffine.f := by
    simp only [Cubic.toPoly, C_1, one_mul, Affine.f]
  rw [← hpoly, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at h
  simp only [Cubic.mk.injEq, true_and] at h
  obtain ⟨ha₂, ha₄, ha₆⟩ := h
  ext <;>
    simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, ha₂, ha₄, ha₆] <;> ring

end WeierstrassCurve
