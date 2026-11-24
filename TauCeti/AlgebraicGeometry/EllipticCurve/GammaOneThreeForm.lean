/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The `Γ₁(3)` normal form `Y² + a₁XY + a₃Y = X³`

A Weierstrass curve over a field with a point `P` of exact order `3` can be moved by a change of
variables so that `P = (0, 0)` with tangent line `Y = 0` there; since `P` is a flex, the curve
then has the form `Y² + a₁XY + a₃Y = X³`, that is, `a₂ = a₄ = a₆ = 0`
(`WeierstrassCurve.gammaOneThreeForm`). This is the form in which curves with a `Γ₁(3)`-structure
enter the `2`-local computation of the homotopy of `tmf`.

This file records its coefficients, its invariants

  `c₄ = a₁⁴ - 24a₁a₃`, `c₆ = -a₁⁶ + 36a₁³a₃ - 216a₃²`, `Δ = a₁³a₃³ - 27a₃⁴`,

with Mathlib's sign conventions, its base change, and the coefficients of its image under a
coordinate change `(1, r, s, t)`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
-/

public section

namespace WeierstrassCurve

variable {B : Type*} [CommRing B]

/-- The Weierstrass curve `Y² + a₁XY + a₃Y = X³`, with `a₂ = a₄ = a₆ = 0`. Over a field, a curve
with a point `P` of exact order `3` can be moved to this form with `P = (0, 0)` and flex tangent
`Y = 0`. -/
def gammaOneThreeForm (a₁ a₃ : B) : WeierstrassCurve B where
  a₁ := a₁
  a₂ := 0
  a₃ := a₃
  a₄ := 0
  a₆ := 0

variable (a₁ a₃ : B)

@[simp] theorem gammaOneThreeForm_a₁ : (gammaOneThreeForm a₁ a₃).a₁ = a₁ := (rfl)
@[simp] theorem gammaOneThreeForm_a₂ : (gammaOneThreeForm a₁ a₃).a₂ = 0 := (rfl)
@[simp] theorem gammaOneThreeForm_a₃ : (gammaOneThreeForm a₁ a₃).a₃ = a₃ := (rfl)
@[simp] theorem gammaOneThreeForm_a₄ : (gammaOneThreeForm a₁ a₃).a₄ = 0 := (rfl)
@[simp] theorem gammaOneThreeForm_a₆ : (gammaOneThreeForm a₁ a₃).a₆ = 0 := (rfl)

/-- The invariant `c₄` of `Y² + a₁XY + a₃Y = X³`. -/
@[simp]
theorem gammaOneThreeForm_c₄ : (gammaOneThreeForm a₁ a₃).c₄ = a₁ ^ 4 - 24 * a₁ * a₃ := by
  simp only [c₄, b₂, b₄, gammaOneThreeForm_a₁, gammaOneThreeForm_a₂, gammaOneThreeForm_a₃,
    gammaOneThreeForm_a₄]
  ring

/-- The invariant `c₆` of `Y² + a₁XY + a₃Y = X³`. -/
@[simp]
theorem gammaOneThreeForm_c₆ :
    (gammaOneThreeForm a₁ a₃).c₆ = -a₁ ^ 6 + 36 * a₁ ^ 3 * a₃ - 216 * a₃ ^ 2 := by
  simp only [c₆, b₂, b₄, b₆, gammaOneThreeForm_a₁, gammaOneThreeForm_a₂, gammaOneThreeForm_a₃,
    gammaOneThreeForm_a₄, gammaOneThreeForm_a₆]
  ring

/-- The discriminant of `Y² + a₁XY + a₃Y = X³`. -/
@[simp]
theorem gammaOneThreeForm_Δ : (gammaOneThreeForm a₁ a₃).Δ = a₁ ^ 3 * a₃ ^ 3 - 27 * a₃ ^ 4 := by
  simp only [Δ, b₂, b₄, b₆, b₈, gammaOneThreeForm_a₁, gammaOneThreeForm_a₂, gammaOneThreeForm_a₃,
    gammaOneThreeForm_a₄, gammaOneThreeForm_a₆]
  ring

/-- Base change of `Y² + a₁XY + a₃Y = X³` along `φ`. -/
@[simp]
theorem map_gammaOneThreeForm {C : Type*} [CommRing C] (φ : B →+* C) :
    (gammaOneThreeForm a₁ a₃).map φ = gammaOneThreeForm (φ a₁) (φ a₃) := by
  ext <;> simp [gammaOneThreeForm]

section VariableChange

variable (r s t : B)

/-- The coefficient `a₁` of the image of `Y² + a₁XY + a₃Y = X³` under `(1, r, s, t)`. -/
theorem variableChange_gammaOneThreeForm_a₁ :
    ((⟨1, r, s, t⟩ : VariableChange B) • gammaOneThreeForm a₁ a₃).a₁ = a₁ + 2 * s := by
  simp [variableChange_a₁]

/-- The coefficient `a₂` of the image of `Y² + a₁XY + a₃Y = X³` under `(1, r, s, t)`. -/
theorem variableChange_gammaOneThreeForm_a₂ :
    ((⟨1, r, s, t⟩ : VariableChange B) • gammaOneThreeForm a₁ a₃).a₂ = 3 * r - s ^ 2 - s * a₁ := by
  simp [variableChange_a₂]
  ring

/-- The coefficient `a₃` of the image of `Y² + a₁XY + a₃Y = X³` under `(1, r, s, t)`. -/
theorem variableChange_gammaOneThreeForm_a₃ :
    ((⟨1, r, s, t⟩ : VariableChange B) • gammaOneThreeForm a₁ a₃).a₃ = a₃ + r * a₁ + 2 * t := by
  simp [variableChange_a₃]

/-- The coefficient `a₄` of the image of `Y² + a₁XY + a₃Y = X³` under `(1, r, s, t)`. -/
theorem variableChange_gammaOneThreeForm_a₄ :
    ((⟨1, r, s, t⟩ : VariableChange B) • gammaOneThreeForm a₁ a₃).a₄ =
      -(s * a₃) - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t := by
  simp [variableChange_a₄]

/-- The coefficient `a₆` of the image of `Y² + a₁XY + a₃Y = X³` under `(1, r, s, t)`. -/
theorem variableChange_gammaOneThreeForm_a₆ :
    ((⟨1, r, s, t⟩ : VariableChange B) • gammaOneThreeForm a₁ a₃).a₆ =
      r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁ := by
  simp [variableChange_a₆]

end VariableChange

end WeierstrassCurve
