/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
-- Proof-only: `Point.cast_some`, the coordinates of a point transported along `AddEquiv.cast`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# The isomorphism of point groups induced by a change of variables

An admissible change of variables `C : VariableChange F` induces a group isomorphism
`(C • W).toAffine.Point ≃+ W.toAffine.Point`, sending
`(x, y)` to `(u²x + r, u³y + u²sx + t)` and fixing the point at infinity.
Here `Point` consists of the nonsingular points, so the construction applies to every
Weierstrass curve over a field, including singular curves. It is computable given
`[DecidableEq F]`.

## Main definitions and results

* `WeierstrassCurve.Affine.Point.equivVariableChange`: the group isomorphism, with inverse
  induced by `C⁻¹`.
* `WeierstrassCurve.Affine.Point.equivVariableChange_some` and
  `WeierstrassCurve.Affine.Point.equivVariableChange_symm_some`: the forward and inverse
  coordinate formulas, both tagged `@[simp]`.

The underlying homomorphism is `(equivVariableChange W C).toAddMonoidHom`. Transport along
an equality of curves uses Mathlib's `AddEquiv.cast`; `Point.cast_some` describes its effect
on coordinates. These maps identify the point groups of different Weierstrass models and,
in particular, a quadratic twist with its original curve over a splitting field.

## Implementation notes

The coordinate map and its injectivity work over any commutative ring, since the scale `u`
is a unit. The group isomorphism uses the field-valued addition formulas from
`Affine/Formula/VariableChange.lean`. Nonsingularity is transported by
`variableChange_nonsingular`, without an ellipticity hypothesis. The private coordinate map
and homomorphism assemble the equivalence; its definition remains unexposed.

## References

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` at commit `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0), by Michael Stoll and Claude.
-/

public section

namespace WeierstrassCurve.Affine

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition (`negY`) only if the original pair does. This is the case split of the
addition formula, transported; it is what lets `add_some` be applied on both sides at once. -/
private lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : R}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : R) ^ 2 * x₁ + C.r = (C.u : R) ^ 2 * x₂ + C.r ∧
      (C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : R) ^ 2 * x₂ + C.r) ((C.u : R) ^ 3 * y₂ + (C.u : R) ^ 2 * C.s * x₂ + C.t)) := by
  rintro ⟨hX, hY⟩
  have hx : x₁ = x₂ := (C.u.isUnit.pow 2).mul_left_cancel (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, (C.u.isUnit.pow 3).mul_left_cancel (by linear_combination hY)⟩

namespace Point

/-- The underlying map `(C • W).Point → W.Point` of the change of variables, sending `0` to `0` and
`(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
private def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : R) ^ 2 * x + C.r)
      ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] private lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

private lemma mapVariableChangeFun_some {x y : R} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

private lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := (C.u.isUnit.pow 2).mul_left_cancel (by linear_combination hX)
    simp only [some.injEq]
    exact ⟨hx,
      (C.u.isUnit.pow 3).mul_left_cancel (by linear_combination hY - (C.u : R) ^ 2 * C.s * hx)⟩

end Point

end CommRing

namespace Point

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) (C : VariableChange F)

/-- The homomorphism on nonsingular points induced by the change of variables. -/
private def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addX, variableChange_addY]

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, with inverse coming from `C⁻¹`. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹
        (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
          (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · have hz : (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm) 0 = 0 := _root_.map_zero _
      rw [← zero_def, hz, mapVariableChangeFun_zero, mapVariableChangeFun_zero]
    · rw [cast_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      simp only [some.injEq]
      refine ⟨?_, ?_⟩ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹
      (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
        (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

/-- The forward coordinate formula for the change-of-variables isomorphism. -/
@[simp] lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) :=
  mapVariableChangeFun_some W C h

/-- The inverse is induced by `C⁻¹`, transported along `C⁻¹ • (C • W) = W`. -/
private lemma equivVariableChange_symm_apply (P : W.toAffine.Point) :
    (equivVariableChange W C).symm P
      = mapVariableChangeFun (C • W) C⁻¹
          (AddEquiv.cast (M := fun V : WeierstrassCurve F ↦ V.toAffine.Point)
            (inv_smul_smul C W).symm P) := rfl

/-- The inverse coordinate formula, given by the inverse change of variables. -/
@[simp] lemma equivVariableChange_symm_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (equivVariableChange W C).symm (.some x y h)
      = .some (((C⁻¹).u : F) ^ 2 * x + (C⁻¹).r)
          (((C⁻¹).u : F) ^ 3 * y + ((C⁻¹).u : F) ^ 2 * (C⁻¹).s * x + (C⁻¹).t)
          ((variableChange_nonsingular (C • W) C⁻¹ x y).mpr
            ((inv_smul_smul C W).symm ▸ h)) := by
  rw [equivVariableChange_symm_apply, cast_some, mapVariableChangeFun_some]

end Point

end WeierstrassCurve.Affine

end
