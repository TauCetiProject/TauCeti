/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# The isomorphism of point groups induced by a change of variables

An admissible change of variables `C : VariableChange R` over a commutative ring induces a
bijection `(C • W).toAffine.Point ≃ W.toAffine.Point` of nonsingular points, sending
`(x, y)` to `(u²x + r, u³y + u²sx + t)` and fixing the point at infinity, with inverse
induced by `C⁻¹`. Over a field it is a group isomorphism. No ellipticity hypothesis is needed,
so this applies to the nonsingular points of singular Weierstrass curves as well.

## Main definitions and results

* `WeierstrassCurve.Affine.Point.equivVariableChange`: the bijection of nonsingular points, over
  a commutative ring.
* `WeierstrassCurve.Affine.Point.equivVariableChange_some` and
  `WeierstrassCurve.Affine.Point.equivVariableChange_symm_some`: the forward and inverse
  coordinate formulas; `WeierstrassCurve.Affine.Point.equivVariableChange_zero` and
  `WeierstrassCurve.Affine.Point.equivVariableChange_symm_zero`: both fix the point at
  infinity. All four are tagged `@[simp]`.
* `WeierstrassCurve.Affine.Point.addEquivVariableChange`: the group isomorphism over a field
  with decidable equality, whose underlying functions are given by
  `WeierstrassCurve.Affine.Point.coe_addEquivVariableChange` and
  `WeierstrassCurve.Affine.Point.coe_addEquivVariableChange_symm`.
* `WeierstrassCurve.pointEquivVariableChange`: for `W` and `C` over a commutative ring `R` and a
  field `L` over `R`, the group isomorphism between the points over `L` of `C • W` and of `W`, that
  is `((C • W).baseChange L).toAffine.Point ≃+ (W.baseChange L).toAffine.Point`, with its coordinate
  lemmas `pointEquivVariableChange_some` and `pointEquivVariableChange_symm_some`.
* `WeierstrassCurve.map_pointEquivVariableChange` and
  `WeierstrassCurve.map_pointEquivVariableChange_symm`: this group isomorphism is natural in `L`,
  commuting with `WeierstrassCurve.Affine.Point.map` along `R`-algebra homomorphisms.

These maps identify the point groups of different Weierstrass models and, in particular, a
quadratic twist with its original curve over a splitting field.

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

/-- The inverse map `W.Point → (C • W).Point`, induced by `C⁻¹` via `C⁻¹ • (C • W) = W`. -/
private def mapVariableChangeInvFun (P : W.toAffine.Point) : (C • W).toAffine.Point :=
  mapVariableChangeFun (C • W) C⁻¹
    (Equiv.cast (congrArg (fun V : WeierstrassCurve R ↦ V.toAffine.Point)
      (inv_smul_smul C W).symm) P)

private lemma mapVariableChangeInvFun_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapVariableChangeInvFun W C (.some x y h)
      = .some (((C⁻¹).u : R) ^ 2 * x + (C⁻¹).r)
          (((C⁻¹).u : R) ^ 3 * y + ((C⁻¹).u : R) ^ 2 * (C⁻¹).s * x + (C⁻¹).t)
          ((variableChange_nonsingular (C • W) C⁻¹ x y).mpr
            ((inv_smul_smul C W).symm ▸ h)) := by
  rw [mapVariableChangeInvFun, Equiv.cast_apply, cast_some (inv_smul_smul C W).symm,
    mapVariableChangeFun_some]

private lemma mapVariableChangeFun_mapVariableChangeInvFun (P : W.toAffine.Point) :
    mapVariableChangeFun W C (mapVariableChangeInvFun W C P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [mapVariableChangeInvFun, ← zero_def, Equiv.cast_apply,
      cast_zero (inv_smul_smul C W).symm, mapVariableChangeFun_zero, mapVariableChangeFun_zero]
  · have hu : (C.u : R) * ((C.u⁻¹ : Rˣ) : R) = 1 := C.u.mul_inv
    rw [mapVariableChangeInvFun_some, mapVariableChangeFun_some]
    simp only [some.injEq, VariableChange.inv_def]
    set a := (C.u : R) * ((C.u⁻¹ : Rˣ) : R)
    exact ⟨by linear_combination (a + 1) * (x - C.r) * hu,
      by linear_combination ((a ^ 2 + a + 1) * (y - C.s * x + C.r * C.s - C.t)
        + (a + 1) * (C.s * x - C.s * C.r)) * hu⟩

/-- The bijection `(C • W).Point ≃ W.Point` of nonsingular points induced by the admissible
change of variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, with inverse coming from `C⁻¹`. -/
def equivVariableChange : (C • W).toAffine.Point ≃ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  invFun := mapVariableChangeInvFun W C
  left_inv := Function.RightInverse.leftInverse_of_injective
    (mapVariableChangeFun_mapVariableChangeInvFun W C) (mapVariableChangeFun_injective W C)
  right_inv := mapVariableChangeFun_mapVariableChangeInvFun W C

/-- The forward coordinate formula for the change-of-variables bijection. -/
@[simp] lemma equivVariableChange_some {x y : R} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) :=
  mapVariableChangeFun_some W C h

/-- The change-of-variables bijection fixes the point at infinity. -/
@[simp] lemma equivVariableChange_zero : equivVariableChange W C 0 = 0 :=
  mapVariableChangeFun_zero W C

/-- The inverse of the change-of-variables bijection fixes the point at infinity. -/
@[simp] lemma equivVariableChange_symm_zero : (equivVariableChange W C).symm 0 = 0 :=
  (Equiv.symm_apply_eq _).2 (equivVariableChange_zero W C).symm

private lemma equivVariableChange_symm_apply (P : W.toAffine.Point) :
    (equivVariableChange W C).symm P = mapVariableChangeInvFun W C P := rfl

/-- The inverse coordinate formula, given by the inverse change of variables. -/
@[simp] lemma equivVariableChange_symm_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    (equivVariableChange W C).symm (.some x y h)
      = .some (((C⁻¹).u : R) ^ 2 * x + (C⁻¹).r)
          (((C⁻¹).u : R) ^ 3 * y + ((C⁻¹).u : R) ^ 2 * (C⁻¹).s * x + (C⁻¹).t)
          ((variableChange_nonsingular (C • W) C⁻¹ x y).mpr
            ((inv_smul_smul C W).symm ▸ h)) := by
  rw [equivVariableChange_symm_apply, mapVariableChangeInvFun_some]

end Point

end CommRing

namespace Point

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) (C : VariableChange F)

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables; its underlying bijection is `equivVariableChange`. -/
def addEquivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  __ := equivVariableChange W C
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [Equiv.toFun_as_coe, equivVariableChange_some]
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, equivVariableChange_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C h₁.1 h₂.1 hxy, variableChange_addX, variableChange_addY]

private lemma addEquivVariableChange_apply (P : (C • W).toAffine.Point) :
    addEquivVariableChange W C P = equivVariableChange W C P := rfl

private lemma addEquivVariableChange_symm_apply (P : W.toAffine.Point) :
    (addEquivVariableChange W C).symm P = (equivVariableChange W C).symm P := rfl

/-- The group isomorphism `addEquivVariableChange` has underlying function
`equivVariableChange`. -/
@[simp] lemma coe_addEquivVariableChange :
    ⇑(addEquivVariableChange W C) = equivVariableChange W C :=
  funext (addEquivVariableChange_apply W C)

/-- The inverse of the group isomorphism `addEquivVariableChange` has underlying function the
inverse of `equivVariableChange`. -/
@[simp] lemma coe_addEquivVariableChange_symm :
    ⇑(addEquivVariableChange W C).symm = (equivVariableChange W C).symm :=
  funext (addEquivVariableChange_symm_apply W C)

end Point

end WeierstrassCurve.Affine

namespace WeierstrassCurve

/-! ### Curves over a ring and their points over a field -/

section BaseChange

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (L : Type*) [Field L] [DecidableEq L]
  [Algebra R L] (C : VariableChange R)

/-- **The points over `L` of `C • W` and of `W` are identified by a change of variables `C` over
`R`**: the group isomorphism `(x, y) ↦ (u²x + r, u³y + u²sx + t)` between the points of their base
changes to a field `L`. It is `WeierstrassCurve.Affine.Point.addEquivVariableChange` for the base
change of `C` to `L`, read on the base change of `C • W`. -/
def pointEquivVariableChange :
    ((C • W).baseChange L).toAffine.Point ≃+ (W.baseChange L).toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve L ↦ V.toAffine.Point)
    (baseChange_smul_baseChange L C W).symm).trans
    (Affine.Point.addEquivVariableChange (W.baseChange L) (C.baseChange L))

/-- What the identification `pointEquivVariableChange` does to a point given by coordinates: it is
the change of variables `C`, base changed to `L`. -/
@[simp]
theorem pointEquivVariableChange_some {x y : L}
    (h : ((C • W).baseChange L).toAffine.Nonsingular x y) :
    W.pointEquivVariableChange L C (.some x y h) =
      .some (((C.baseChange L).u : L) ^ 2 * x + (C.baseChange L).r)
        (((C.baseChange L).u : L) ^ 3 * y + ((C.baseChange L).u : L) ^ 2 * (C.baseChange L).s * x +
          (C.baseChange L).t)
        ((Affine.variableChange_nonsingular (W.baseChange L) (C.baseChange L) x y).mpr
          ((baseChange_smul_baseChange L C W).symm ▸ h)) := by
  rw [pointEquivVariableChange, AddEquiv.trans_apply, AddEquiv.cast_apply,
    Affine.Point.cast_some (baseChange_smul_baseChange L C W).symm,
    Affine.Point.coe_addEquivVariableChange,
    Affine.Point.equivVariableChange_some]

/-- What the inverse of the identification `pointEquivVariableChange` does to a point given by
coordinates: it is the change of variables `C⁻¹`, base changed to `L`. -/
@[simp]
theorem pointEquivVariableChange_symm_some {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) :
    (W.pointEquivVariableChange L C).symm (.some x y h) =
      .some (((C.baseChange L)⁻¹.u : L) ^ 2 * x + (C.baseChange L)⁻¹.r)
        (((C.baseChange L)⁻¹.u : L) ^ 3 * y +
          ((C.baseChange L)⁻¹.u : L) ^ 2 * (C.baseChange L)⁻¹.s * x + (C.baseChange L)⁻¹.t)
        (baseChange_smul_baseChange L C W ▸
          (Affine.variableChange_nonsingular (C.baseChange L • W.baseChange L)
            (C.baseChange L)⁻¹ x y).mpr
            ((inv_smul_smul (C.baseChange L) (W.baseChange L)).symm ▸ h)) := by
  rw [pointEquivVariableChange, AddEquiv.symm_trans_apply,
    Affine.Point.coe_addEquivVariableChange_symm,
    Affine.Point.equivVariableChange_symm_some, AddEquiv.symm_apply_eq, AddEquiv.cast_apply,
    Affine.Point.cast_some (baseChange_smul_baseChange L C W).symm]

/-- **The identification `pointEquivVariableChange` is natural in the field of coordinates**: it
commutes with moving points along an `R`-algebra homomorphism `f : K → L`, since the change of
variables has its coefficients in `R`. -/
theorem map_pointEquivVariableChange {K : Type*} [Field K] [DecidableEq K] [Algebra R K]
    (f : K →ₐ[R] L) (P : ((C • W).baseChange K).toAffine.Point) :
    Affine.Point.map f (W.pointEquivVariableChange K C P) =
      W.pointEquivVariableChange L C (Affine.Point.map f P) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · simp [Affine.Point.map_some, VariableChange.baseChange]

/-- The inverse of `pointEquivVariableChange` commutes with moving points along an `R`-algebra
homomorphism of the fields of coordinates. -/
theorem map_pointEquivVariableChange_symm {K : Type*} [Field K] [DecidableEq K] [Algebra R K]
    (f : K →ₐ[R] L) (P : (W.baseChange K).toAffine.Point) :
    Affine.Point.map f ((W.pointEquivVariableChange K C).symm P) =
      (W.pointEquivVariableChange L C).symm (Affine.Point.map f P) := by
  rw [AddEquiv.eq_symm_apply, ← map_pointEquivVariableChange, AddEquiv.apply_symm_apply]

end BaseChange

end WeierstrassCurve

end
