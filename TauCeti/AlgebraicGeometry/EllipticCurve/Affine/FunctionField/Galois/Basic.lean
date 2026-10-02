/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRingMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois

/-!
# Galois actions on function fields of Weierstrass curves

Let `W` be a Weierstrass curve over a field `F`, and let `K/F` be a field extension. Every
`F`-automorphism of `K` acts semilinearly on the function field of `W_K`: it applies the
automorphism to coefficients and fixes the coordinate functions `x` and `y`. This file extends the
coordinate-ring action `WeierstrassCurve.coordinateRingGaloisAction` to the function field and
proves its identity and composition laws.

The action on functions, together with the action on points, enters the proof of Galois
equivariance of the Weil pairing; the compatibility with translation proved here, conjugating
translation by `P` to translation by the conjugate point, is the function-side half of that
argument.

## Main definitions

* `WeierstrassCurve.functionFieldGaloisAction`: the action on the function field.

## Main results

* `WeierstrassCurve.functionFieldGaloisAction_algebraMap`: the action is semilinear on
  constants.
* `WeierstrassCurve.functionFieldGaloisAction_genericX` and
  `WeierstrassCurve.functionFieldGaloisAction_genericY`: the two coordinate functions are fixed.
* `WeierstrassCurve.functionFieldGaloisAction_map_algebraMap`: every function defined over the
  ground field is fixed.
* `WeierstrassCurve.functionFieldGaloisAction_translation`: on an elliptic curve, the action
  intertwines translation by a point with translation by its Galois conjugate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

/-- **The Galois action on the function field of a base-changed Weierstrass curve.** It is the
unique extension of `coordinateRingGaloisAction` to the fraction field. -/
noncomputable def functionFieldGaloisAction :
    (K ≃ₐ[F] K) →* ((W⁄K).toAffine.FunctionField ≃+* (W⁄K).toAffine.FunctionField) :=
  (IsFractionRing.ringEquivOfRingEquivHom (W⁄K).toAffine.CoordinateRing
    (W⁄K).toAffine.FunctionField).comp (coordinateRingGaloisAction W)

/-- The inverse function-field action is the action of the inverse coefficient automorphism. -/
@[simp]
theorem functionFieldGaloisAction_symm (σ : K ≃ₐ[F] K) :
    (functionFieldGaloisAction W σ).symm = functionFieldGaloisAction W σ.symm :=
  (map_inv (functionFieldGaloisAction W) σ).symm

/-- The function-field action restricts to the coordinate-ring action. -/
@[simp]
theorem functionFieldGaloisAction_algebraMap_coordinateRing (σ : K ≃ₐ[F] K)
    (z : (W⁄K).toAffine.CoordinateRing) :
    functionFieldGaloisAction W σ
        (algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField z) =
      algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField
        (coordinateRingGaloisAction W σ z) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ z

/-- The function-field action on the class of a polynomial applies the automorphism to its
coefficients. -/
theorem functionFieldGaloisAction_algebraMap_mk (σ : K ≃ₐ[F] K) (p : K[X][Y]) :
    functionFieldGaloisAction W σ
        (algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField
          (Affine.CoordinateRing.mk _ p)) =
      algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField
        (Affine.CoordinateRing.mk _ (p.map (mapRingHom σ))) := by
  rw [functionFieldGaloisAction_algebraMap_coordinateRing, coordinateRingGaloisAction_mk]

/-- The function-field action applies the field automorphism to constants. -/
@[simp]
theorem functionFieldGaloisAction_algebraMap (σ : K ≃ₐ[F] K) (a : K) :
    functionFieldGaloisAction W σ
        (algebraMap K (W⁄K).toAffine.FunctionField a) =
      algebraMap K (W⁄K).toAffine.FunctionField (σ a) := by
  rw [IsScalarTower.algebraMap_apply K (W⁄K).toAffine.CoordinateRing
    (W⁄K).toAffine.FunctionField, functionFieldGaloisAction_algebraMap_coordinateRing,
    coordinateRingGaloisAction_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The function-field action fixes the generic `x`-coordinate. -/
@[simp]
theorem functionFieldGaloisAction_genericX (σ : K ≃ₐ[F] K) :
    functionFieldGaloisAction W σ (W⁄K).toAffine.genericX = (W⁄K).toAffine.genericX := by
  rw [Affine.genericX_def, functionFieldGaloisAction_algebraMap_mk, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_X]

/-- The function-field action fixes the generic `y`-coordinate. -/
@[simp]
theorem functionFieldGaloisAction_genericY (σ : K ≃ₐ[F] K) :
    functionFieldGaloisAction W σ (W⁄K).toAffine.genericY = (W⁄K).toAffine.genericY := by
  rw [Affine.genericY_def, functionFieldGaloisAction_algebraMap_mk, Polynomial.map_X]

/-- **The Galois action fixes the function field defined over the ground field.** -/
@[simp]
theorem functionFieldGaloisAction_map_algebraMap (σ : K ≃ₐ[F] K)
    (z : W.toAffine.FunctionField) :
    functionFieldGaloisAction W σ
        (Affine.FunctionField.map W.toAffine (algebraMap F K) z) =
      Affine.FunctionField.map W.toAffine (algebraMap F K) z := by
  have hmap_const (a : F) :
      Affine.FunctionField.map W.toAffine (algebraMap F K)
          (algebraMap F W.toAffine.FunctionField a) =
        algebraMap K (W⁄K).toAffine.FunctionField (algebraMap F K a) :=
    Affine.FunctionField.map_algebraMap W.toAffine (algebraMap F K) a
  have hmap_x :
      Affine.FunctionField.map W.toAffine (algebraMap F K) W.toAffine.genericX =
        (W⁄K).toAffine.genericX :=
    Affine.FunctionField.map_genericX W.toAffine (algebraMap F K)
  have hmap_y :
      Affine.FunctionField.map W.toAffine (algebraMap F K) W.toAffine.genericY =
        (W⁄K).toAffine.genericY :=
    Affine.FunctionField.map_genericY W.toAffine (algebraMap F K)
  let m : W.toAffine.FunctionField →+* (W⁄K).toAffine.FunctionField :=
    Affine.FunctionField.map W.toAffine (algebraMap F K)
  have h : (functionFieldGaloisAction W σ).toRingHom.comp m = m := by
    apply Affine.FunctionField.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      -- `ringHom_ext` states this through the local map `m`; expose its pointwise application
      -- so the named `FunctionField.map` compatibility lemmas can perform the calculation.
      change functionFieldGaloisAction W σ
          (Affine.FunctionField.map W.toAffine (algebraMap F K)
            (algebraMap F W.toAffine.FunctionField a)) =
        Affine.FunctionField.map W.toAffine (algebraMap F K)
          (algebraMap F W.toAffine.FunctionField a)
      rw [hmap_const, functionFieldGaloisAction_algebraMap]
      exact congrArg (algebraMap K (W⁄K).toAffine.FunctionField) (σ.commutes a)
    · simp only [RingHom.comp_apply]
      change functionFieldGaloisAction W σ
          (Affine.FunctionField.map W.toAffine (algebraMap F K) W.toAffine.genericX) =
        Affine.FunctionField.map W.toAffine (algebraMap F K) W.toAffine.genericX
      rw [hmap_x, functionFieldGaloisAction_genericX]
    · simp only [RingHom.comp_apply]
      change functionFieldGaloisAction W σ
          (Affine.FunctionField.map W.toAffine (algebraMap F K) W.toAffine.genericY) =
        Affine.FunctionField.map W.toAffine (algebraMap F K) W.toAffine.genericY
      rw [hmap_y, functionFieldGaloisAction_genericY]
  exact RingHom.congr_fun h z

variable [DecidableEq K] [W.IsElliptic]

private theorem functionFieldGaloisAction_translation_genericX (σ : K ≃ₐ[F] K) {x y : K}
    (h : (W⁄K).toAffine.Nonsingular x y) :
    functionFieldGaloisAction W σ
        (Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (.some x y h))
          (W⁄K).toAffine.genericX) =
      Affine.translation (W⁄K).toAffine
        (Affine.Point.equivBaseChangeSelf _
          (Multiplicative.toAdd (W.pointGaloisAction σ) (.some x y h)))
        (W⁄K).toAffine.genericX := by
  rw [Affine.Point.equivBaseChangeSelf_some, pointGaloisAction_apply, Affine.Point.map_some,
    Affine.Point.equivBaseChangeSelf_some, Affine.translation_apply_genericX_some,
    Affine.translation_apply_genericX_some,
    Affine.slope_of_X_ne (Affine.genericX_ne_algebraMap _ x),
    Affine.slope_of_X_ne (Affine.genericX_ne_algebraMap _ _)]
  simp [Affine.addX]

private theorem functionFieldGaloisAction_translation_genericY (σ : K ≃ₐ[F] K) {x y : K}
    (h : (W⁄K).toAffine.Nonsingular x y) :
    functionFieldGaloisAction W σ
        (Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (.some x y h))
          (W⁄K).toAffine.genericY) =
      Affine.translation (W⁄K).toAffine
        (Affine.Point.equivBaseChangeSelf _
          (Multiplicative.toAdd (W.pointGaloisAction σ) (.some x y h)))
        (W⁄K).toAffine.genericY := by
  rw [Affine.Point.equivBaseChangeSelf_some, pointGaloisAction_apply, Affine.Point.map_some,
    Affine.Point.equivBaseChangeSelf_some, Affine.translation_apply_genericY_some,
    Affine.translation_apply_genericY_some,
    Affine.slope_of_X_ne (Affine.genericX_ne_algebraMap _ x),
    Affine.slope_of_X_ne (Affine.genericX_ne_algebraMap _ _)]
  simp [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]

/-- **Galois conjugation intertwines translation by `P` with translation by the conjugate
point.** Equivalently, the pullback squares formed by the two translations and the Galois action
commute. -/
@[simp]
theorem functionFieldGaloisAction_translation (σ : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) (z : (W⁄K).toAffine.FunctionField) :
    functionFieldGaloisAction W σ
        (Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ P) z) =
      Affine.translation (W⁄K).toAffine
        (Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P))
        (functionFieldGaloisAction W σ z) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  -- Both sides are ring homomorphisms in `z`; compare them on constants and the generic point.
  have key :
      RingHom.comp (functionFieldGaloisAction W σ).toRingHom (Affine.translation (W⁄K).toAffine
          (Affine.Point.equivBaseChangeSelf _ (.some x y h))).toRingEquiv.toRingHom =
        RingHom.comp (Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _
            (Multiplicative.toAdd (W.pointGaloisAction σ) (.some x y h)))).toRingEquiv.toRingHom
          (functionFieldGaloisAction W σ).toRingHom :=
    Affine.FunctionField.ringHom_ext (fun a ↦ by simp)
      (by simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv, functionFieldGaloisAction_genericX] using
        functionFieldGaloisAction_translation_genericX W σ h)
      (by simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv, functionFieldGaloisAction_genericY] using
        functionFieldGaloisAction_translation_genericY W σ h)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv] using RingHom.congr_fun key z

end WeierstrassCurve

end
