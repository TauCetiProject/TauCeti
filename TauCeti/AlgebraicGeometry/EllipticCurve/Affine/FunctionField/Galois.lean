/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois

/-!
# Galois actions on elliptic-curve function fields

Let `W` be a Weierstrass curve over a field `F`, and let `K/F` be a field extension. Every
`F`-automorphism of `K` acts semilinearly on the coordinate ring and function field of `W_K`:
it applies the automorphism to coefficients and fixes the coordinate functions `x` and `y`.
This file packages those actions and proves their identity and composition laws.

The function-field action and the already-defined action on torsion points are the two inputs
needed to prove Galois equivariance of the Weil pairing. In particular, the action on functions
must also conjugate translation by `P` to translation by the conjugate point; that compatibility
is proved here.

## Main definitions

* `WeierstrassCurve.Affine.coordinateRingGaloisAction`: the action on the coordinate ring.
* `WeierstrassCurve.Affine.functionFieldGaloisAction`: the action on the function field.

## Main results

* `WeierstrassCurve.Affine.functionFieldGaloisAction_algebraMap`: the action is semilinear on
  constants.
* `WeierstrassCurve.Affine.functionFieldGaloisAction_genericX` and
  `functionFieldGaloisAction_genericY`: the two coordinate functions are fixed.
* `WeierstrassCurve.Affine.functionFieldGaloisAction_translation`: the action intertwines
  translation by a point with translation by its Galois conjugate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  (W : WeierstrassCurve F)

private theorem map_polynomial_galois (σ : K ≃ₐ[F] K) :
    ((W⁄K).toAffine.polynomial.map
      (Polynomial.mapEquiv σ.toRingEquiv).toRingHom) = (W⁄K).toAffine.polynomial := by
  rw [show (Polynomial.mapEquiv σ.toRingEquiv).toRingHom = mapRingHom σ from rfl]
  rw [← WeierstrassCurve.Affine.map_polynomial]
  exact congrArg WeierstrassCurve.Affine.polynomial
    (WeierstrassCurve.Affine.map_baseChange (W := W.toAffine) σ.toAlgHom)

/-- **The Galois action on the coordinate ring of an elliptic curve.** It applies an
`F`-automorphism of the extension field to coefficients and fixes the classes of `x` and `y`. -/
private noncomputable def coordinateRingGaloisEquiv (σ : K ≃ₐ[F] K) :
    (W⁄K).toAffine.CoordinateRing ≃+* (W⁄K).toAffine.CoordinateRing :=
  AdjoinRoot.mapRingEquiv (Polynomial.mapEquiv σ.toRingEquiv)
    (W⁄K).toAffine.polynomial (W⁄K).toAffine.polynomial
    (Associated.of_eq (map_polynomial_galois W σ))

/-- The coordinate-ring action applies the field automorphism to constants. -/
@[simp]
private theorem coordinateRingGaloisEquiv_algebraMap (σ : K ≃ₐ[F] K) (a : K) :
    coordinateRingGaloisEquiv W σ
        (algebraMap K (W⁄K).toAffine.CoordinateRing a) =
      algebraMap K (W⁄K).toAffine.CoordinateRing (σ a) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (W⁄K).toAffine.CoordinateRing,
    AdjoinRoot.algebraMap_eq]
  simp only [coordinateRingGaloisEquiv, Polynomial.mapEquiv,
    AlgEquiv.toRingEquiv_toRingHom, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
    AlgEquiv.symm_toEquiv_eq_symm, Polynomial.algebraMap_eq, AdjoinRoot.coe_mapRingEquiv,
    AdjoinRoot.map_of, RingHom.coe_coe, RingEquiv.ofRingHom_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_C]
  calc
    AdjoinRoot.of (W⁄K).toAffine.polynomial (C (σ a)) =
        algebraMap K[X] (W⁄K).toAffine.CoordinateRing (C (σ a)) :=
      by rw [AdjoinRoot.algebraMap_eq]
    _ = algebraMap K[X] (W⁄K).toAffine.CoordinateRing
        (algebraMap K K[X] (σ a)) := by rw [Polynomial.algebraMap_eq]
    _ = algebraMap K (W⁄K).toAffine.CoordinateRing (σ a) :=
      (IsScalarTower.algebraMap_apply K K[X] (W⁄K).toAffine.CoordinateRing (σ a)).symm

/-- The coordinate-ring action fixes the class of `y`. -/
@[simp]
private theorem coordinateRingGaloisEquiv_root (σ : K ≃ₐ[F] K) :
    coordinateRingGaloisEquiv W σ
        (AdjoinRoot.root (W⁄K).toAffine.polynomial) =
      AdjoinRoot.root (W⁄K).toAffine.polynomial := by
  simp [coordinateRingGaloisEquiv]

/-- On the polynomial subring, the coordinate-ring action maps coefficients and fixes `x`. -/
@[simp]
private theorem coordinateRingGaloisEquiv_of (σ : K ≃ₐ[F] K) (p : K[X]) :
    coordinateRingGaloisEquiv W σ
        (AdjoinRoot.of (W⁄K).toAffine.polynomial p) =
      AdjoinRoot.of (W⁄K).toAffine.polynomial (p.map σ) := by
  simp [coordinateRingGaloisEquiv, Polynomial.mapEquiv]

/-- **The Galois action on the coordinate ring**, bundled with its identity and composition
laws. -/
noncomputable def coordinateRingGaloisAction :
    (K ≃ₐ[F] K) →* ((W⁄K).toAffine.CoordinateRing ≃+* (W⁄K).toAffine.CoordinateRing) where
  toFun := coordinateRingGaloisEquiv W
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext <;> simp
    · simp
  map_mul' σ τ := by
    apply RingEquiv.toRingHom_injective
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext <;> simp
    · simp

/-- The coordinate-ring action applies the field automorphism to constants. -/
@[simp]
theorem coordinateRingGaloisAction_algebraMap (σ : K ≃ₐ[F] K) (a : K) :
    coordinateRingGaloisAction W σ
        (algebraMap K (W⁄K).toAffine.CoordinateRing a) =
      algebraMap K (W⁄K).toAffine.CoordinateRing (σ a) := by
  change coordinateRingGaloisEquiv W σ
      (algebraMap K (W⁄K).toAffine.CoordinateRing a) = _
  exact coordinateRingGaloisEquiv_algebraMap W σ a

/-- The coordinate-ring action fixes the class of `y`. -/
@[simp]
theorem coordinateRingGaloisAction_root (σ : K ≃ₐ[F] K) :
    coordinateRingGaloisAction W σ
        (AdjoinRoot.root (W⁄K).toAffine.polynomial) =
      AdjoinRoot.root (W⁄K).toAffine.polynomial := by
  change coordinateRingGaloisEquiv W σ
      (AdjoinRoot.root (W⁄K).toAffine.polynomial) = _
  exact coordinateRingGaloisEquiv_root W σ

/-- On the polynomial subring, the coordinate-ring action maps coefficients and fixes `x`. -/
@[simp]
theorem coordinateRingGaloisAction_of (σ : K ≃ₐ[F] K) (p : K[X]) :
    coordinateRingGaloisAction W σ
        (AdjoinRoot.of (W⁄K).toAffine.polynomial p) =
      AdjoinRoot.of (W⁄K).toAffine.polynomial (p.map σ) := by
  change coordinateRingGaloisEquiv W σ
      (AdjoinRoot.of (W⁄K).toAffine.polynomial p) = _
  exact coordinateRingGaloisEquiv_of W σ p

/-- **The Galois action on the function field of an elliptic curve.** It is the unique extension
of `coordinateRingGaloisAction` to the fraction field. -/
noncomputable def functionFieldGaloisAction :
    (K ≃ₐ[F] K) →*
      ((W⁄K).toAffine.FunctionField ≃+* (W⁄K).toAffine.FunctionField) :=
  (IsFractionRing.ringEquivOfRingEquivHom (W⁄K).toAffine.CoordinateRing
    (W⁄K).toAffine.FunctionField).comp (coordinateRingGaloisAction W)

/-- The function-field action restricts to the coordinate-ring action. -/
@[simp]
theorem functionFieldGaloisAction_algebraMap_coordinateRing (σ : K ≃ₐ[F] K)
    (z : (W⁄K).toAffine.CoordinateRing) :
    functionFieldGaloisAction W σ
        (algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField z) =
      algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField
        (coordinateRingGaloisAction W σ z) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ z

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
    functionFieldGaloisAction W σ (W⁄K).toAffine.genericX =
      (W⁄K).toAffine.genericX := by
  rw [genericX_def, functionFieldGaloisAction_algebraMap_coordinateRing]
  congr 1
  simp

/-- The function-field action fixes the generic `y`-coordinate. -/
@[simp]
theorem functionFieldGaloisAction_genericY (σ : K ≃ₐ[F] K) :
    functionFieldGaloisAction W σ (W⁄K).toAffine.genericY =
      (W⁄K).toAffine.genericY := by
  rw [genericY_def, functionFieldGaloisAction_algebraMap_coordinateRing]
  congr 1
  exact coordinateRingGaloisAction_root W σ

variable [DecidableEq K] [W.IsElliptic]

private theorem functionFieldGaloisAction_translation_genericX (σ : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) :
    functionFieldGaloisAction W σ
        (translation (W⁄K).toAffine (Point.equivBaseChangeSelf (W⁄K).toAffine P)
          (W⁄K).toAffine.genericX) =
      translation (W⁄K).toAffine
        (Point.equivBaseChangeSelf (W⁄K).toAffine
          (Multiplicative.toAdd (W.pointGaloisAction σ) P))
        (W⁄K).toAffine.genericX := by
  rcases P with _ | ⟨x, y, h⟩
  · have hzero : (Point.zero : (W⁄K).toAffine.Point) = 0 := rfl
    rw [hzero]
    have hbase : Point.equivBaseChangeSelf (W⁄K).toAffine (0 : (W⁄K).toAffine.Point) = 0 :=
      map_zero _
    have hσ : Multiplicative.toAdd (W.pointGaloisAction σ)
        (0 : (W⁄K).toAffine.Point) = 0 := map_zero _
    rw [hbase, hσ, hbase, translation_zero, AlgEquiv.one_apply,
      functionFieldGaloisAction_genericX]
  · rw [Point.equivBaseChangeSelf_some, pointGaloisAction_apply, Point.map_some,
      Point.equivBaseChangeSelf_some, translation_apply_genericX_some,
      translation_apply_genericX_some]
    have hx : (W⁄K).toAffine.genericX ≠
        algebraMap K (W⁄K).toAffine.FunctionField x :=
      genericX_ne_algebraMap (W⁄K).toAffine x
    have hxσ : (W⁄K).toAffine.genericX ≠
        algebraMap K (W⁄K).toAffine.FunctionField (σ x) :=
      genericX_ne_algebraMap (W⁄K).toAffine (σ x)
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    unfold WeierstrassCurve.Affine.slope
    simp only [genericX_ne_algebraMap, ↓reduceIte]
    simp [WeierstrassCurve.Affine.addX]

private theorem functionFieldGaloisAction_translation_genericY (σ : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) :
    functionFieldGaloisAction W σ
        (translation (W⁄K).toAffine (Point.equivBaseChangeSelf (W⁄K).toAffine P)
          (W⁄K).toAffine.genericY) =
      translation (W⁄K).toAffine
        (Point.equivBaseChangeSelf (W⁄K).toAffine
          (Multiplicative.toAdd (W.pointGaloisAction σ) P))
        (W⁄K).toAffine.genericY := by
  rcases P with _ | ⟨x, y, h⟩
  · have hzero : (Point.zero : (W⁄K).toAffine.Point) = 0 := rfl
    rw [hzero]
    have hbase : Point.equivBaseChangeSelf (W⁄K).toAffine (0 : (W⁄K).toAffine.Point) = 0 :=
      map_zero _
    have hσ : Multiplicative.toAdd (W.pointGaloisAction σ)
        (0 : (W⁄K).toAffine.Point) = 0 := map_zero _
    rw [hbase, hσ, hbase, translation_zero, AlgEquiv.one_apply,
      functionFieldGaloisAction_genericY]
  · rw [Point.equivBaseChangeSelf_some, pointGaloisAction_apply, Point.map_some,
      Point.equivBaseChangeSelf_some, translation_apply_genericY_some,
      translation_apply_genericY_some]
    have hx : (W⁄K).toAffine.genericX ≠
        algebraMap K (W⁄K).toAffine.FunctionField x :=
      genericX_ne_algebraMap (W⁄K).toAffine x
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    unfold WeierstrassCurve.Affine.slope
    simp only [genericX_ne_algebraMap, ↓reduceIte]
    simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]

/-- **Galois conjugation intertwines translation by `P` with translation by the conjugate
point.** Equivalently, the pullback squares formed by the two translations and the Galois action
commute. -/
@[simp]
theorem functionFieldGaloisAction_translation (σ : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) (z : (W⁄K).toAffine.FunctionField) :
    functionFieldGaloisAction W σ
        (translation (W⁄K).toAffine (Point.equivBaseChangeSelf (W⁄K).toAffine P) z) =
      translation (W⁄K).toAffine
        (Point.equivBaseChangeSelf (W⁄K).toAffine
          (Multiplicative.toAdd (W.pointGaloisAction σ) P))
        (functionFieldGaloisAction W σ z) := by
  let τP := translation (W⁄K).toAffine (Point.equivBaseChangeSelf (W⁄K).toAffine P)
  let τσP := translation (W⁄K).toAffine
    (Point.equivBaseChangeSelf (W⁄K).toAffine
      (Multiplicative.toAdd (W.pointGaloisAction σ) P))
  let A := functionFieldGaloisAction W σ
  have ringEquiv_toRingHom_apply
      (e : (W⁄K).toAffine.FunctionField ≃+* (W⁄K).toAffine.FunctionField)
      (x : (W⁄K).toAffine.FunctionField) : e.toRingHom x = e x :=
    DFunLike.congr_fun (RingEquiv.toRingHom_eq_coe e) x
  have algEquiv_toRingHom_apply
      (e : (W⁄K).toAffine.FunctionField ≃ₐ[K] (W⁄K).toAffine.FunctionField)
      (x : (W⁄K).toAffine.FunctionField) : e.toRingEquiv.toRingHom x = e x :=
    DFunLike.congr_fun (AlgEquiv.toRingEquiv_toRingHom e) x
  have algEquiv_toRingEquiv_apply
      (e : (W⁄K).toAffine.FunctionField ≃ₐ[K] (W⁄K).toAffine.FunctionField)
      (x : (W⁄K).toAffine.FunctionField) : e.toRingEquiv x = e x :=
    congrFun (AlgEquiv.coe_toRingEquiv e) x
  have h : A.toRingHom.comp τP.toRingEquiv.toRingHom =
      τσP.toRingEquiv.toRingHom.comp A.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := (W⁄K).toAffine.CoordinateRing)
    intro a
    have hc :
        (A.toRingHom.comp τP.toRingEquiv.toRingHom).comp
            (algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField) =
          (τσP.toRingEquiv.toRingHom.comp A.toRingHom).comp
            (algebraMap (W⁄K).toAffine.CoordinateRing
              (W⁄K).toAffine.FunctionField) := by
      apply AdjoinRoot.ringHom_ext
      · apply Polynomial.ringHom_ext
        · intro b
          simp only [RingHom.comp_apply]
          have hof : AdjoinRoot.of (W⁄K).toAffine.polynomial (C b) =
              algebraMap K (W⁄K).toAffine.CoordinateRing b := by
            calc
              AdjoinRoot.of (W⁄K).toAffine.polynomial (C b) =
                  algebraMap K[X] (W⁄K).toAffine.CoordinateRing (C b) := by
                rw [AdjoinRoot.algebraMap_eq]
              _ = algebraMap K[X] (W⁄K).toAffine.CoordinateRing
                  (algebraMap K K[X] b) := by rw [Polynomial.algebraMap_eq]
              _ = algebraMap K (W⁄K).toAffine.CoordinateRing b :=
                (IsScalarTower.algebraMap_apply K K[X]
                  (W⁄K).toAffine.CoordinateRing b).symm
          rw [hof, ← IsScalarTower.algebraMap_apply K (W⁄K).toAffine.CoordinateRing
            (W⁄K).toAffine.FunctionField]
          simp [A, τP, τσP]
        · simp only [RingHom.comp_apply]
          have hxdef : algebraMap (W⁄K).toAffine.CoordinateRing
              (W⁄K).toAffine.FunctionField
                (AdjoinRoot.of (W⁄K).toAffine.polynomial X) =
              (W⁄K).toAffine.genericX := by
            rw [genericX_def, CoordinateRing.mk_C_eq_algebraMap,
              AdjoinRoot.algebraMap_eq]
          rw [hxdef]
          dsimp only [A, τP, τσP]
          simpa only [ringEquiv_toRingHom_apply, algEquiv_toRingHom_apply,
            algEquiv_toRingEquiv_apply, functionFieldGaloisAction_genericX] using
            functionFieldGaloisAction_translation_genericX W σ P
      · simp only [RingHom.comp_apply]
        have hydef : algebraMap (W⁄K).toAffine.CoordinateRing
            (W⁄K).toAffine.FunctionField
              (AdjoinRoot.root (W⁄K).toAffine.polynomial) =
            (W⁄K).toAffine.genericY := by
          rw [genericY_def, AdjoinRoot.mk_X]
        rw [hydef]
        dsimp only [A, τP, τσP]
        simpa only [ringEquiv_toRingHom_apply, algEquiv_toRingHom_apply,
          algEquiv_toRingEquiv_apply, functionFieldGaloisAction_genericY] using
          functionFieldGaloisAction_translation_genericY W σ P
    exact RingHom.congr_fun hc a
  exact RingHom.congr_fun h z

end WeierstrassCurve.Affine

end
