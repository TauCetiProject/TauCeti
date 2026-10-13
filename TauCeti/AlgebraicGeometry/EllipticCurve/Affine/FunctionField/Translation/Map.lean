/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong

/-!
# Translations under change of the coefficient field

Let `W` be a Weierstrass curve over a field `F` and `f : F →+* K` a homomorphism of fields. A point
`P` of `W` is carried to the point `f P` of `W.map f` (`WeierstrassCurve.Affine.Point.mapAlong`),
and the function field of `W` is carried into that of `W.map f`
(`WeierstrassCurve.Affine.FunctionField.map`). This file proves that the second map intertwines
translation by `P` with translation by `f P`:

    f^* (τ_P^* z) = τ_{f P}^* (f^* z).

Both sides are ring homomorphisms in `z`, so it suffices to compare them on the constants and on
the generic point. On the constants both are `f`. On the generic point, translation by an affine
point is given by the addition formulas, whose coefficients are polynomials in the coefficients of
the curve and the coordinates of the point, and `f` commutes with them.

## Main results

* `WeierstrassCurve.Affine.FunctionField.map_translation`: changing the coefficient field
  intertwines translation by `P` with translation by `f P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine.FunctionField

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic] (f : F →+* K)

/-- Translating the generic `x`-coordinate by an affine point commutes with changing the
coefficient field. -/
private theorem map_translation_genericX {x y : F} (h : W.Nonsingular x y) :
    map W f (translation W (Point.equivBaseChangeSelf W (.some x y h)) W.genericX) =
      translation (W.map f)
        (Point.equivBaseChangeSelf (W.map f) ((Point.some x y h).mapAlong f f.injective))
        (W.map f).genericX := by
  rw [Point.mapAlong_some, Point.equivBaseChangeSelf_some, Point.equivBaseChangeSelf_some,
    translation_apply_genericX_some, translation_apply_genericX_some,
    slope_of_X_ne (genericX_ne_algebraMap _ x), slope_of_X_ne (genericX_ne_algebraMap _ _)]
  simp [addX]

/-- Translating the generic `y`-coordinate by an affine point commutes with changing the
coefficient field. -/
private theorem map_translation_genericY {x y : F} (h : W.Nonsingular x y) :
    map W f (translation W (Point.equivBaseChangeSelf W (.some x y h)) W.genericY) =
      translation (W.map f)
        (Point.equivBaseChangeSelf (W.map f) ((Point.some x y h).mapAlong f f.injective))
        (W.map f).genericY := by
  rw [Point.mapAlong_some, Point.equivBaseChangeSelf_some, Point.equivBaseChangeSelf_some,
    translation_apply_genericY_some, translation_apply_genericY_some,
    slope_of_X_ne (genericX_ne_algebraMap _ x), slope_of_X_ne (genericX_ne_algebraMap _ _)]
  simp [addY, negY, negAddY, addX]

/-- **Changing the coefficient field intertwines translation by `P` with translation by `f P`**:
`f^* (τ_P^* z) = τ_{f P}^* (f^* z)` for every function `z` on `W`. -/
theorem map_translation (P : W.Point) (z : W.FunctionField) :
    map W f (translation W (Point.equivBaseChangeSelf W P) z) =
      translation (W.map f) (Point.equivBaseChangeSelf (W.map f) (P.mapAlong f f.injective))
        (map W f z) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  -- Both sides are ring homomorphisms in `z`; compare them on constants and the generic point.
  have key :
      (map W f).comp (translation W (Point.equivBaseChangeSelf W (.some x y h))).toRingHom =
        (translation (W.map f) (Point.equivBaseChangeSelf (W.map f)
          ((Point.some x y h).mapAlong f f.injective))).toRingHom.comp (map W f) :=
    ringHom_ext (fun a ↦ by simp) (by simpa using map_translation_genericX W f h)
      (by simpa using map_translation_genericY W f h)
  exact RingHom.congr_fun key z

end WeierstrassCurve.Affine.FunctionField

end
