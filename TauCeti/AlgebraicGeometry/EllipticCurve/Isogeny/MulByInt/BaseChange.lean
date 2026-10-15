/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
-- Proof-only: `ωₙ` commutes with change of coefficients.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Omega

/-!
# Multiplication by `n` under base change

Multiplication by `n` is defined by the same division polynomials over every field, and the
division polynomials of `W.map f` are those of `W` with `f` applied to their coefficients
(`WeierstrassCurve.map_ψ`, `WeierstrassCurve.map_φ`, `WeierstrassCurve.map_ω`). So carrying the
isogeny `[n]` of `W` along a homomorphism `f : F →+* K` of the base field gives the isogeny `[n]`
of `W.map f`. This is what lets a statement about `[n]` over `F` be read over an extension, where
more points are available: over an algebraic closure its kernel is the whole geometric
`n`-torsion.

## Main results

* `TauCeti.Isogeny.map_psiFunctionField`, `TauCeti.Isogeny.map_phiFunctionField` and
  `TauCeti.Isogeny.map_omegaFunctionField`: the division polynomials at the generic point are
  carried to those of `W.map f`.
* `TauCeti.Isogeny.map_mulByIntX` and `TauCeti.Isogeny.map_mulByIntY`: so are the coordinates
  of `[n]` at the generic point.
* `TauCeti.Isogeny.mulByIntIsogeny_map`: the base change of `[n]` is `[n]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Field K] (W : WeierstrassCurve.Affine F) (f : F →+* K)

/-- **`ψₙ` at the generic point is carried to `ψₙ` of `W.map f`.** -/
@[simp]
theorem map_psiFunctionField (n : ℤ) :
    FunctionField.map W f (psiFunctionField W n) = psiFunctionField (W.map f) n := by
  rw [psiFunctionField_def, psiFunctionField_def, FunctionField.map_algebraMap_coordinateRing,
    CoordinateRing.map_mk, WeierstrassCurve.map_ψ]

/-- **`φₙ` at the generic point is carried to `φₙ` of `W.map f`.** -/
@[simp]
theorem map_phiFunctionField (n : ℤ) :
    FunctionField.map W f (phiFunctionField W n) = phiFunctionField (W.map f) n := by
  rw [phiFunctionField_def, phiFunctionField_def, FunctionField.map_algebraMap_coordinateRing,
    CoordinateRing.map_mk, WeierstrassCurve.map_φ]

/-- **`ωₙ` at the generic point is carried to `ωₙ` of `W.map f`.** -/
@[simp]
theorem map_omegaFunctionField (n : ℤ) :
    FunctionField.map W f (omegaFunctionField W n) = omegaFunctionField (W.map f) n := by
  rw [omegaFunctionField_def, omegaFunctionField_def,
    FunctionField.map_algebraMap_coordinateRing, CoordinateRing.map_mk, WeierstrassCurve.map_ω]

/-- **The `x`-coordinate `φₙ / ψₙ²` of `[n]` is carried to that of `W.map f`.** -/
@[simp]
theorem map_mulByIntX (n : ℤ) :
    FunctionField.map W f (mulByIntX W n) = mulByIntX (W.map f) n := by
  rw [mulByIntX_def, mulByIntX_def, map_div₀, map_pow, map_phiFunctionField,
    map_psiFunctionField]

/-- **The `y`-coordinate `ωₙ / ψₙ³` of `[n]` is carried to that of `W.map f`.** -/
@[simp]
theorem map_mulByIntY (n : ℤ) :
    FunctionField.map W f (mulByIntY W n) = mulByIntY (W.map f) n := by
  rw [mulByIntY_def, mulByIntY_def, map_div₀, map_pow, map_omegaFunctionField,
    map_psiFunctionField]

/-- **The base change of `[n]` is `[n]`**: carrying multiplication by `n` on `W` along `f` gives
multiplication by `n` on `W.map f`. The nonvanishing of `ψₙ` over `K` is that over `F`, carried
along the injective map `FunctionField.map W f`. -/
@[simp]
theorem mulByIntIsogeny_map [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).map f = mulByIntIsogeny (W.map f) (n := n)
      (map_psiFunctionField W f n ▸
        (map_ne_zero_iff _ (FunctionField.map W f).injective).2 hn) := by
  refine eq_of_pullback_coords rfl _ _ ?_ ?_
  · rw [map_pullback, CoordinatePullback.map_of_X, mulByIntIsogeny_pullback,
      mulByIntIsogeny_pullback, mulByIntPullback_X, mulByIntPullback_X, map_mulByIntX]
  · rw [map_pullback, CoordinatePullback.map_root, mulByIntIsogeny_pullback,
      mulByIntIsogeny_pullback, mulByIntPullback_Y, mulByIntPullback_Y, map_mulByIntY]

end TauCeti.Isogeny

end
