/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic

/-!
# The formal group of the Tate curve at `q = 0`

The Tate curve over `ℤ⟦q⟧` reduces at `q = 0` to the nodal cubic `y² + xy = x³`. By
`WeierstrassCurve.formalGroup_eq_homothety_smul_𝔾ₘ`, its formal group law is `X + Y - XY`, the
transport of the multiplicative formal group law `X + Y + XY` along `T ↦ -T`. In particular it has
height `1` in every characteristic, including `2` and `3`
(`WeierstrassCurve.height_formalGroup_eq_one`).

## Main results

* `TauCeti.formalGroup_map_constantCoeff_tateCurve`: the formal group law of the Tate
  curve at `q = 0` is the transport of the multiplicative formal group law along `T ↦ -T`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

open WeierstrassCurve FormalGroup

namespace TauCeti

/-- **The formal group of the Tate curve at `q = 0` is multiplicative**: the Tate curve over
`ℤ⟦q⟧` reduces at `q = 0` to the nodal cubic `y² + xy = x³`, whose formal group law
`X + Y - XY` is the transport of `X + Y + XY` along `T ↦ -T`. -/
theorem formalGroup_map_constantCoeff_tateCurve :
    formalGroup (tateCurve.map PowerSeries.constantCoeff) =
      FormalCoordinate.homothety (-1 : ℤˣ) • (𝔾ₘ : FormalGroup ℤ) := by
  simpa using formalGroup_eq_homothety_smul_𝔾ₘ (W := tateCurve.map PowerSeries.constantCoeff) 1
    (by simp) (by simp) (by simp) (by simp) (by simp)

end TauCeti
