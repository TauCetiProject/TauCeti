/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Basic

/-!
# The isogeny `1 − π` is separable

Over a finite field, the Frobenius isogeny `π` pulls the invariant differential `ω` back to `0`, so
the isogeny `1 − π` pulls it back to `ω` itself; by the differential criterion, `1 − π` is
separable (Silverman III.5.5). This is the step through which the number of rational points,
the size of the kernel of `1 − π`, becomes a degree.

## Main results

* `TauCeti.Isogeny.pullbackDifferential_oneSubFrobeniusIsogeny_invariantDifferential`:
  `(1 − π)^*ω = ω`.
* `TauCeti.Isogeny.isSeparable_oneSubFrobeniusIsogeny`: `1 − π` is separable.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) also establishes the separability of `1 − π`, in
`AdditionPullback/Frobenius.lean`, for its own notion of isogeny, which carries a map on points.
Here the isogeny is a coordinate pullback and separability is that of the function-field
extension it induces, as everywhere in `TauCeti.Isogeny`; nothing is taken from the source.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.5, V.1.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **`1 − π` pulls the invariant differential back to itself**, since Frobenius kills it. -/
@[simp]
theorem pullbackDifferential_oneSubFrobeniusIsogeny_invariantDifferential :
    (oneSubFrobeniusIsogeny W).pullbackDifferential (invariantDifferential W) =
      invariantDifferential W := by
  -- In the endomorphism carrier `1 − π` is the difference `1 - π`, the pullback of `ω` is additive,
  -- and Frobenius kills `ω`.
  rw [← Hom.pullbackDifferential_ofIsogeny]
  simp

/-- **The isogeny `1 − π` is separable.** -/
theorem isSeparable_oneSubFrobeniusIsogeny :
    Algebra.IsSeparable (oneSubFrobeniusIsogeny W).fieldPullback.fieldRange W.FunctionField :=
  (isSeparable_iff_pullbackDifferential_ne_zero _).2 (by
    rw [pullbackDifferential_oneSubFrobeniusIsogeny_invariantDifferential]
    exact invariantDifferential_ne_zero W)

end TauCeti.Isogeny

end
