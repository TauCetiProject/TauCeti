/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique

/-!
# The place at infinity under change of the coefficient field

The place at infinity of a base-changed Weierstrass curve restricts to the original place at
infinity. The restriction is trivial on the original constants and the generic `x`-coordinate
still has a pole, so uniqueness of the infinity place identifies it. The conclusion identifies
their valuation rings, which is the place-level notion of equality.

No ellipticity or algebraicity hypothesis on the extension is needed. The base map may be any
homomorphism of fields, including a coefficient automorphism.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K]

/-- The place at infinity after changing coefficients restricts to the original place at
infinity: the generic `x`-coordinate retains its pole and the restriction is trivial on `F`. -/
theorem isEquiv_comap_infinityPlace_map (W : Affine F) (f : F →+* K) :
    ((infinityPlace (W.map f)).comap (FunctionField.map W f)).IsEquiv
      (infinityPlace W) := by
  let v := (infinityPlace (W.map f)).comap (FunctionField.map W f)
  have : v.IsTrivialOn F := {
    eq_one a ha := by
      -- Evaluate the restricted valuation on a constant before applying scalar compatibility.
      change infinityPlace (W.map f)
          (FunctionField.map W f (algebraMap F W.FunctionField a)) = 1
      rw [FunctionField.map_algebraMap]
      exact Valuation.IsTrivialOn.eq_one (v := infinityPlace (W.map f)) (f a)
        (by simpa only [map_zero] using f.injective.ne ha) }
  apply isEquiv_infinityPlace_of_one_lt (v := v)
  -- The comap is evaluation after the function-field coefficient embedding.
  change 1 < infinityPlace (W.map f)
    (FunctionField.map W f (algebraMap F[X] W.FunctionField Polynomial.X))
  rw [FunctionField.map_algebraMap_X]
  exact one_lt_infinityPlace_X (W.map f)

end WeierstrassCurve.Affine

end
