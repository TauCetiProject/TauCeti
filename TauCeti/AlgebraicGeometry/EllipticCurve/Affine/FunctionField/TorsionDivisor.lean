/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.DivisorClass

/-!
# The function with divisor `n(T) - n(O)` at an `n`-torsion point

An affine point `T` of `W` is the degree-zero divisor class of `(T) - (O)`, so `T` is killed by `n`
exactly when that class is, and a degree-zero class is trivial exactly when its divisor is the
divisor of a function. At an `n`-torsion point, therefore, `n(T) - n(O)` is principal.

This is the first input to the divisor construction of the Weil pairing (Silverman III.8): the
pairing is built from such a function together with a second one whose `n`-th power is its
pullback along `[n]`.

## Main results

* `WeierstrassCurve.Affine.exists_principal_zsmul_pointPlace_sub_infinity`: at an `n`-torsion
  point `T`, the divisor `n(T) - n(O)` is the divisor of a function.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.4.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry IsDedekindDomain

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsDedekindDomain W.CoordinateRing] [DecidableEq F]

/-- **At an `n`-torsion point, `n(T) - n(O)` is the divisor of a function** (Silverman III.8.1). -/
theorem exists_principal_zsmul_pointPlace_sub_infinity {x y : F} (h : W.Nonsingular x y) {n : ℤ}
    (hT : n • Point.some x y h = 0) :
    ∃ z : W.FunctionFieldˣ, Divisor.principal W.isFunctionField z =
      n • (WeilDivisor.ofPoint (Place.ofPrime F W.FunctionField
            (CoordinateRing.pointPlace h.left)) -
          WeilDivisor.ofPoint (Place.infinity W)) := by
  rw [← Divisor.divisorClass_eq_zero_iff, map_zsmul,
    ← W.val_pointEquivDegreeZeroDivisorClass_some h]
  have hzero : n • W.pointEquivDegreeZeroDivisorClass (Point.some x y h) = 0 := by
    rw [← map_zsmul, hT, map_zero]
  exact congrArg Subtype.val hzero

end WeierstrassCurve.Affine

end
