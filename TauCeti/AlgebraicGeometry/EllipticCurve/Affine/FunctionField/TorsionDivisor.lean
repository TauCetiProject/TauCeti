/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Sum

/-!
# The function with divisor `n(T) - n(O)` at an `n`-torsion point

The sum of `(T) - (O)` is `T`, so the sum of `n(T) - n(O)` is `n • T`, and a degree-zero divisor is
principal exactly when its sum is `O`. At an `n`-torsion point, therefore, `n(T) - n(O)` is
principal.

This is the first input to the divisor construction of the Weil pairing (Silverman III.8): the
pairing is built from such a function together with a second one whose `n`-th power is its
pullback along `[n]`.

## Main results

* `WeierstrassCurve.Affine.exists_principal_eq_zsmul_ofPoint_sub_infinity`: at an `n`-torsion
  point `T`, the divisor `n(T) - n(O)` is the divisor of a function.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.4.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry IsDedekindDomain

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsDedekindDomain W.CoordinateRing] [DecidableEq F] [W.IsElliptic]

/-- **At an `n`-torsion point, `n(T) - n(O)` is the divisor of a function** (Silverman III.8.1). -/
theorem exists_principal_eq_zsmul_ofPoint_sub_infinity {n : ℤ} {T : W.Point} (hT : n • T = 0) :
    ∃ z : W.FunctionFieldˣ, Divisor.principal W.isFunctionField z =
      n • (WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace T).1 -
        WeilDivisor.ofPoint (Place.infinity W)) := by
  rw [← coe_pointEquivDegreeOnePlace_zero]
  exact W.divisorSum_eq_zero_iff (D := n • ⟨_, W.ofPoint_sub_ofPoint_mem_ker_degree T .zero⟩) |>.1
    (by rw [map_zsmul, divisorSum_ofPoint_sub_ofPoint, ← Point.zero_def, sub_zero, hT])

end WeierstrassCurve.Affine

end
