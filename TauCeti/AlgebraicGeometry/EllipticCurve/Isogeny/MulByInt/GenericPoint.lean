/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Basic

/-!
# The generic point of an elliptic curve has infinite order

For an elliptic curve over a field, every nonzero integer multiple of its generic point is
nonzero. Consequently, distinct integers give distinct multiples of the generic point.

## Main results

* `WeierstrassCurve.Affine.zsmul_genericPoint_ne_zero`: every nonzero multiple of the generic
  point is nonzero.
* `WeierstrassCurve.Affine.zsmul_genericPoint_injective`: multiplication of the generic point by
  an integer is injective.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **The generic point of an elliptic curve is not torsion:** every nonzero integer multiple is
nonzero. -/
theorem zsmul_genericPoint_ne_zero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    n • W.genericPoint ≠ 0 := by
  rw [← TauCeti.Isogeny.tautologicalPoint_mulByIntPullback W
    (TauCeti.Isogeny.psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn)]
  exact TauCeti.CoordinatePullback.tautologicalPoint_ne_zero _

/-- **The multiples of the generic point are pairwise distinct**, the generic point having
infinite order. -/
theorem zsmul_genericPoint_injective [W.IsElliptic] :
    Function.Injective fun n : ℤ => n • W.genericPoint :=
  injective_zsmul_iff_not_isOfFinAddOrder.mpr fun h ↦
    let ⟨_k, hk, hz⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp h
    zsmul_genericPoint_ne_zero W hk hz

end WeierstrassCurve.Affine
