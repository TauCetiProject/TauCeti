/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Class

/-!
# The sum of a degree-zero divisor as a point

A degree-zero divisor of `F(W)` has a divisor class, and `Divisor/Class.lean` identifies the
degree-zero classes with the points of `W`. Composing the two gives the sum map `σ`, which reads a
degree-zero divisor as a point, and the principal divisors are exactly those it sends to `O`.

That last statement is the principal-divisor characterisation: `Σ nᵢ (Pᵢ)` is the divisor of a
function exactly when `Σ nᵢ = 0` and `Σ [nᵢ] Pᵢ = O`. It is where the divisor calculus meets the
group law, and it is the existence criterion the divisor construction of the Weil pairing uses to
produce its functions.

## Main definitions

* `WeierstrassCurve.Affine.divisorSum`: **the sum of a degree-zero divisor**, as a point of `W`.
  It is `TauCeti.Divisor.degreeZeroClassHom` followed by the identification of the degree-zero
  classes with the points.

## Main results

* `WeierstrassCurve.Affine.divisorSum_pointPlace_sub_infinity`: `σ((P) - (O)) = P`, the computation
  rule that fixes `divisorSum` on the divisors it is read off from.
* `WeierstrassCurve.Affine.divisorSum_eq_zero_iff`: **a degree-zero divisor is principal exactly
  when its sum is `O`.**

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.4 and III.3.5.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.4.

## Provenance

The principality criterion was previously formalized in the AINTLIB `HasseWeil` project
(Chris Birkbeck), Apache-2.0, at commit `a302aeacd86053f9d5f991fbbf664e1cc1051d08`, as
`projIsPrincipal_of_degZero_of_sigma_eq_zero` and its torsion specialization
`weilFunction_exists`, both in
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/WeilFunction.lean`. Those are stated for the
projective divisors of a smooth plane curve and are derived from a linear-equivalence reduction
`D ∼ (σD) - (O)`; `divisorSum_eq_zero_iff` below is the function-field statement, obtained from
the degree-zero class group instead.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry IsDedekindDomain

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsDedekindDomain W.CoordinateRing] [DecidableEq F]

/-- **The sum of a degree-zero divisor**, as a point of `W`: the point whose class is the class of
the divisor. On `(P) - (O)` it is `P`, and it is additive, so on `Σ nᵢ (Pᵢ)` it is `Σ [nᵢ] Pᵢ`. -/
noncomputable def divisorSum :
    (Divisor.degree (k := F) (F := W.FunctionField)).ker →+ W.Point :=
  (W.pointEquivDegreeZeroDivisorClass.symm.toAddMonoidHom).comp
    (Divisor.degreeZeroClassHom W.isFunctionField)

/-- The defining formula for `divisorSum`: the degree-zero class map, read back as a point.

Not `@[simp]`: the characterisation `divisorSum_eq_zero_iff` below is the `simp` form, and
unfolding the composite first would keep it from firing. -/
theorem divisorSum_apply (D : (Divisor.degree (k := F) (F := W.FunctionField)).ker) :
    W.divisorSum D =
      W.pointEquivDegreeZeroDivisorClass.symm (Divisor.degreeZeroClassHom W.isFunctionField D) :=
  (rfl)

/-- **`σ((P) - (O)) = P`.** -/
@[simp]
theorem divisorSum_pointPlace_sub_infinity {x y : F} (h : W.Nonsingular x y) :
    W.divisorSum ⟨WeilDivisor.ofPoint
          (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h.left)) -
        WeilDivisor.ofPoint (Place.infinity W), by
      simpa only [AddMonoidHom.mem_ker, Divisor.degreeClass_divisorClass] using
        W.degreeClass_divisorClass_pointPlace_sub_infinity h.left⟩ = Point.some x y h := by
  rw [divisorSum_apply, AddEquiv.symm_apply_eq]
  exact Subtype.ext (by
    rw [Divisor.coe_degreeZeroClassHom_apply]
    exact (W.val_pointEquivDegreeZeroDivisorClass_some h).symm)

/-- **A degree-zero divisor is principal exactly when its sum is `O`** (Silverman III.3.5). -/
@[simp]
theorem divisorSum_eq_zero_iff {D : (Divisor.degree (k := F) (F := W.FunctionField)).ker} :
    W.divisorSum D = 0 ↔ ∃ z : W.FunctionFieldˣ,
      Divisor.principal W.isFunctionField z = (D : Divisor F W.FunctionField) := by
  rw [divisorSum_apply, AddEquiv.map_eq_zero_iff]
  exact Divisor.degreeZeroClassHom_eq_zero_iff W.isFunctionField

end WeierstrassCurve.Affine

end
