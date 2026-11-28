/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic

/-!
# Translations move the places of points

Let `W` be an elliptic curve over a field `F`. The automorphism group of `F(W)` over `F` acts on
the places of `F(W)` (`TauCeti.Place.instMulActionAlgEquiv`), and the translation `τ_P^*` is such
an automorphism. It moves the place of a point `Q` to the place of `Q - P`: the function
`τ_P^* f` takes at `Q` the value `f` takes at `Q + P`, and the place `σ • v` is the one at which
`σ f` behaves as `f` does at `v`. Through the equivariance of principal divisors
(`TauCeti.Divisor.principal_smul`) this computes the divisor of a translated function from the
divisor of the function, which is what the divisor calculus of the Weil pairing needs.

## Main results

* `WeierstrassCurve.Affine.translation_smul_pointEquivDegreeOnePlace`: `τ_P^*` carries the
  place of `Q` to the place of `Q - P`.
* `WeierstrassCurve.Affine.Point.infinityPlace_translation`: the valuation of a translated function
  at infinity is its original valuation at the translating point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3, III.8.
-/

public section

open TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- **The translation by `P` carries the place of `Q` to the place of `Q - P`**: `τ_P^* f` has
at `Q` the behaviour of `f` at `Q + P`. -/
@[simp]
theorem translation_smul_pointEquivDegreeOnePlace (P Q : W.Point) :
    translation W (Point.equivBaseChangeSelf W P) • (pointEquivDegreeOnePlace W Q).val =
      (pointEquivDegreeOnePlace W (Q - P)).val := by
  set σ := translation W (Point.equivBaseChangeSelf W P)
  set v := pointEquivDegreeOnePlace W Q
  -- `σ • v` is the place of some point `R`, read off the reduction of the generic point
  have hdeg : (σ • v.val).degree = 1 := (Place.degree_smul σ v.val).trans v.property
  set R := (pointEquivDegreeOnePlace W).symm ⟨σ • v.val, hdeg⟩ with hR
  suffices R = Q - P by rw [← this, hR, Equiv.apply_symm_apply]
  apply (Point.equivBaseChangeSelf W).injective
  -- the generic point is the image under `σ` of its translate by `-P`
  have hgen : genericPoint W = Point.map (σ : W.FunctionField →ₐ[F] W.FunctionField)
      (translatedGenericPoint W (-Point.equivBaseChangeSelf W P)) := by
    rw [map_translation_translatedGenericPoint, neg_add_cancel,
      translatedGenericPoint_zero]
  rw [← reductionOfDegreeEqOne_genericPoint W R, hR, Equiv.apply_symm_apply, hgen,
    reductionOfDegreeEqOne_smul_map W σ v.property, translatedGenericPoint_def, map_add,
    reductionOfDegreeEqOne_genericPoint, reductionOfDegreeEqOne_baseChange, map_sub,
    sub_eq_add_neg]

variable {W} in
/-- At infinity, a translated function has the same valuation as the original function at
the place of the translating point. -/
theorem Point.infinityPlace_translation (P : W.Point) (f : W.FunctionField) :
    W.infinityPlace (translation W (Point.equivBaseChangeSelf W P) f) =
      (pointEquivDegreeOnePlace W P).val.valuation f := by
  -- The inverse translation sends infinity to the place of `P`.
  rw [← Place.valuation_infinity, ← AlgEquiv.symm_symm (translation W _),
    ← Place.valuation_smul, ← AlgEquiv.aut_inv, ← translation_neg, ← map_neg,
    ← coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def,
    translation_smul_pointEquivDegreeOnePlace, zero_sub, neg_neg]

end WeierstrassCurve.Affine

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- Every nonidentity translate of a coordinate-ring function is regular at infinity. -/
theorem _root_.WeierstrassCurve.Affine.valuation_translation_le_one
    {P : (W⁄F).toAffine.Point} (hP : P ≠ 0)
    (r : W.CoordinateRing) :
    W.infinityPlace (translation W P (algebraMap W.CoordinateRing W.FunctionField r)) ≤ 1 := by
  obtain ⟨Q, rfl⟩ := (Point.equivBaseChangeSelf W).surjective P
  rw [Q.infinityPlace_translation]
  apply Place.valuation_algebraMap_le_one_of_ne_infinity _ r
  rw [← coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def]
  exact fun h ↦ hP (by rw [(pointEquivDegreeOnePlace W).injective (Subtype.ext h), map_zero])

end TauCeti

end
