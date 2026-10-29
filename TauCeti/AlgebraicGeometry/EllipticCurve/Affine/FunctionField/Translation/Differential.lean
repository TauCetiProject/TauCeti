/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Derivation

/-!
# Translation invariance of the elliptic differential

For an elliptic Weierstrass curve `W` over any field `F`, the function-field pullback of every
translation fixes the invariant differential `ω = dx / (2y + a₁x + a₃)`. The map on differentials
is the canonical `KaehlerDifferential.mapSemilinear` along the translation automorphism.

The statement includes translations by points of order two, where `2y + a₁x + a₃` can vanish at
the translating point: its coordinates have zero differential, so no division by that value is
needed. The computation is valid in every characteristic.

## Main result

* `WeierstrassCurve.Affine.mapSemilinear_translation_invariantDifferential`: `τ_P^*ω = ω`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5.1.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

private theorem D_translation_genericX_some {x y : F} (h : (W⁄F).toAffine.Nonsingular x y) :
    KaehlerDifferential.D F W.FunctionField (translation W (.some x y h) (genericX W)) =
      translation W (.some x y h) (invariantDifferentialDenom W) •
        invariantDifferential W := by
  have h₂ : (W⁄W.FunctionField).toAffine.Equation
      (algebraMap F W.FunctionField x) (algebraMap F W.FunctionField y) :=
    h.left.baseChange (Algebra.ofId F W.FunctionField)
  have hd := derivation_addX_slope_of_right_constant
    (W := W) (KaehlerDifferential.D F W.FunctionField)
    (equation_genericX_genericY W) h₂ (genericX_ne_algebraMap W x)
    (evalEval_polynomialY_genericX_genericY_ne_zero W)
    (KaehlerDifferential.D F W.FunctionField |>.map_algebraMap x)
    (KaehlerDifferential.D F W.FunctionField |>.map_algebraMap y)
  rw [translation_apply_genericX_some W h]
  rw [hd, invariantDifferential_def, invariantDifferentialDenom_eq_evalEval_polynomialY]
  congr 1
  rw [← translation_apply_genericX_some W h, ← translation_apply_genericY_some W h]
  nth_rw 1 [baseChange_polynomialY W (translation W (.some x y h)).toAlgHom]
  exact Polynomial.map_mapRingHom_evalEval (translation W (.some x y h)).toAlgHom.toRingHom _ _ _

/-- **Every translation fixes the invariant differential** `ω = dx / (2y + a₁x + a₃)`
(Silverman III.5.1). This holds over any field, including for translating points of order two. -/
-- Simplify before the semilinear map's scalar homomorphism normalizes from the algebra-map
-- projection to the ring-map projection of the translation equivalence.
@[simp↓]
theorem mapSemilinear_translation_invariantDifferential (P : (W⁄F).toAffine.Point) :
    KaehlerDifferential.mapSemilinear
      (translation W P : W.FunctionField →ₐ[F] W.FunctionField)
      (invariantDifferential W) = invariantDifferential W := by
  cases P with
  | zero =>
    rw [← Point.zero_def, translation_zero]
    exact KaehlerDifferential.mapSemilinear_id_apply _
  | some x y h =>
    have hdenom : translation W (.some x y h) (invariantDifferentialDenom W) ≠ 0 :=
      (map_ne_zero _).mpr (invariantDifferentialDenom_ne_zero W)
    nth_rw 1 [invariantDifferential_def]
    rw [KaehlerDifferential.mapSemilinear_smul,
      KaehlerDifferential.mapSemilinear_D, map_inv₀, AlgEquiv.toAlgHom_apply,
      AlgEquiv.toAlgHom_apply, D_translation_genericX_some W h,
      smul_smul, inv_mul_cancel₀ hdenom, one_smul]

end WeierstrassCurve.Affine

end
