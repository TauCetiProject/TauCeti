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
    translation W (Point.equivBaseChangeSelf W P) • (pointEquivDegreeOnePlace W Q).1 =
      (pointEquivDegreeOnePlace W (Q - P)).1 := by
  set σ := translation W (Point.equivBaseChangeSelf W P)
  set v := pointEquivDegreeOnePlace W Q
  -- `σ • v` is the place of some point `R`, read off the reduction of the generic point
  have hdeg : (σ • v.1).degree = 1 := (Place.degree_smul σ v.1).trans v.2
  set R := (pointEquivDegreeOnePlace W).symm ⟨σ • v.1, hdeg⟩ with hR
  have hRv : (pointEquivDegreeOnePlace W R).1 = σ • v.1 := by
    rw [hR, Equiv.apply_symm_apply]
  suffices R = Q - P by rw [← this, hRv]
  apply (Point.equivBaseChangeSelf W).injective
  -- the generic point is the image under `σ` of its translate by `-P`
  have hgen : genericPoint W = Point.map (σ : W.FunctionField →ₐ[F] W.FunctionField)
      (translatedGenericPoint W (-Point.equivBaseChangeSelf W P)) := by
    rw [map_translation_translatedGenericPoint, neg_add_cancel,
      translatedGenericPoint_zero]
  -- the reduction depends on the place only, not on the proof that it has degree one
  have hred : ∀ {w₁ w₂ : Place F W.FunctionField} (_ : w₁ = w₂) (h₁ : w₁.degree = 1)
      (h₂ : w₂.degree = 1), reductionOfDegreeEqOne W h₁ = reductionOfDegreeEqOne W h₂ := by
    rintro _ _ rfl _ _
    rfl
  rw [← reductionOfDegreeEqOne_genericPoint W R, hred hRv _ hdeg, hgen,
    reductionOfDegreeEqOne_smul_map W σ v.2, translatedGenericPoint_def, map_add,
    reductionOfDegreeEqOne_genericPoint, reductionOfDegreeEqOne_baseChange, map_sub,
    sub_eq_add_neg]

end WeierstrassCurve.Affine

end
