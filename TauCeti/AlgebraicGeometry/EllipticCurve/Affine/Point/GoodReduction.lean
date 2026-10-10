/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction
-- Proof-only: one Bosma–Lenstra law computes a sum over a local ring and all its residue fields.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.LocalRing
-- Proof-only: a nonzero solution on an elliptic curve over a field is nonsingular.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
-- Proof-only: over a local ring, a unimodular vector has a unit coordinate.
import TauCeti.LinearAlgebra.Unimodular

/-!
# Reduction of points at good reduction

Let `v` be a valuation on a field `F`, with valuation ring `O` and residue field `k`, and let `W` be
a Weierstrass curve over `F` with an integral model `W_O` over `O` whose discriminant is a unit of
`O`, so that `W` has good reduction and the reduced curve `W_k = W_O ⊗ k` is an elliptic curve. This
file shows that reduction of points (`WeierstrassCurve.Affine.Point.reduction`) is then a group
homomorphism `W(F) →+ W_k(k)`: Silverman VII.2.1 in the case of good reduction, where the subgroup
`E₀(F)` of points with nonsingular reduction is all of `W(F)`. Its kernel is the kernel of
reduction `E₁(F)`, the points whose `x`-coordinate has a pole.

The proof uses the two Bosma–Lenstra addition laws. Write two points `P` and `Q` as classes of
primitive integral vectors `X` and `Y`. Since the discriminant of `W_O` is a unit, some coordinate
of one of the laws at `(X, Y)` is a unit of `O`. That law is then a primitive integral vector `S`
whose class is `P + Q` over `F` and whose reduction is the sum of the reductions of `X` and `Y`
over `k` (`WeierstrassCurve.Projective.exists_isUnimodular_map_equiv_add`). As reduction is computed
by any primitive representative (`WeierstrassCurve.Affine.Point.reduction_eq_mk`), the reduction of
`P + Q` is the class of the residues of `S`.

## Main definitions

* `WeierstrassCurve.Affine.Point.reductionHom`: at good reduction, the reduction homomorphism
  `W(F) →+ W_k(k)`.

## Main results

* `WeierstrassCurve.Affine.Point.nonsingularLift_reduction`: at good reduction, every point reduces
  to a nonsingular point of the reduced curve.
* `WeierstrassCurve.Affine.Point.reduction_add`: at good reduction, reduction commutes with
  addition.
* `WeierstrassCurve.Affine.Point.reductionHom_eq_zero_iff`: the kernel of the reduction
  homomorphism consists of the point at infinity and the points whose `x`-coordinate has a pole.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

open IsLocalRing

namespace WeierstrassCurve.Affine.Point

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]
  [(integralModel v.valuationSubring W).IsElliptic]

/-- **At good reduction, points reduce to nonsingular points.** If the integral model of `W` has
unit discriminant, the reduction of every point of `W(F)` is a nonsingular point of the reduced
curve. -/
theorem nonsingularLift_reduction (P : W.Point) :
    ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P) := by
  obtain ⟨X, hX, hX₁, hPX⟩ := exists_isUnimodular_toProjective_point_eq v P
  obtain ⟨i, hi⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp hX₁
  rw [reduction_eq_mk v hX₁ hPX, Projective.nonsingularLift_iff]
  exact (Projective.equation_iff_nonsingular_of_ne_zero
    (Function.ne_iff.mpr ⟨i, (hi.map (residue v.valuationSubring)).ne_zero⟩)).mp (hX.map _)

variable [DecidableEq F]

/-- **At good reduction, reduction commutes with addition.** If the integral model of `W` has unit
discriminant, the reduction of `P + Q` is the sum of the reductions of `P` and `Q` on the reduced
curve. -/
@[simp]
theorem reduction_add (P Q : W.Point) :
    reduction v (P + Q) =
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.addMap
        (reduction v P) (reduction v Q) := by
  obtain ⟨X, hX, hX₁, hPX⟩ := exists_isUnimodular_toProjective_point_eq v P
  obtain ⟨Y, hY, hY₁, hQY⟩ := exists_isUnimodular_toProjective_point_eq v Q
  -- one primitive integral vector `S` represents both the sum and the sum of the reductions
  obtain ⟨S, -, hS₁, hS⟩ := Projective.exists_isUnimodular_map_equiv_add hX hY hX₁ hY₁
  -- `baseChange` is `map` along `algebraMap`
  have hW : (integralModel v.valuationSubring W).toProjective.map
      (algebraMap v.valuationSubring F) = W.toProjective :=
    baseChange_integralModel_eq v.valuationSubring W
  have hPQ : (P + Q).toProjective.point = ⟦algebraMap v.valuationSubring F ∘ S⟧ := by
    have hadd : (P + Q).toProjective = P.toProjective + Q.toProjective := by
      simpa only [Projective.Point.toAffineAddEquiv_symm_apply] using
        _root_.map_add (Projective.Point.toAffineAddEquiv W.toProjective).symm P Q
    have hSF := hS (algebraMap v.valuationSubring F)
    rw [hW] at hSF
    rw [hadd, Projective.Point.add_point, hPX, hQY, Projective.addMap_eq]
    exact (Quotient.sound hSF).symm
  rw [reduction_eq_mk v hS₁ hPQ, reduction_eq_mk v hX₁ hPX, reduction_eq_mk v hY₁ hQY,
    Projective.addMap_eq]
  exact Quotient.sound (hS (residue v.valuationSubring))

variable [DecidableEq (ResidueField v.valuationSubring)]

-- The reduction of a point, as a nonsingular projective point of the reduced curve.
private noncomputable def reductionPoint (P : W.Point) :
    ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.Point :=
  ⟨nonsingularLift_reduction v P⟩

/-- **The reduction homomorphism** at good reduction. If the integral model of `W` has unit
discriminant, reduction of points is a group homomorphism `W(F) →+ W_k(k)` to the points of the
reduced curve: a point with integral `x`-coordinate goes to the residues of its coordinates
(`reductionHom_some_of_valuation_le_one`), and the other points go to the point at infinity. -/
noncomputable def reductionHom :
    W.Point →+
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Point where
  toFun P := (reductionPoint v P).toAffineLift
  map_zero' := by
    have h0 : reductionPoint v 0 = 0 :=
      Projective.Point.ext ((reduction_zero (W := W) v).trans Projective.Point.zero_point.symm)
    rw [h0, Projective.Point.toAffineLift_zero]
  map_add' P Q := by
    have hadd : reductionPoint v (P + Q) = reductionPoint v P + reductionPoint v Q :=
      Projective.Point.ext ((reduction_add v P Q).trans
        (Projective.Point.add_point (reductionPoint v P) (reductionPoint v Q)).symm)
    rw [hadd, Projective.Point.toAffineLift_add]

/-- The reduction homomorphism, read in projective coordinates, is the reduction of points. -/
@[simp]
theorem reductionHom_toProjective_point (P : W.Point) :
    (reductionHom v P).toProjective.point = reduction v P :=
  -- `reductionHom v P` is `toAffineLift` of the projective point `reductionPoint v P`
  congrArg Projective.Point.point
    ((Projective.Point.toAffineAddEquiv _).symm_apply_apply (reductionPoint v P))

/-- At good reduction, a point with integral `x`-coordinate reduces to the residues of its
coordinates. -/
theorem reductionHom_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y) (hx : v x ≤ 1)
    (h' : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)) :
    reductionHom v (some x y h) = some _ _ h' := by
  apply (Projective.Point.toAffineAddEquiv _).symm.injective
  rw [Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.toAffineAddEquiv_symm_apply,
    Projective.Point.fromAffine_some]
  exact Projective.Point.ext ((reductionHom_toProjective_point v _).trans
    (reduction_some_of_valuation_le_one v h hx))

/-- At good reduction, a point whose `x`-coordinate has a pole reduces to the point at infinity. -/
@[simp]
theorem reductionHom_some_of_one_lt {x y : F} (h : W.Nonsingular x y) (hx : 1 < v x) :
    reductionHom v (some x y h) = 0 := by
  apply (Projective.Point.toAffineAddEquiv _).symm.injective
  rw [_root_.map_zero, Projective.Point.toAffineAddEquiv_symm_apply]
  exact Projective.Point.ext ((reductionHom_toProjective_point v _).trans
    ((reduction_some_of_one_lt v h hx).trans Projective.Point.zero_point.symm))

/-- **The kernel of reduction** at good reduction: a point reduces to the point at infinity exactly
when it is the point at infinity or its `x`-coordinate has a pole. -/
theorem reductionHom_eq_zero_iff (P : W.Point) :
    reductionHom v P = 0 ↔ P = 0 ∨ 1 < v P.xCoord := by
  rw [← reduction_eq_zero_iff, ← reductionHom_toProjective_point,
    ← (Projective.Point.toAffineAddEquiv _).symm.injective.eq_iff, _root_.map_zero,
    Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.ext_iff,
    Projective.Point.zero_point]

end WeierstrassCurve.Affine.Point

end
