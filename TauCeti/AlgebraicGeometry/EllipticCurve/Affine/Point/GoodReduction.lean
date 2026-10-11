/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
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
`E₀(F)` of points with nonsingular reduction (`WeierstrassCurve.Affine.nonsingularReduction`) is all
of `W(F)`. Its kernel is the kernel of reduction `E₁(F)`, the points whose `x`-coordinate has a
pole.

Since the reduced curve is elliptic, every point of it is nonsingular, so every point of `W(F)` has
nonsingular reduction. The reduction homomorphism is then the homomorphism
`WeierstrassCurve.Affine.nonsingularReductionHom` on `E₀(F) = W(F)`.

## Main definitions

* `WeierstrassCurve.Affine.Point.reductionHom`: at good reduction, the reduction homomorphism
  `W(F) →+ W_k(k)`.

## Main results

* `WeierstrassCurve.Affine.Point.nonsingularLift_reduction`: at good reduction, every point reduces
  to a nonsingular point of the reduced curve.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top`: at good reduction, every point has
  nonsingular reduction.
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

/-- **At good reduction, every point has nonsingular reduction**: `E₀(F) = W(F)`. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.nonsingularReduction_eq_top :
    W.nonsingularReduction v = ⊤ :=
  eq_top_iff.mpr fun P _ ↦ (mem_nonsingularReduction_iff v).mpr (nonsingularLift_reduction v P)

/-- **At good reduction, reduction commutes with addition.** If the integral model of `W` has unit
discriminant, the reduction of `P + Q` is the sum of the reductions of `P` and `Q` on the reduced
curve. -/
@[simp]
theorem reduction_add (P Q : W.Point) :
    reduction v (P + Q) =
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.addMap
        (reduction v P) (reduction v Q) :=
  reduction_add_of_nonsingularLift v (nonsingularLift_reduction v P) (nonsingularLift_reduction v Q)

variable [DecidableEq (ResidueField v.valuationSubring)]

/-- **The reduction homomorphism** at good reduction. If the integral model of `W` has unit
discriminant, reduction of points is a group homomorphism `W(F) →+ W_k(k)` to the points of the
reduced curve: a point with integral `x`-coordinate goes to the residues of its coordinates
(`reductionHom_some_of_valuation_le_one`), and the other points go to the point at infinity. It is
the reduction homomorphism `WeierstrassCurve.Affine.nonsingularReductionHom` on `E₀(F) = W(F)`. -/
noncomputable def reductionHom :
    W.Point →+
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Point :=
  (W.nonsingularReductionHom v).comp <| (AddMonoidHom.id W.Point).codRestrict _
    fun P ↦ (mem_nonsingularReduction_iff v).mpr (nonsingularLift_reduction v P)

/-- At good reduction, the reduction homomorphism is the reduction homomorphism on points with
nonsingular reduction. -/
theorem reductionHom_apply (P : W.Point) (hP : P ∈ W.nonsingularReduction v) :
    reductionHom v P = W.nonsingularReductionHom v ⟨P, hP⟩ :=
  (rfl)

/-- The reduction homomorphism, read in projective coordinates, is the reduction of points. -/
@[simp]
theorem reductionHom_toProjective_point (P : W.Point) :
    (reductionHom v P).toProjective.point = reduction v P := by
  rw [reductionHom_apply v P (by simp), nonsingularReductionHom_toProjective_point]

/-- At good reduction, a point with integral `x`-coordinate reduces to the residues of its
coordinates. -/
theorem reductionHom_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y) (hx : v x ≤ 1)
    (h' : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)) :
    reductionHom v (some x y h) = some _ _ h' := by
  rw [reductionHom_apply v _ ((some_mem_nonsingularReduction_iff v h hx).mpr h')]
  exact nonsingularReductionHom_some_of_valuation_le_one v h hx h'

/-- **The kernel of reduction** at good reduction: a point reduces to the point at infinity exactly
when it is the point at infinity or its `x`-coordinate has a pole. -/
theorem reductionHom_eq_zero_iff (P : W.Point) :
    reductionHom v P = 0 ↔ P = 0 ∨ 1 < v P.xCoord := by
  rw [reductionHom_apply v P (by simp), nonsingularReductionHom_eq_zero_iff]

/-- At good reduction, a point whose `x`-coordinate has a pole reduces to the point at infinity. -/
@[simp]
theorem reductionHom_some_of_one_lt {x y : F} (h : W.Nonsingular x y) (hx : 1 < v x) :
    reductionHom v (some x y h) = 0 :=
  (reductionHom_eq_zero_iff v _).mpr (.inr (by rwa [xCoord_some]))

end WeierstrassCurve.Affine.Point

end
