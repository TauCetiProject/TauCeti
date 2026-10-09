/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction

/-!
# Point reduction at good reduction

Let `v` be a valuation on a field `F`, let `O` be its valuation ring, and let `W` be a
Weierstrass curve over `F` with an integral model over `O`. The projective-coordinate reduction
`WeierstrassCurve.Affine.Point.reduction` always lies on the reduced cubic, but at bad reduction
it can be singular. If the reduced integral model is elliptic, reduction instead gives an honest
point of the reduced elliptic curve.

This file makes that passage explicit. By `unimodularLift_reduction`, reduction is represented
by a solution with unimodular coordinates. At good reduction this is nonsingular,
so `reductionPoint` reads it as a point in Mathlib's affine point group. Its projective point is
exactly the original projective-coordinate reduction; the zero, affine-coordinate, kernel, and
negation formulae therefore descend without any choice of representatives.

## Main definitions

* `WeierstrassCurve.Affine.Point.reductionProjective`: reduction as a nonsingular projective point
  when the reduced model is elliptic.
* `WeierstrassCurve.Affine.Point.reductionPoint`: reduction as an affine point of the reduced
  elliptic curve.

## Main results

* `WeierstrassCurve.Affine.Point.reductionPoint_toProjective_point`: the underlying projective
  class is `reduction`.
* `WeierstrassCurve.Affine.Point.reductionPoint_eq_zero_iff`: the kernel criterion for the typed
  reduction map.
* `WeierstrassCurve.Affine.Point.reductionPoint_neg`: typed reduction commutes with negation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.
-/

public section

namespace WeierstrassCurve.Affine.Point

open IsLocalRing

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀) {W : WeierstrassCurve.Affine F}
  [WeierstrassCurve.IsIntegral v.valuationSubring W]

variable [((integralModel v.valuationSubring W).map
  (residue v.valuationSubring)).IsElliptic]

/-- At good reduction, projective-coordinate reduction is a nonsingular projective point of the
reduced elliptic curve. -/
theorem nonsingularLift_reduction (P : W.Point) :
    ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P) :=
  Projective.unimodularLift_iff_nonsingularLift.mp (unimodularLift_reduction v P)

/-- **Reduction as a nonsingular projective point at good reduction.** Its underlying projective
class is `reduction v P`; see `reductionProjective_point`. -/
noncomputable def reductionProjective (P : W.Point) :
  ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.Point :=
  ⟨nonsingularLift_reduction v P⟩

/-- The projective class underlying `reductionProjective` is the original coordinate reduction. -/
@[simp]
theorem reductionProjective_point (P : W.Point) :
    (reductionProjective v P).point = reduction v P :=
  (rfl)

/-- **Reduction as an affine point of the reduced elliptic curve at good reduction.** -/
noncomputable def reductionPoint (P : W.Point) :
    ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Point :=
  (reductionProjective v P).toAffineLift

/-- The projective point underlying `reductionPoint` is the original projective-coordinate
reduction. -/
@[simp]
theorem reductionPoint_toProjective_point (P : W.Point) :
    (reductionPoint v P).toProjective.point = reduction v P := by
  classical
  rw [reductionPoint, ← reductionProjective_point]
  exact congrArg Projective.Point.point
    ((Projective.Point.toAffineAddEquiv ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective).left_inv
      (reductionProjective v P))

/-- The point at infinity reduces to the point at infinity. -/
@[simp]
theorem reductionPoint_zero : reductionPoint v (0 : W.Point) = 0 := by
  rw [reductionPoint]
  have h : reductionProjective v (0 : W.Point) = 0 := by
    apply Projective.Point.ext
    rw [reductionProjective_point, Projective.Point.zero_point, reduction_zero]
  rw [h, Projective.Point.toAffineLift_zero]

/-- A point with integral `x`-coordinate reduces by reducing its affine coordinates. -/
@[simp]
theorem reductionPoint_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y)
    (hx : v x ≤ 1) :
    reductionPoint v (some x y h) =
      some (residue v.valuationSubring ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue v.valuationSubring ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩) (by
            rw [← Projective.nonsingular_some]
            rw [← Projective.nonsingularLift_iff]
            simpa only [reduction_some_of_valuation_le_one v h hx] using
              nonsingularLift_reduction v (some x y h)) := by
  rw [reductionPoint]
  let hred : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift
      ⟦![residue v.valuationSubring ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩,
        residue v.valuationSubring ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩, 1]⟧ := by
    simpa only [reduction_some_of_valuation_le_one v h hx] using
      nonsingularLift_reduction v (some x y h)
  have hp : reductionProjective v (some x y h) = ⟨hred⟩ := by
    apply Projective.Point.ext
    exact reduction_some_of_valuation_le_one v h hx
  rw [hp, Projective.Point.toAffineLift_some]

/-- A point whose `x`-coordinate has a pole reduces to the point at infinity. -/
@[simp]
theorem reductionPoint_some_of_one_lt {x y : F} (h : W.Nonsingular x y) (hx : 1 < v x) :
    reductionPoint v (some x y h) = 0 := by
  rw [reductionPoint]
  have hp : reductionProjective v (some x y h) = 0 := by
    apply Projective.Point.ext
    rw [reductionProjective_point, Projective.Point.zero_point,
      reduction_some_of_one_lt v h hx]
  rw [hp, Projective.Point.toAffineLift_zero]

/-- **Kernel criterion for typed reduction.** A point reduces to zero exactly when it is the point
at infinity or its `x`-coordinate has a pole. -/
theorem reductionPoint_eq_zero_iff (P : W.Point) :
    reductionPoint v P = 0 ↔ P = 0 ∨ 1 < v P.xCoord := by
  rw [← reduction_eq_zero_iff v P]
  constructor
  · intro h
    simpa only [reductionPoint_toProjective_point, Projective.Point.fromAffine_zero,
      Projective.Point.zero_point] using
      congrArg (fun Q ↦ Q.toProjective.point) h
  · intro h
    rw [reductionPoint]
    have hp : reductionProjective v P = 0 := by
      apply Projective.Point.ext
      simpa only [reductionProjective_point, Projective.Point.zero_point] using h
    rw [hp, Projective.Point.toAffineLift_zero]

/-- **Typed reduction commutes with negation.** -/
@[simp]
theorem reductionPoint_neg (P : W.Point) : reductionPoint v (-P) = -reductionPoint v P := by
  rw [reductionPoint, reductionPoint, ← Projective.Point.toAffineLift_neg]
  congr 1
  apply Projective.Point.ext
  exact reduction_neg v P

end WeierstrassCurve.Affine.Point

end
