/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Reduction
-- Proof-only: one Bosma–Lenstra law computes a sum over a local ring and all its residue fields.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.LocalRing

/-!
# Points with nonsingular reduction

Let `v` be a valuation on a field `F`, with valuation ring `O` and residue field `k`, and let `W`
be a Weierstrass curve over `F` with an integral model `W_O` over `O`. Every point of `W(F)` reduces
to a `k`-point of the reduced curve `W_k = W_O ⊗ k` (`WeierstrassCurve.Affine.Point.reduction`).
When `W_k` is singular, the reduction of a point may be its singular point. This file defines the
subgroup

`E₀(F) = {P ∈ W(F) | the reduction of P is a nonsingular point of W_k}`

and shows that reduction is a group homomorphism `E₀(F) →+ W_k,ns(k)` to the group of nonsingular
points of `W_k`, whose kernel is the kernel of reduction `E₁(F)`: the point at infinity together
with the points whose `x`-coordinate has a pole. This is the left-exact part of Silverman's exact
sequence `0 → E₁(F) → E₀(F) → W_k,ns(k) → 0` (AEC VII.2.1), for an arbitrary valuation and an
arbitrary integral model. The hypotheses are those of the statement: neither ellipticity of `W`,
minimality of `W_O`, discreteness of `v` nor completeness of `F` is assumed.

## Main definitions

* `WeierstrassCurve.Affine.nonsingularReduction`: the subgroup `E₀(F)` of points whose
  reduction is a nonsingular point of the reduced curve.
* `WeierstrassCurve.Affine.nonsingularReductionHom`: the reduction homomorphism
  `E₀(F) →+ W_k,ns(k)`.

## Main results

* `WeierstrassCurve.Affine.Point.reduction_add_of_nonsingularLift`: if `P` and `Q` reduce to
  nonsingular points, then the reduction of `P + Q` is the sum of their reductions.
* `WeierstrassCurve.Affine.some_mem_nonsingularReduction_iff`: an affine point with integral
  coordinates lies in `E₀(F)` exactly when the residues of its coordinates form a nonsingular point
  of the reduced curve.
* `WeierstrassCurve.Affine.mem_nonsingularReduction_of_one_lt`: the kernel of reduction is
  contained in `E₀(F)`.
* `WeierstrassCurve.Affine.nonsingularReductionHom_eq_zero_iff`: the kernel of the reduction
  homomorphism is the kernel of reduction `E₁(F)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

open IsLocalRing

namespace WeierstrassCurve.Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

namespace Point

/-- **Reduction commutes with addition on points with nonsingular reduction.** If `P` and `Q`
reduce to nonsingular points of the reduced curve, then the reduction of `P + Q` is the sum of the
reductions of `P` and `Q` on the reduced curve. -/
theorem reduction_add_of_nonsingularLift {P Q : W.Point}
    (hP : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v P))
    (hQ : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (reduction v Q)) :
    reduction v (P + Q) =
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toProjective.addMap
        (reduction v P) (reduction v Q) := by
  -- Write `P` and `Q` as classes of primitive integral vectors `X` and `Y`. Their residues are
  -- nonsingular points of the reduced curve, where the two Bosma–Lenstra laws do not vanish
  -- simultaneously, so some coordinate of one of the laws at `(X, Y)` is a unit. That law is then
  -- a primitive integral vector `S` whose class is `P + Q` over `F` and whose reduction is the sum
  -- of the reductions of `X` and `Y` over the residue field.
  obtain ⟨X, hX, hX₁, hPX⟩ := exists_isUnimodular_toProjective_point_eq v P
  obtain ⟨Y, hY, hY₁, hQY⟩ := exists_isUnimodular_toProjective_point_eq v Q
  rw [reduction_eq_mk v hX₁ hPX, Projective.nonsingularLift_iff] at hP
  rw [reduction_eq_mk v hY₁ hQY, Projective.nonsingularLift_iff] at hQ
  obtain ⟨S, -, hS₁, hS⟩ := Projective.exists_isUnimodular_map_equiv_add hX hY hP hQ
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

end Point

variable (W) in
/-- **The subgroup `E₀(F)` of points with nonsingular reduction**: the points of `W(F)` whose
reduction is a nonsingular point of the reduced curve. -/
noncomputable def nonsingularReduction : AddSubgroup W.Point where
  carrier := {P | ((integralModel v.valuationSubring W).map
    (residue v.valuationSubring)).toProjective.NonsingularLift (Point.reduction v P)}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, Point.reduction_zero, Projective.nonsingularLift_iff]
    exact Projective.nonsingular_zero
  add_mem' {P Q} hP hQ := by
    rw [Set.mem_ofPred_eq, Point.reduction_add_of_nonsingularLift v hP hQ]
    exact Projective.nonsingularLift_addMap hP hQ
  neg_mem' {P} hP := by
    rw [Set.mem_ofPred_eq, Point.reduction_neg]
    exact Projective.nonsingularLift_negMap hP

/-- A point lies in `E₀(F)` exactly when its reduction is a nonsingular point of the reduced curve.
-/
theorem mem_nonsingularReduction_iff {P : W.Point} :
    P ∈ W.nonsingularReduction v ↔ ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toProjective.NonsingularLift (Point.reduction v P) :=
  Iff.rfl

/-- An affine point with integral `x`-coordinate has nonsingular reduction exactly when the
residues of its coordinates form a nonsingular point of the reduced curve. -/
@[simp]
theorem some_mem_nonsingularReduction_iff {x y : F} (h : W.Nonsingular x y) (hx : v x ≤ 1) :
    Point.some x y h ∈ W.nonsingularReduction v ↔
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩) := by
  rw [mem_nonsingularReduction_iff, Point.reduction_some_of_valuation_le_one v h hx,
    Projective.nonsingularLift_some]

/-- **The kernel of reduction is contained in `E₀(F)`**: a point whose `x`-coordinate has a pole
reduces to the point at infinity, which is nonsingular. -/
theorem mem_nonsingularReduction_of_one_lt {P : W.Point} (hP : 1 < v P.xCoord) :
    P ∈ W.nonsingularReduction v := by
  rw [mem_nonsingularReduction_iff, (Point.reduction_eq_zero_iff v P).mpr (.inr hP),
    Projective.nonsingularLift_iff]
  exact Projective.nonsingular_zero

variable [DecidableEq (ResidueField v.valuationSubring)]

variable (W) in
/-- **The reduction homomorphism** `E₀(F) →+ W_k,ns(k)`, from the points with nonsingular
reduction to the group of nonsingular points of the reduced curve. A point with integral
`x`-coordinate goes to the residues of its coordinates
(`nonsingularReductionHom_some_of_valuation_le_one`), and the other points go to the point at
infinity. -/
noncomputable def nonsingularReductionHom :
    W.nonsingularReduction v →+
      ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.Point where
  toFun P := (⟨P.2⟩ : Projective.Point _).toAffineLift
  map_zero' := by
    have h0 : (⟨(W.nonsingularReduction v).zero_mem⟩ : Projective.Point _) = 0 :=
      Projective.Point.ext ((Point.reduction_zero (W := W) v).trans
        Projective.Point.zero_point.symm)
    exact h0 ▸ Projective.Point.toAffineLift_zero
  map_add' P Q := by
    have hadd : (⟨(P + Q).2⟩ : Projective.Point _) = ⟨P.2⟩ + ⟨Q.2⟩ :=
      Projective.Point.ext ((Point.reduction_add_of_nonsingularLift v P.2 Q.2).trans
        (Projective.Point.add_point ⟨P.2⟩ ⟨Q.2⟩).symm)
    exact hadd ▸ Projective.Point.toAffineLift_add _ _

/-- The reduction homomorphism, read in projective coordinates, is the reduction of points. -/
@[simp]
theorem nonsingularReductionHom_toProjective_point (P : W.nonsingularReduction v) :
    (W.nonsingularReductionHom v P).toProjective.point = Point.reduction v (P : W.Point) :=
  -- `nonsingularReductionHom v P` is `toAffineLift` of the nonsingular projective point `⟨P.2⟩`
  congrArg Projective.Point.point ((Projective.Point.toAffineAddEquiv _).symm_apply_apply ⟨P.2⟩)

/-- A point with nonsingular reduction and integral `x`-coordinate reduces to the residues of its
coordinates. -/
theorem nonsingularReductionHom_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y)
    (hx : v x ≤ 1)
    (h' : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)) :
    W.nonsingularReductionHom v
        ⟨Point.some x y h, (some_mem_nonsingularReduction_iff v h hx).mpr h'⟩ =
      Point.some _ _ h' := by
  apply (Projective.Point.toAffineAddEquiv _).symm.injective
  rw [Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.toAffineAddEquiv_symm_apply,
    Projective.Point.fromAffine_some]
  exact Projective.Point.ext ((nonsingularReductionHom_toProjective_point v _).trans
    (Point.reduction_some_of_valuation_le_one v h hx))

/-- **The kernel of the reduction homomorphism is the kernel of reduction** `E₁(F)`: a point with
nonsingular reduction reduces to the point at infinity exactly when it is the point at infinity or
its `x`-coordinate has a pole. -/
theorem nonsingularReductionHom_eq_zero_iff (P : W.nonsingularReduction v) :
    W.nonsingularReductionHom v P = 0 ↔ (P : W.Point) = 0 ∨ 1 < v (P : W.Point).xCoord := by
  rw [← Point.reduction_eq_zero_iff, ← nonsingularReductionHom_toProjective_point,
    ← (Projective.Point.toAffineAddEquiv _).symm.injective.eq_iff, _root_.map_zero,
    Projective.Point.toAffineAddEquiv_symm_apply, Projective.Point.ext_iff,
    Projective.Point.zero_point]

end WeierstrassCurve.Affine

end
