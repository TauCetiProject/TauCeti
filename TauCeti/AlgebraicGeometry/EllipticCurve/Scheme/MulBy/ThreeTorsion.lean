/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Points killed by `3` on the projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, with projective model
`E = projModel W` over `Spec R`, and let `(x, y)` be a solution of the affine Weierstrass equation
over `R`. This file shows that the point `P = [x : y : 1]` of `E` with values in `R` is killed by
multiplication by `3`, as a morphism `Spec R ⟶ E`, exactly when `x` is a root of the
`3`-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`
(`WeierstrassCurve.projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff`).

No hypothesis on `R` is needed. In particular `R` may be nonreduced, so the statement is an
equality of morphisms of schemes and not merely of their values at the points of `Spec R`. The
pointwise statement, that `3P` misses the zero section over a point `s` of `Spec R` exactly when
`Ψ₃(x) ∉ s`, is `WeierstrassCurve.projModelAffinePoint_projModelMulBy_ne_projModelZero_iff`.

The proof computes `2P` on homogeneous coordinates. Write `ψ₂ = 2y + a₁x + a₃`. If `ψ₂` is a unit
of `R`, the second Bosma–Lenstra addition law, whose diagonal is the doubling formula
`WeierstrassCurve.Projective.dblXYZ`, computes the addition morphism at `(P, P)`
(`WeierstrassCurve.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ`), and on the curve

  `dblXYZ [x : y : 1] = ψ₂³ • [x : -y - a₁x - a₃ : 1] - Ψ₃(x) • [ψ₂ : W_X(x, y) - a₁ψ₂ : 0]`,

where `W_X = a₁y - (3x² + 2a₂x + a₄)` is the partial derivative of the Weierstrass equation in
`x`. The first term represents `-P`, so `2P = -P`, equivalently `3P = 0`, exactly when
`Ψ₃(x) = 0`. The unit hypothesis on `ψ₂` costs nothing. If `3P = 0`, then `2P = -P` misses the
zero section everywhere, which makes `ψ₂` a unit (`WeierstrassCurve.isUnit_evalEval_ψ_iff`).
Conversely, `Ψ₃(x) = 0` makes `ψ₂` a unit on an elliptic curve
(`WeierstrassCurve.isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero`).

This is the scheme-theoretic counterpart, over an arbitrary base ring, of the equation-level
description of points of order `3` as the points with `Ψ₃(x) = 0`. It identifies the condition
`Ψ₃(x) = 0` in the equation-level description of a basis of the `3`-torsion
(`WeierstrassCurve.IsThreeTorsionBasis`), on which the level-three normal form rests, with the
scheme-theoretic condition `3P = 0`.

## Main results

* `WeierstrassCurve.projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff`: the point
  `[x : y : 1]` is killed by `3` if and only if `Ψ₃(x) = 0`.

The two equation-level inputs are `WeierstrassCurve.Projective.dblXYZ_some`, the doubling formula
at `[x : y : 1]` displayed above, and `WeierstrassCurve.isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 3.7, for the
  division polynomials and the points of order `3`.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj Polynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic]

-- If `ψ₂(x, y)` is a unit, then `2P = -P` exactly when `Ψ₃(x) = 0`.
private theorem projModelAffinePoint_projModelMulBy_two_eq_projModelNeg_iff {x y : R}
    (h : W.toAffine.Equation x y) (hψ₂ : IsUnit (W.ψ₂.evalEval x y)) :
    W.projModelAffinePoint h ≫ W.projModelMulBy 2 = W.projModelAffinePoint h ≫ W.projModelNeg ↔
      W.Ψ₃.eval x = 0 := by
  -- `W.map (RingHom.id R)` is `W` only up to unfolding `Projective.map`, so it is rewritten away
  have hW : W.toProjective.map (RingHom.id R) = W.toProjective := W.map_id
  have hE : W.toProjective.Equation ![x, y, 1] := (Projective.equation_some _ _).mpr h
  have hdbl : (W.toProjective.map (RingHom.id R)).dblAddXYZ ![x, y, 1] ![x, y, 1] =
      W.toProjective.dblXYZ ![x, y, 1] := by
    rw [Projective.dblAddXYZ_self (hW ▸ hE), hW]
  have hm : IsUnit ((W.toProjective.map (RingHom.id R)).dblAddXYZ ![x, y, 1] ![x, y, 1] 2) := by
    rw [hdbl, Projective.dblXYZ_some h]
    simpa using hψ₂.pow 3
  rw [comp_projModelMulBy_two (projModelAffinePoint_projModelOver h),
    projModelAffinePoint_projModelNeg, projModelAffinePoint_def, projModelAffinePoint_def,
    lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (hm := hm),
    projModelPoint_eq_projModelPoint_iff, hdbl, Projective.dblXYZ_some h]
  refine ⟨fun ⟨_, u, hu⟩ ↦ ?_, fun h₃ ↦ ⟨rfl, (hψ₂.pow 3).unit, by simp [h₃]⟩⟩
  -- the `Z`-coordinates force `u = ψ₂³`, and then the `X`-coordinates give `Ψ₃(x) ψ₂ = 0`
  have hz := congrFun hu 2
  have hx := congrFun hu 0
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, smul_eq_mul, mul_zero, add_zero, Units.smul_def] at hz hx
  exact hψ₂.mul_left_eq_zero.mp (by linear_combination -hx + x * hz)

/-- **Points killed by `3`.** Let `W` be an elliptic Weierstrass curve over a commutative ring `R`
and `(x, y)` a solution of its affine equation over `R`. The point `[x : y : 1]` of the projective
model with values in `R` is killed by multiplication by `3`, as a morphism `Spec R ⟶ projModel W`,
if and only if `x` is a root of the `3`-division polynomial `Ψ₃`. -/
theorem projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff {x y : R}
    (h : W.toAffine.Equation x y) :
    W.projModelAffinePoint h ≫ W.projModelMulBy 3 = W.projModelZero ↔ W.Ψ₃.eval x = 0 := by
  rw [show (3 : ℤ) = 2 + 1 by norm_num,
    comp_projModelMulBy_add_one_eq_projModelZero_iff (projModelAffinePoint_projModelOver h)]
  refine ⟨fun h₂ ↦ (projModelAffinePoint_projModelMulBy_two_eq_projModelNeg_iff h ?_).mp h₂,
    fun h₃ ↦ (projModelAffinePoint_projModelMulBy_two_eq_projModelNeg_iff h
      (isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero h h₃)).mpr h₃⟩
  -- `2P = -P` misses the zero section everywhere, so `ψ₂(x, y)` is a unit
  rw [← ψ_two, isUnit_evalEval_ψ_iff h 2, h₂, projModelAffinePoint_projModelNeg]
  exact fun s ↦ (ne_projModelZero_iff_mem_basicOpen (by simp) s).mpr
    (projModelAffinePoint_mem_basicOpen _ s)

end WeierstrassCurve
