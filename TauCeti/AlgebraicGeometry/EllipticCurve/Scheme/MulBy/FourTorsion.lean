/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateNormalForm

/-!
# The `4`-torsion locus of `(0, 0)` on the Tate normal form

Let `W = tateNormalForm a b` be an elliptic Tate normal form `Y² + aXY + bY = X³ + bX²` over a
commutative ring `R`, where `b` is a unit, with projective model `E = projModel W` over `Spec R`.
The second Bosma–Lenstra addition law computes the double of `[0 : 0 : 1]` on the projective model
as `2 • [0 : 0 : 1] = [-b : b(a - 1) : 1]`
(`WeierstrassCurve.tateNormalForm_projModelMulBy_two_zero`). At `(-b, b(a - 1))` the `2`-division
polynomial takes the value `b(a - 1)`, without a factor of `2`, so
`WeierstrassCurve.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff` shows over any
commutative ring `R` that `4 • [0 : 0 : 1] = 0` on an elliptic Tate normal form if and only if
`a = 1` (`WeierstrassCurve.tateNormalForm_projModelMulBy_four_eq_projModelZero_iff`).

## Main results

* `WeierstrassCurve.tateNormalForm_projModelMulBy_two_zero`: on an elliptic Tate normal form
  `Y² + aXY + bY = X³ + bX²`, doubling `[0 : 0 : 1]` gives `[-b : b(a - 1) : 1]`.
* `WeierstrassCurve.tateNormalForm_projModelMulBy_four_eq_projModelZero_iff`: on an elliptic Tate
  normal form, `[0 : 0 : 1]` is killed by `4` if and only if `a = 1`.

## References

* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237, Table 3 (`X₁(4)`).
* D. Loeffler, *Modular Curves*, lecture notes, §3.3.
-/

public section

open CategoryTheory

universe u

namespace WeierstrassCurve

section TateNormalFormScheme

variable {R : Type u} [CommRing R] {a b : R} [(tateNormalForm a b).IsElliptic]

/-- **Doubling `(0, 0)` on an elliptic Tate normal form.** On `Y² + aXY + bY = X³ + bX²`, doubling
the section `[0 : 0 : 1]` of the projective model yields `[-b : b(a - 1) : 1]`. -/
theorem tateNormalForm_projModelMulBy_two_zero :
    (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫
        (tateNormalForm a b).projModelMulBy 2 =
      (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_neg_mul_sub_one a b) := by
  set W := tateNormalForm a b
  have hb : IsUnit b := isUnit_of_isUnit_tateNormalForm_Δ W.isUnit_Δ
  have h₀ : W.toAffine.Equation 0 0 := equation_tateNormalForm_zero a b
  have hW : W.toProjective.map (RingHom.id R) = W.toProjective := W.map_id
  have hE : W.toProjective.Equation ![0, 0, 1] := (Projective.equation_some _ _).mpr h₀
  have hdbl : (W.toProjective.map (RingHom.id R)).dblAddXYZ ![0, 0, 1] ![0, 0, 1] =
      W.toProjective.dblXYZ ![0, 0, 1] := by
    rw [Projective.dblAddXYZ_self (hW ▸ hE), hW]
  have hm : IsUnit ((W.toProjective.map (RingHom.id R)).dblAddXYZ ![0, 0, 1] ![0, 0, 1] 2) := by
    rw [hdbl, Projective.dblXYZ_some h₀]
    simpa [W] using hb.pow 3
  rw [comp_projModelMulBy_two, projModelAffinePoint_def, projModelAffinePoint_def,
    lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (hm := hm),
    projModelPoint_eq_projModelPoint_iff, hdbl, Projective.dblXYZ_some h₀]
  refine ⟨rfl, (hb.pow 3).unit, ?_⟩
  ext i
  fin_cases i <;>
    simp [W, Affine.negY, Affine.evalEval_polynomialX, Units.smul_def]
  ring

/-- **The `4`-torsion locus of `(0, 0)` on an elliptic Tate normal form.** Over any commutative
ring `R`, the point `[0 : 0 : 1]` of an elliptic Tate normal form `Y² + aXY + bY = X³ + bX²` is
killed by multiplication by `4` if and only if `a = 1`. -/
theorem tateNormalForm_projModelMulBy_four_eq_projModelZero_iff :
    (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫
        (tateNormalForm a b).projModelMulBy 4 = (tateNormalForm a b).projModelZero ↔
      a = 1 := by
  have hb : IsUnit b := isUnit_of_isUnit_tateNormalForm_Δ (tateNormalForm a b).isUnit_Δ
  have h4 : (tateNormalForm a b).projModelMulBy 4 =
      (tateNormalForm a b).projModelMulBy 2 ≫ (tateNormalForm a b).projModelMulBy 2 := by
    simpa using projModelMulBy_mul (tateNormalForm a b) 2 2
  rw [h4, ← Category.assoc, tateNormalForm_projModelMulBy_two_zero,
    projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff,
    evalEval_ψ₂_tateNormalForm_neg_mul_sub_one, hb.mul_right_eq_zero, sub_eq_zero]

end TateNormalFormScheme

end WeierstrassCurve
