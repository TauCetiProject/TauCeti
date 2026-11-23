/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg

/-!
# Points killed by `2` on the projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, with projective model
`E = projModel W` over `Spec R`, and let `(x, y)` be a solution of the affine Weierstrass equation
over `R`. This file shows that a section `P` of `E` is killed by multiplication by `2` exactly when
it is fixed by negation (`WeierstrassCurve.comp_projModelMulBy_two_eq_projModelZero_iff`), and that
for an affine point `P = [x : y : 1]` this holds as an equality of morphisms `Spec R ⟶ E` over any
(possibly nonreduced) commutative ring `R` if and only if `ψ₂(x, y) = 2y + a₁x + a₃ = 0`
(`WeierstrassCurve.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff`).

When `P₁ = [x₁ : y₁ : 1]` is killed by `2`, it equals its own negative, so another affine point
`P₂ = [x₂ : y₂ : 1]` agrees with `P₁` over a point `s` of `Spec R` if and only if `x₂ ≡ x₁` modulo
`s` (`WeierstrassCurve.projModelAffinePoint_apply_eq_iff_of_projModelMulBy_two`), and `P₂` differs
from `P₁` at every point of `Spec R` if and only if `x₂ - x₁` is a unit of `R`
(`WeierstrassCurve.forall_projModelAffinePoint_apply_ne_iff_isUnit_sub`).

## Main results

* `WeierstrassCurve.comp_projModelMulBy_two_eq_projModelZero_iff`: a section `P` is killed by `2`
  if and only if `P ≫ projModelNeg = P`.
* `WeierstrassCurve.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff`: the affine point
  `[x : y : 1]` is killed by `2` if and only if `ψ₂(x, y) = 0`.
* `WeierstrassCurve.forall_projModelAffinePoint_apply_ne_iff_isUnit_sub`: when `[x₁ : y₁ : 1]` is
  killed by `2`, `[x₂ : y₂ : 1]` differs from `[x₁ : y₁ : 1]` at every point of `Spec R` if and
  only if `x₂ - x₁` is a unit.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2 and Exercise 3.7.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.9.
-/

public section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic]

/-- For a section `P` of the projective model, `2P = 0` if and only if `P` is fixed by negation. -/
theorem comp_projModelMulBy_two_eq_projModelZero_iff {P : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) :
    P ≫ W.projModelMulBy 2 = W.projModelZero ↔ P ≫ W.projModelNeg = P := by
  have h1 : P ≫ W.projModelMulBy 1 = P := by
    rw [comp_projModelMulBy_eq_homMk_zpow_left hP 1, zpow_one]
    rfl
  rw [← one_add_one_eq_two, comp_projModelMulBy_add_one_eq_projModelZero_iff hP 1, h1, eq_comm]

/-- **Points killed by `2`.** Let `W` be an elliptic Weierstrass curve over a commutative ring `R`
and `(x, y)` a solution of its affine equation over `R`. The point `[x : y : 1]` of the projective
model with values in `R` is killed by multiplication by `2`, as a morphism `Spec R ⟶ projModel W`,
if and only if `ψ₂(x, y) = 2y + a₁x + a₃ = 0`. -/
theorem projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff {x y : R}
    (h : W.toAffine.Equation x y) :
    W.projModelAffinePoint h ≫ W.projModelMulBy 2 = W.projModelZero ↔ W.ψ₂.evalEval x y = 0 := by
  rw [comp_projModelMulBy_two_eq_projModelZero_iff (projModelAffinePoint_projModelOver h),
    projModelAffinePoint_projModelNeg, projModelAffinePoint_inj, ψ₂, Affine.evalEval_polynomialY,
    Affine.negY]
  exact ⟨fun ⟨_, hy⟩ ↦ by linear_combination -hy, fun hy ↦ ⟨rfl, by linear_combination -hy⟩⟩

/-- When `[x₁ : y₁ : 1]` is killed by `2`, another affine point `[x₂ : y₂ : 1]` agrees with it over
a point `s` of `Spec R` if and only if `x₂ - x₁` lies in the prime ideal `s`. -/
theorem projModelAffinePoint_apply_eq_iff_of_projModelMulBy_two {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hP₁ : W.projModelAffinePoint h₁ ≫ W.projModelMulBy 2 = W.projModelZero) (s : Spec (.of R)) :
    W.projModelAffinePoint h₂ s = W.projModelAffinePoint h₁ s ↔ x₂ - x₁ ∈ s.asIdeal := by
  have hneg := (comp_projModelMulBy_two_eq_projModelZero_iff
    (projModelAffinePoint_projModelOver h₁)).mp hP₁
  have key := W.projModelAffinePoint_apply_eq_or_eq_projModelNeg_iff h₁ h₂ s
  rwa [hneg, or_self] at key

/-- When `[x₁ : y₁ : 1]` is killed by `2`, another affine point `[x₂ : y₂ : 1]` differs from it at
every point of `Spec R` if and only if `x₂ - x₁` is a unit of `R`. -/
theorem forall_projModelAffinePoint_apply_ne_iff_isUnit_sub {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hP₁ : W.projModelAffinePoint h₁ ≫ W.projModelMulBy 2 = W.projModelZero) :
    (∀ s, W.projModelAffinePoint h₂ s ≠ W.projModelAffinePoint h₁ s) ↔ IsUnit (x₂ - x₁) := by
  simp_rw [Ne, projModelAffinePoint_apply_eq_iff_of_projModelMulBy_two h₁ h₂ hP₁]
  refine ⟨fun H ↦ ?_, fun hu s hs ↦ s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hu)⟩
  by_contra hu
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
  exact H ⟨m, hm.isPrime⟩ hmem

end WeierstrassCurve
