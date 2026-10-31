/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Basic.Real.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
-- Proof-only: the square root of `Ψ₂Sq(x)` gives the ordinate of a point.
import Mathlib.Analysis.Real.Sqrt
-- Proof-only: `ψ₂(x, y)² = Ψ₂Sq(x)` characterises the points of the curve, and the points of order
-- two are the zeros of `ψ₂`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion

/-!
# Real points of a Weierstrass curve

Over `ℝ`, completing the square writes the Weierstrass equation as
`(2y + a₁x + a₃)² = Ψ₂Sq(x)`, where `Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆` is Mathlib's
`WeierstrassCurve.Ψ₂Sq`. So the curve has a real point with abscissa `x` exactly when
`Ψ₂Sq(x) ≥ 0`. The two points `(x, y)` and `-(x, y)` over such an `x` coincide exactly when
`Ψ₂Sq(x) = 0`, that is, at the points of order two. These are the facts that let the real period
integral `∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)` be read as an integral over the real points that are not
`2`-torsion.

## Main results

* `WeierstrassCurve.Affine.exists_equation_iff_nonneg_eval_Ψ₂Sq`: there is a real point with
  abscissa `x` exactly when `Ψ₂Sq(x) ≥ 0`.
* `WeierstrassCurve.Affine.Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq`: a point is not
  `2`-torsion exactly when it is affine and `Ψ₂Sq` is positive at its abscissa, over any ordered
  field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {W : WeierstrassCurve.Affine ℝ}

/-- **A real Weierstrass curve has a point with abscissa `x` exactly when `Ψ₂Sq(x) ≥ 0`.** One
such point has `2y + a₁x + a₃ = √Ψ₂Sq(x)`. -/
theorem exists_equation_iff_nonneg_eval_Ψ₂Sq {x : ℝ} :
    (∃ y, W.Equation x y) ↔ 0 ≤ W.Ψ₂Sq.eval x := by
  refine ⟨fun ⟨y, h⟩ ↦ W.evalEval_ψ₂_sq h ▸ sq_nonneg _, fun hx ↦
    ⟨(√(W.Ψ₂Sq.eval x) - W.a₁ * x - W.a₃) / 2, (W.evalEval_ψ₂_sq_eq_iff two_ne_zero).mp ?_⟩⟩
  rw [WeierstrassCurve.ψ₂, evalEval_polynomialY]
  convert Real.sq_sqrt hx using 2
  ring

/-- **A point is not `2`-torsion exactly when it is affine and `Ψ₂Sq` is positive at its
abscissa**, over an ordered field such as `ℝ`. At an affine point `(x, y)`,
`Ψ₂Sq(x) = (2y + a₁x + a₃)²`, which vanishes exactly at the points of order two. -/
theorem Point.neg_ne_self_iff_ne_zero_and_pos_eval_Ψ₂Sq {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {W : WeierstrassCurve.Affine F} {P : W.Point} :
    -P ≠ P ↔ P ≠ 0 ∧ 0 < W.Ψ₂Sq.eval P.xCoord := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  rw [ne_eq, neg_eq_iff_add_eq_zero, Point.some_add_self_eq_zero_iff h, Point.xCoord_some,
    ← W.evalEval_ψ₂_sq h.1, WeierstrassCurve.ψ₂, sq_pos_iff]
  exact ⟨fun h0 ↦ ⟨Point.some_ne_zero h, h0⟩, And.right⟩

end WeierstrassCurve.Affine
