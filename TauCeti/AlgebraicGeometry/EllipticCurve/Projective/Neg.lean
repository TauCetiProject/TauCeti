/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Negation of solutions of the projective Weierstrass equation

For a Weierstrass curve `W'` over a commutative ring, Mathlib's negation
`WeierstrassCurve.Projective.neg` sends a point representative `[P₀ : P₁ : P₂]` to
`[P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]`. Mathlib shows that it preserves nonsingularity over a field; this
file shows that over any commutative ring it is the action on homogeneous coordinates of the change
of variables `negVariableChange W'`, which fixes `W'`, and hence that it preserves the projective
Weierstrass equation.

## Main results

* `WeierstrassCurve.toMatrix_negVariableChange_mulVec`: the matrix of `negVariableChange W` acts on
  point representatives by `WeierstrassCurve.Projective.neg`.
* `WeierstrassCurve.Projective.equation_neg`: the negation of a point representative is a solution
  of the projective Weierstrass equation exactly when the representative is.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

open Matrix in
/-- The change of variables `negVariableChange W` acts on homogeneous coordinates by Mathlib's
negation: `W.negVariableChange.toMatrix *ᵥ P = [P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]`. -/
theorem toMatrix_negVariableChange_mulVec (W : WeierstrassCurve R) (P : Fin 3 → R) :
    W.negVariableChange.toMatrix *ᵥ P = W.toProjective.neg P := by
  ext k
  fin_cases k <;> simp [VariableChange.toMatrix_def, mulVec, dotProduct, Fin.sum_univ_three,
    Projective.neg_X, Projective.neg_Y, Projective.neg_Z, Projective.negY]
  -- the `Y`-coordinate remains: `-a₁P₀ + (-1)³P₁ - a₃P₂ = -P₁ - a₁P₀ - a₃P₂`
  ring

namespace Projective

variable {W' : Projective R}

/-- The negation `W'.neg P = [P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]` of a point representative `P` is a
solution of the projective Weierstrass equation exactly when `P` is: the projective form of
`WeierstrassCurve.Affine.equation_neg`. -/
theorem equation_neg (P : Fin 3 → R) : W'.Equation (W'.neg P) ↔ W'.Equation P := by
  rw [← toMatrix_negVariableChange_mulVec, ← equation_variableChange, negVariableChange_smul_self]

end Projective

end WeierstrassCurve
