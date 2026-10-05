/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# Nonsingularity of projective points on an elliptic curve

Over a field, every nonzero point representative `[X : Y : Z]` satisfying the projective
Weierstrass equation of an elliptic curve is nonsingular. This is the projective counterpart of
Mathlib's `WeierstrassCurve.Affine.equation_iff_nonsingular`. The hypothesis that the
representative is nonzero is necessary: `(0, 0, 0)` satisfies the homogeneous equation but all
three partial derivatives vanish there.

## Main results

* `WeierstrassCurve.Projective.equation_iff_nonsingular_of_ne_zero`: on an elliptic curve over a
  field, a nonzero point representative satisfies the equation if and only if it is nonsingular.
-/

public section

namespace WeierstrassCurve.Projective

variable {F : Type*} [Field F] {W : Projective F}

/-- On an elliptic curve over a field, a nonzero point representative satisfies the projective
Weierstrass equation if and only if it is nonsingular. If `Z ≠ 0`, this is the affine statement;
if `Z = 0`, the equation forces `X = 0`, and then `Y ≠ 0` makes `W_Z = Y²` nonzero. -/
theorem equation_iff_nonsingular_of_ne_zero [W.IsElliptic] {P : Fin 3 → F} (hP : P ≠ 0) :
    W.Equation P ↔ W.Nonsingular P := by
  refine ⟨fun h ↦ ?_, And.left⟩
  by_cases hz : P 2 = 0
  · have hx : P 0 = 0 := X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy ↦ hP (funext fun k ↦ by fin_cases k <;> assumption)
    rw [nonsingular_of_Z_eq_zero hz]
    exact ⟨h, Or.inr (by simpa [hx] using hy)⟩
  · rw [nonsingular_of_Z_ne_zero hz, ← Affine.equation_iff_nonsingular,
      ← equation_of_Z_ne_zero hz]
    exact h

end WeierstrassCurve.Projective
