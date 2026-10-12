/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.EllipticCurve

/-!
# Elementary properties of the naïve height on an elliptic curve

Mathlib defines the naïve height `Point.naiveHeight P = logHeight P.xRep` of an affine point of a
Weierstrass curve, proves the approximate parallelogram law for it and deduces Northcott
finiteness. This file adds the three pointwise facts that the canonical height needs and that
Mathlib does not state: non-negativity, the value at the point at infinity, and invariance under
negation.

## Main results

* `WeierstrassCurve.Affine.Point.naiveHeight_nonneg` : the naïve height is non-negative.
* `WeierstrassCurve.Affine.Point.naiveHeight_zero` : the point at infinity has height zero.
* `WeierstrassCurve.Affine.Point.naiveHeight_neg` : negation preserves the naïve height.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

open Height

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [AdmissibleAbsValues F] {W : Affine F}

/-- **The naïve height is non-negative**, being a logarithmic height. -/
lemma Point.naiveHeight_nonneg (P : W.Point) : 0 ≤ P.naiveHeight := by
  rw [naiveHeight_eq_logHeight]
  positivity

/-- The point at infinity has height zero: its representative is `![1, 0]`. -/
@[simp]
lemma Point.naiveHeight_zero : (0 : W.Point).naiveHeight = 0 := by
  simp [naiveHeight_eq_logHeight, Point.xRep_zero]

/-- Negation preserves the naïve height, since `P` and `-P` share an `x`-coordinate. -/
@[simp]
lemma Point.naiveHeight_neg (P : W.Point) : (-P).naiveHeight = P.naiveHeight := by
  simp [naiveHeight_eq_logHeight, Point.xRep_neg]

end WeierstrassCurve.Affine

end
