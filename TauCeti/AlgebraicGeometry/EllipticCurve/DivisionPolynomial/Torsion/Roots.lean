/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
-- Proof-only: a vanishing `ψₙ` annihilates the point, and conversely.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
-- Proof-only: over an algebraically closed field every `x` is the abscissa of a point.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed

/-!
# The roots of `ΨSqₙ` are the abscissae of the nonzero `n`-torsion

`ΨSqₙ` is the square of the `n`-division polynomial, pushed down to a polynomial in `x` alone. Its
roots are exactly the `x`-coordinates of the affine points killed by `n`: one direction holds over
any field, the other needs the base field algebraically closed, so that the `y` completing a root
to a point exists.

This is the dictionary the `n`-torsion is counted through — the kernel of `[n]` maps to the roots
of `ΨSqₙ` two-to-one away from the `2`-torsion, which is what matches `#ker [n] = n ²` against
`deg preΨₙ`.

## Main results

* `WeierstrassCurve.eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero`: over an algebraically closed
  field, the roots of `ΨSqₙ` are exactly the abscissae of the `n`-torsion points. The pointwise
  form, for a supplied `y`, is `eval_ΨSq_eq_zero_iff_zsmul_eq_zero` in
  `DivisionPolynomial/ZSMul.lean`; only the existence of `y` needs the closure assumption.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **Over an algebraically closed field the roots of `ΨSqₙ` are exactly the abscissae of the
`n`-torsion points.** Solving the Weierstrass equation for `y` gives a point over a root, and
`ΨSqₙ(x) = 0` makes `ψₙ` vanish there, which annihilates it; the converse needs no closure, since
the `y` is supplied. -/
theorem eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero [IsAlgClosed F] [W.IsElliptic] {n : ℤ} {x : F} :
    (W.ΨSq n).eval x = 0 ↔ ∃ y, ∃ hns : W.toAffine.Nonsingular x y,
      n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, hns, h⟩ ↦ (eval_ΨSq_eq_zero_iff_zsmul_eq_zero W hns n).mpr h⟩
  obtain ⟨y, hy⟩ := W.toAffine.exists_point_on_curve x
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  exact ⟨y, hns, (eval_ΨSq_eq_zero_iff_zsmul_eq_zero W hns n).mp hx⟩

end WeierstrassCurve

end
