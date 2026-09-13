/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
-- Proof-only: `ΨSqₙ` is a nonzero polynomial when the curve is nonsingular and `n ≠ 0`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
-- Proof-only: the coordinate identity turning a vanishing `ψₙ` into a vanishing `ΨSqₙ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval
-- Proof-only: a torsion point is a root of `ψₙ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul

/-!
# A torsion point's `x`-coordinate is integral over the base field

`ΨSqₙ` is a nonzero polynomial over the base field whenever `n ≠ 0` and the curve is nonsingular,
and a torsion point is a root of it. So the `x`-coordinate of an affine point killed by a nonzero
`n` is integral over the base, with no hypothesis on the extension.

Over an algebraically closed base that integrality becomes rationality; that is
`Torsion/AlgClosed.lean`, which is the only place algebraic closedness is used.

## Main results

* `WeierstrassCurve.isIntegral_x_of_zsmul_eq_zero`: the `x`-coordinate of an affine point killed
  by a nonzero `n` is integral over the base field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
  {Ω : Type*} [Field Ω] [Algebra F Ω]

/-- **The `x`-coordinate of a point killed by a nonzero `n` is integral over the base field**: it
is a root of `ΨSqₙ`, which is a nonzero polynomial there. The nonvanishing hypothesis is on `n`,
not on the point. -/
theorem isIntegral_x_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    IsIntegral F x := by
  have hψ : ((W.baseChange Ω).ψ n).evalEval x y = 0 :=
    evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange Ω) hns n htors
  have hΨSq : ((W.baseChange Ω).ΨSq n).eval x = 0 := by
    rw [← evalEval_Ψ_sq_eq_eval_ΨSq (W.baseChange Ω) hns.left n,
      ← evalEval_ψ_eq_evalEval_Ψ (W.baseChange Ω) hns.left n, hψ, zero_pow two_ne_zero]
  refine IsAlgebraic.isIntegral
    ⟨W.ΨSq n, W.ΨSq_ne_zero_of_Δ_ne_zero W.isUnit_Δ.ne_zero hn, ?_⟩
  rwa [baseChange, map_ΨSq, eval_map, ← aeval_def] at hΨSq

end WeierstrassCurve

end
