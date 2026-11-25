/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Character
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization

/-!
# Curves with nonintegral `j`-invariant are twists of Tate curves

Let `K` be a complete nonarchimedean field of characteristic other than `2`, and `E/K` an elliptic
curve. If `q ∈ Kˣ` with `|q| < 1` is a Tate parameter for `j(E)`, that is `j(E_q) = j(E)`, then
`E` is the quadratic twist of the Tate curve `E_q` by exactly one continuous character
`η : Gal(Kᵃˡᵍ/K) → ℤˣ`. Such a `q` exists, and is unique, exactly when `|j(E)| > 1`
(`TauCeti.existsUnique_tateCurveAt_j`). Since `|j(E_q)| = |q|⁻¹ > 1` and `|1728| ≤ 1`, the
`j`-invariant of `E_q` is neither `0` nor `1728` (`TauCeti.tateCurveAt_j_ne_zero`,
`TauCeti.tateCurveAt_j_ne_1728`), so this is the general classification of twists by characters
(`WeierstrassCurve.existsUnique_isQuadraticTwistBy`) applied to `E_q`.

By `WeierstrassCurve.isQuadraticTwistBy_one_iff`, the character `η` is trivial exactly when `E` is
isomorphic over `K` to `E_q`.

## Main results

* `TauCeti.existsUnique_isQuadraticTwistBy_tateCurveAt`: a curve with the `j`-invariant of `E_q`
  is the quadratic twist of `E_q` by a unique continuous character.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.5.
* B. Mazur and K. Rubin, *Selmer companion curves*, Trans. Amer. Math. Soc. 367 (2015), §2.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **A curve with the `j`-invariant of a Tate curve is a quadratic twist of it by a unique
character.** Over a complete nonarchimedean field of characteristic other than `2`, if
`j(E_q) = j(E)` then `E` is the quadratic twist of the Tate curve `E_q` by exactly one continuous
character of the absolute Galois group. -/
theorem existsUnique_isQuadraticTwistBy_tateCurveAt (h2 : (2 : K) ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (hj : (tateCurveAt q hq).j = E.j) :
    ∃! η : Gal(AlgebraicClosure K/K) →ₜ* ℤˣ, (tateCurveAt q hq).IsQuadraticTwistBy E η :=
  (tateCurveAt q hq).existsUnique_isQuadraticTwistBy h2 (tateCurveAt_j_ne_zero q hq)
    (tateCurveAt_j_ne_1728 q hq) E hj.symm

end TauCeti
