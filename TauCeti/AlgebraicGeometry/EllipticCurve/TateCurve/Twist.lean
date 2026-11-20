/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Character
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# The twisting character of a curve with Tate `j`-invariant

Let `K` be a complete nonarchimedean normed field with `2 ≠ 0`, and `q ∈ Kˣ` with `|q| < 1`. The
Tate curve `E_q` has `|j(E_q)| = 1 / |q| > 1` (`TauCeti.norm_tateCurveAt_j`), while `0` and `1728`
have norm at most one, so `j(E_q) ∉ {0, 1728}`. Every elliptic curve `E` over `K` with
`j(E) = j(E_q)` is therefore the quadratic twist of `E_q` by a unique continuous character
`η : Gal(Kᵃˡᵍ/K) → {±1}`: this is the presentation `E ≅ E_q ⊗ η` of a curve with nonintegral
`j`-invariant. Every invariant of norm above one is `j(E_q)` for exactly one such `q`
(`TauCeti.existsUnique_tateCurveAt_j`).

## Main results

* `TauCeti.existsUnique_isQuadraticTwistBy_tateCurveAt`: a curve with the `j`-invariant of `E_q`
  is the twist of `E_q` by exactly one character.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.5.
* B. Mazur, K. Rubin, *Selmer companion curves*, Trans. Amer. Math. Soc. **367** (2015), §2.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The twisting character of a curve with Tate `j`-invariant.** Over a complete nonarchimedean
field with `2 ≠ 0`, an elliptic curve with the `j`-invariant of the Tate curve `E_q` is the
quadratic twist of `E_q` by exactly one continuous character of `Gal(Kᵃˡᵍ/K)` with values in
`{±1}`. -/
theorem existsUnique_isQuadraticTwistBy_tateCurveAt (h2 : (2 : K) ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (hj : E.j = (tateCurveAt q hq).j) :
    ∃! η, E.IsQuadraticTwistBy (tateCurveAt q hq) η := by
  have hj₁ : 1 < ‖(tateCurveAt q hq).j‖ := by
    rw [norm_tateCurveAt_j]
    exact (one_lt_inv₀ (norm_pos_iff.mpr q.ne_zero)).mpr hq
  refine WeierstrassCurve.existsUnique_isQuadraticTwistBy_of_j_eq h2 ?_ ?_ hj
  · rintro h
    rw [h, norm_zero] at hj₁
    exact zero_le_one.not_gt hj₁
  · rintro h
    rw [h] at hj₁
    exact (IsUltrametricDist.norm_natCast_le_one K 1728).not_gt (by exact_mod_cast hj₁)

end TauCeti
