/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Degree

/-!
# The dual of `1 − π_q`

Over a finite field `𝔽_q` the kernel of `1 − π_q` is the set of all rational points, and its
degree is their number `#E(𝔽_q)`. So `1 − π_q` satisfies the hypothesis `#ker φ = deg φ` of
`Isogeny/Dual/Basic.lean`, and `[#E(𝔽_q)]` factors through it. The factor is the dual
`(1 − π_q)^`, of degree `#E(𝔽_q)`. The classical identities `(1 − π_q)^ = 1 − π̂_q` and
`π_q + π̂_q = [a_q]` are not proved here.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_oneSubFrobeniusIsogeny_eq_mulByIntIsogenyOfNeZero`: there
  is a unique `χ` with `χ ∘ (1 − π_q) = [#E(𝔽_q)]`.
* `TauCeti.Isogeny.degree_eq_pointCount_of_comp_oneSubFrobeniusIsogeny_eq`: any such `χ` has
  degree `#E(𝔽_q)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 and V.1.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **`[#E(𝔽_q)]` factors through `1 − π_q`**, by a unique isogeny: the dual of `1 − π_q`. -/
theorem existsUnique_comp_oneSubFrobeniusIsogeny_eq_mulByIntIsogenyOfNeZero
    {hn : (W.pointCount : ℤ) ≠ 0} :
    ∃! χ : Isogeny W W, χ.comp (oneSubFrobeniusIsogeny W) = mulByIntIsogenyOfNeZero W hn := by
  classical
  have h := existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree
    (card_ker_oneSubFrobeniusIsogeny_eq_degree W)
  simp_rw [degree_oneSubFrobeniusIsogeny_eq_pointCount] at h
  exact h

/-- **The dual of `1 − π_q` has degree `#E(𝔽_q)`.** -/
theorem degree_eq_pointCount_of_comp_oneSubFrobeniusIsogeny_eq {χ : Isogeny W W}
    {hn : (W.pointCount : ℤ) ≠ 0}
    (h : χ.comp (oneSubFrobeniusIsogeny W) = mulByIntIsogenyOfNeZero W hn) :
    χ.degree = W.pointCount := by
  rw [← degree_oneSubFrobeniusIsogeny_eq_pointCount W]
  refine degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree (hn := ?_) ?_
  · rwa [degree_oneSubFrobeniusIsogeny_eq_pointCount]
  · simp_rw [degree_oneSubFrobeniusIsogeny_eq_pointCount]
    exact h

end TauCeti.Isogeny

end
