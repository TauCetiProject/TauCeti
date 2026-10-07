/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.Algebra.QuadraticDiscriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Trace

/-!
# The Hasse bound

For an elliptic curve `E` over a finite field `𝔽_q`, the number of rational points is within `2√q`
of `q + 1`. In integer form, the Frobenius trace `a_q = q + 1 - #E(𝔽_q)` satisfies `a_q² ≤ 4q`.

## Main results

* `WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card`: `a_q² ≤ 4q`.
* `WeierstrassCurve.hasse_bound`: the same bound, stated for the point count.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.1.1.

## Provenance

The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a` proves the real form `|#E(𝔽_q) - q - 1| ≤ 2√q` as
`HasseWeil.WeilPairing.hasse_bound` in `HasseWeil/HasseBound.lean`, assembled from Weil-pairing
scalings of individual isogenies. Nothing is taken from the source: the statements here are the
integer form, for TauCeti's elliptic curves and their Frobenius trace.
-/

public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic]

private theorem card_mul_sq_sub_frobeniusTrace_mul_add_sq_nonneg (r : ℤ) {s : ℤ}
    (hs : ¬(ringChar F : ℤ) ∣ s) : 0 ≤ Nat.card F * r ^ 2 - W.frobeniusTrace * (r * s) + s ^ 2 :=
  -- `p ∤ s` makes `s` nonzero in an algebraic closure, where this form is the degree of `r π - s`
  (Int.natCast_nonneg _).trans_eq <|
    TauCeti.Isogeny.Hom.degree_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id_eq_frobeniusTrace
      W.toAffine r s <| mt (CharP.intCast_eq_zero_iff (AlgebraicClosure F) (ringChar F) s).mp hs

/-- **The Hasse bound**, in trace form: over a finite field with `q` elements, the Frobenius trace
`a_q` of an elliptic curve satisfies `a_q² ≤ 4q`. `hasse_bound` states the same inequality in terms
of the number of points. -/
theorem frobeniusTrace_sq_le_four_mul_card : W.frobeniusTrace ^ 2 ≤ 4 * Nat.card F := by
  -- Over an algebraic closure, `deg (r π - s) = q r² - a_q r s + s²` whenever the characteristic
  -- `p` does not divide `s`. Degrees are non-negative, so this binary form is non-negative off the
  -- multiples of `p`, which bounds its discriminant `a_q² - 4q` by `0`.
  simpa only [discrim, neg_sq, mul_one, sub_nonpos] using
    Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd (a := Nat.card F) (b := -W.frobeniusTrace)
      (c := 1) (Nat.prime_iff_prime_int.mp (CharP.prime_ringChar F)).not_isUnit
      fun r s _ hs ↦ (W.card_mul_sq_sub_frobeniusTrace_mul_add_sq_nonneg r hs).trans_eq (by ring)

/-- **The Hasse bound** (Silverman V.1.1): an elliptic curve `E` over a field with `q` elements
satisfies `(#E(𝔽_q) - (q + 1))² ≤ 4q`, that is `|#E(𝔽_q) - (q + 1)| ≤ 2√q`, where the count
includes the point at infinity. `frobeniusTrace_sq_le_four_mul_card` is the same bound for the
trace `a_q`. -/
theorem hasse_bound :
    ((Nat.card W.toAffine.Point : ℤ) - ((Nat.card F : ℤ) + 1)) ^ 2 ≤ 4 * (Nat.card F : ℤ) := by
  rw [sub_sq_comm, ← frobeniusTrace_eq_card_point]
  exact W.frobeniusTrace_sq_le_four_mul_card

end WeierstrassCurve

end
