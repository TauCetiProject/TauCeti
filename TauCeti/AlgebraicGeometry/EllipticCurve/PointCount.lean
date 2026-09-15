/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The point count of a Weierstrass model

`pointCount` counts the `F`-points of the projective Weierstrass model: the solutions of the
affine equation, singular or not, together with the point at infinity, `[0 : 1 : 0]` being the only
point on `z = 0`. It is `Nat.card` of the solutions plus one, so it is the honest number of points
whenever that solution type is finite. It is the count against which the Frobenius trace
`q + 1 − #W(F)` is taken over a finite field, which is the setting it exists for.

Counting the singular point is the whole content of the convention, and it is what makes the trace
return the classical local invariant at *every* Weierstrass model: `a_q` at an elliptic one, and
`1`, `−1`, `0` at split multiplicative, nonsplit multiplicative and additive reduction. Against the
nonsingular locus instead it would omit the one singular rational point and return `2`, `0`, `1` at
those three, which is no classical invariant. So the definition carries no ellipticity hypothesis:
there is no junk value to avoid.

The `+ 1` is the line at infinity's contribution. `pointCount_eq_card_point` asks exactly for
finiteness of the solution subtype, which a finite base supplies: adjoining the point at infinity
then raises its `Nat.card` by one, which is what makes the comparison with Mathlib's point type go
through.

## Main definitions

* `WeierstrassCurve.pointCount`: the `Nat.card` count of the projective Weierstrass model's
  `F`-points.
* `WeierstrassCurve.frobeniusTrace`: over a finite field, the defect `q + 1 − #W(F)` of that
  count from `q + 1`.

## Main results

* `WeierstrassCurve.pointCount_eq_card_point`: on an elliptic model whose affine solutions form a
  finite type — a finite base being one case of that — it is the cardinality of Mathlib's point
  type.
* `WeierstrassCurve.frobeniusTrace_eq_card_point`: over a finite field, on an elliptic model the
  trace is `q + 1` minus the cardinality of Mathlib's point type, which is the classical `a_q`.

## Provenance

Not ported. The AINTLIB `HasseWeil` project (Chris Birkbeck, Apache 2.0, commit
`513e83879e2f8cbc626eb9e04d660e92be16ccba`) has a `pointCount` of the same name in
`HasseWeil/Frobenius.lean`, but it is `Fintype.card E.Point` on an elliptic curve carrying a
`Fintype` instance as a hypothesis: the nonsingular-locus count, under the restriction where the
two agree. The definition here is the projective one and is taken for an arbitrary Weierstrass
model, so the comparison with the point type becomes a theorem.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.1, V.2.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **The number of `F`-points of the projective Weierstrass model**, the singular point included
when there is one: `Nat.card` of the solutions of the affine equation, singular or not, plus one
for the point at infinity. It is the honest count whenever that solution type is finite. -/
noncomputable def _root_.WeierstrassCurve.pointCount : ℕ :=
  Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1

/-- The defining equation of `pointCount`. -/
@[simp]
-- Needed as a lemma rather than left to unfolding: `pointCount`'s body is not exposed across a
-- module boundary, so `rfl` for this equation fails in a downstream file.
theorem _root_.WeierstrassCurve.pointCount_def :
    W.pointCount = Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1 := (rfl)

/-- **On an elliptic model the projective count is the cardinality of Mathlib's point type.**
An elliptic model has no singular point to include, so the solutions of the equation are exactly
the nonsingular ones, and the point at infinity is the one Mathlib's type adjoins. -/
theorem _root_.WeierstrassCurve.pointCount_eq_card_point
    [Finite {p : F × F // W.toAffine.Equation p.1 p.2}] [W.IsElliptic] :
    W.pointCount = Nat.card W.toAffine.Point := by
  rw [WeierstrassCurve.pointCount_def, Nat.card_congr W.toAffine.pointEquiv]
  -- `WithZero` is the `Option` the cardinality lemma is stated for
  exact Finite.card_option.symm

/-- **The Frobenius trace** `a_q = q + 1 − #W(F)` of a Weierstrass model over a finite field of
`q` elements, measured against `pointCount`.

Taken against that count the formula returns the classical local invariant at *every* Weierstrass
model: `a_q` at an elliptic one, and `1`, `−1`, `0` at split multiplicative, nonsplit
multiplicative and additive reduction. That is why it carries no ellipticity hypothesis. It is
elliptic-specific only in its reading as a *trace*, which rests on the identity
`deg (1 − π_q) = #E(𝔽_q)`. -/
noncomputable def _root_.WeierstrassCurve.frobeniusTrace [Finite F] : ℤ :=
  -- `q` is a number only because the base is finite, so the count is taken through that
  -- finiteness; `frobeniusTrace_def` restates it with `Nat.card`, the form the API is phrased in
  have : Fintype F := Fintype.ofFinite F
  (Fintype.card F : ℤ) + 1 - W.pointCount

/-- The defining equation of `frobeniusTrace`. -/
@[simp]
theorem _root_.WeierstrassCurve.frobeniusTrace_def [Finite F] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - W.pointCount := by
  simp only [WeierstrassCurve.frobeniusTrace, @Nat.card_eq_fintype_card F (Fintype.ofFinite F)]

/-- **Over a finite field, on an elliptic model the trace is measured against Mathlib's point
type**, which is the classical `a_q`. -/
theorem _root_.WeierstrassCurve.frobeniusTrace_eq_card_point [Finite F] [W.IsElliptic] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - Nat.card W.toAffine.Point := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.pointCount_eq_card_point]

end TauCeti

end
