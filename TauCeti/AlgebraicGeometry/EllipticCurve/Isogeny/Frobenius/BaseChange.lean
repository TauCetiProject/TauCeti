/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Basic

/-!
# The Frobenius over an extension of the finite base

Let `W` be a Weierstrass curve over a finite field `F` with `q` elements, and `K` an extension of
`F`. The `q`-power Frobenius isogeny of `W` base-changes along `F → K` to an isogeny `π` of `W⁄K`,
`TauCeti.Isogeny.baseChangeFrobenius`. Its pullback raises the functions defined over `F`, the
generic coordinates in particular, to the `q`-th power. Over `K` itself the `q`-power map is not
the identity, and it is this base change that acts on the points of `W` over `K`.

## Main definitions

* `TauCeti.Isogeny.baseChangeFrobenius`: the `q`-power Frobenius of `W`, as an isogeny of `W⁄K`.

## Main results

* `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_map`: its pullback raises the functions
  defined over `F` to the `q`-th power.
* `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_genericX` and
  `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_genericY`: in particular the generic
  coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K] (W : WeierstrassCurve.Affine F)

variable (K) in
/-- **The Frobenius of `W` over an extension `K` of its finite base**: the base change of the
`q`-power Frobenius isogeny, read as an isogeny of `W⁄K`. -/
noncomputable def baseChangeFrobenius : Isogeny (W⁄K).toAffine (W⁄K).toAffine :=
  (frobeniusIsogeny W).map (algebraMap F K)

/-- **The pullback of `baseChangeFrobenius` raises the functions defined over `F` to the `q`-th
power.** -/
-- Not `@[simp]`: `FunctionField.map W (algebraMap F K) z` lives in the function field of
-- `W.map (algebraMap F K)`, which is `W⁄K` only after unfolding `WeierstrassCurve.baseChange`, so
-- the rewritten goal `a ^ q = a ^ q` compares powers in two syntactically different fields and
-- `simp` cannot close the lemma's own statement. The generic-coordinate forms below are simp.
theorem fieldPullback_baseChangeFrobenius_map (z : W.FunctionField) :
    (baseChangeFrobenius K W).fieldPullback (FunctionField.map W (algebraMap F K) z) =
      FunctionField.map W (algebraMap F K) z ^ Nat.card F := by
  refine (map_fieldPullback_map (frobeniusIsogeny W) (algebraMap F K) z).trans ?_
  rw [fieldPullback_frobeniusIsogeny_apply, map_pow]

/-- **The pullback of `baseChangeFrobenius` raises the generic `x`-coordinate to the `q`-th
power.** -/
@[simp]
theorem fieldPullback_baseChangeFrobenius_genericX :
    (baseChangeFrobenius K W).fieldPullback (genericX (W⁄K).toAffine) =
      genericX (W⁄K).toAffine ^ Nat.card F :=
  FunctionField.map_genericX W (algebraMap F K) ▸ fieldPullback_baseChangeFrobenius_map W _

/-- **The pullback of `baseChangeFrobenius` raises the generic `y`-coordinate to the `q`-th
power.** -/
@[simp]
theorem fieldPullback_baseChangeFrobenius_genericY :
    (baseChangeFrobenius K W).fieldPullback (genericY (W⁄K).toAffine) =
      genericY (W⁄K).toAffine ^ Nat.card F :=
  FunctionField.map_genericY W (algebraMap F K) ▸ fieldPullback_baseChangeFrobenius_map W _

end TauCeti.Isogeny

end
