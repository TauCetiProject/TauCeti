/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The affine points of a Weierstrass curve over a finite ring form a finite type

`E(𝔽_q)` is finite. This is needed before the count `#E(𝔽_q)` means anything: `Nat.card` reads
`0` on an infinite type, so a statement like the Hasse bound is only the honest count when
accompanied by finiteness.

## Main results

* `WeierstrassCurve.Affine.finite_point`: `W.Point` is finite whenever the base is.

This is stated over an arbitrary finite commutative ring and an arbitrary affine Weierstrass curve:
neither a field nor `IsElliptic` is needed. It is an `instance`, so `Nat.card`/`Finset` arguments
about `E(𝔽_q)` pick it up without being handed a proof.
-/

public section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [Finite R] (W : Affine R)

/-- **The affine points of a Weierstrass curve over a finite ring form a finite type.** -/
instance finite_point : Finite W.Point :=
  -- transport along Mathlib's decomposition of `Point` as the point at infinity together with the
  -- pairs satisfying `Nonsingular`; `WithZero` carries no `Finite` instance of its own, so it is
  -- taken from the `Option` it unfolds to
  have : Finite (WithZero {xy : R × R // W.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option _))
  .of_equiv _ W.nonsingularPointEquiv.symm

end WeierstrassCurve.Affine
