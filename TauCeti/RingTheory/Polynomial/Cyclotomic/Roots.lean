/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Evaluating cyclotomic polynomials at primitive roots

A primitive root of unity in a domain annihilates a cyclotomic polynomial after mapping its
coefficients along a ring homomorphism.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

/-- A primitive `e`-th root of unity `r` in a domain `R` is a root of the cyclotomic polynomial
`Φ_e` over any ring, mapped to `R` along any ring homomorphism `f`. Mathlib's
`IsPrimitiveRoot.isRoot_cyclotomic` is the case of `Φ_e` taken over `R` itself. -/
theorem eval₂_cyclotomic {e : ℕ} {S R : Type*} [Ring S] [CommRing R] [IsDomain R]
    [NeZero e] (f : S →+* R) {r : R} (hr : IsPrimitiveRoot r e) :
    (cyclotomic e S).eval₂ f r = 0 := by
  rw [← eval_map, map_cyclotomic]
  exact hr.isRoot_cyclotomic (NeZero.pos e)

end IsPrimitiveRoot
