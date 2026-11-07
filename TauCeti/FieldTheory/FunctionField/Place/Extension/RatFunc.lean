/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# Orders of polynomials in `x` at a place over a finite place of `k(x)`

Let `F` be a finite extension of the rational function field `k(x)`. At a place `P` of `F` lying
over the finite place `x = a` of `k(x)`, the order of a nonzero polynomial in `x` is the
ramification index of `P` over `k(x)` times the multiplicity of `x - a` in the polynomial.

## Main results

* `TauCeti.Place.ord_algebraMap_eq_of_restrict_eq`: the order of a nonzero polynomial in `x` at a
  place over `x = a`.
* `TauCeti.Place.ord_algebraMap_pos_of_restrict_eq`: such a polynomial has positive order when it
  is divisible by `x - a`.
-/

public section

open Polynomial

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra (RatFunc k) F] [Algebra k F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- At a place over `x = a`, a nonzero polynomial in `x` has order `e` times its multiplicity at
`a`, where `e` is the ramification index over `k(x)`. -/
theorem ord_algebraMap_eq_of_restrict_eq (a : k) {P : Place k F}
    (hP : P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a)) {p : k[X]}
    (hp : p ≠ 0) :
    P.ord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) =
      ramificationIdx (RatFunc k) P * multiplicity (X - C a) p := by
  rw [ord_algebraMap_restrict k (RatFunc k) P, hP, ord_adicOfIrreducible_algebraMap _ hp]

/-- A nonzero polynomial in `x` divisible by `x - a` has positive order at a place over
`x = a`. -/
theorem ord_algebraMap_pos_of_restrict_eq (a : k) {P : Place k F}
    (hP : P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a)) {p : k[X]}
    (hp : p ≠ 0) (hdvd : X - C a ∣ p) :
    0 < P.ord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) := by
  rw [ord_algebraMap_eq_of_restrict_eq a hP hp]
  exact mul_pos (by exact_mod_cast ramificationIdx_pos (RatFunc k) P)
    (by exact_mod_cast (multiplicity_pos_of_dvd hdvd
      (.of_not_isUnit (irreducible_X_sub_C a).not_isUnit hp)))

end Place

end TauCeti
