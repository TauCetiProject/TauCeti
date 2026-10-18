/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Algebra.Polynomial.Degree.Operations

/-!
# Binary homogenization of a product of linear factors

Mathlib's `Polynomial.homogenize p n` is the binary form `Y ^ n p(X / Y)` of degree `n`, with
`X` the variable `0` and `Y` the variable `1`. This file computes it on a product of linear
factors: the homogenization of `∏ (X - a)` is `∏ (X - a Y)`. Consequently, a polynomial with as
many roots as its degree, `p = c ∏ (X - a)`, has degree-`(natDegree p)` homogenization
`F(x, y) = c ∏ (x - a y)` at *every* point `(x, y)`, including the points with `y = 0`.

This factorisation is the starting point of Liouville-type lower bounds for binary forms at
integer points.

## Main results

* `Polynomial.homogenize_multiset_prod_X_sub_C`: `homogenize (∏ (X - a)) (card s) = ∏ (X - a Y)`.
* `Polynomial.eval_homogenize_natDegree_of_card_roots`: if `p` has `natDegree p` roots, then
  `F(x) = leadingCoeff p * ∏_{a ∈ roots p} (x 0 - a x 1)`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The homogenization of `∏_{a ∈ s} (X - a)` in degree `card s` is the product of the linear
binary forms `X₀ - a X₁`. -/
theorem homogenize_multiset_prod_X_sub_C (s : Multiset R) :
    (s.map fun a ↦ X - C a).prod.homogenize (Multiset.card s) =
      (s.map fun a ↦ MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      homogenize_mul _ _ (natDegree_X_sub_C_le a) (natDegree_multiset_prod_X_sub_C_le s), ih,
      Multiset.map_cons, Multiset.prod_cons]
    congr 1
    rw [homogenize_sub, homogenize_X one_ne_zero, homogenize_C]
    simp

/-- If `p` has as many roots as its degree, its homogenization `F` of degree `natDegree p`
factors at every point as `F(x) = leadingCoeff p * ∏_{a ∈ roots p} (x 0 - a x 1)`. -/
theorem eval_homogenize_natDegree_of_card_roots [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) (x : Fin 2 → R) :
    MvPolynomial.eval x (p.homogenize p.natDegree) =
      p.leadingCoeff * (p.roots.map fun a ↦ x 0 - a * x 1).prod := by
  have hp := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  calc MvPolynomial.eval x (p.homogenize p.natDegree)
      = MvPolynomial.eval x ((C p.leadingCoeff * (p.roots.map fun a ↦ X - C a).prod).homogenize
          (Multiset.card p.roots)) := by rw [hp, hroots]
    _ = _ := by
      rw [homogenize_C_mul, homogenize_multiset_prod_X_sub_C]
      simp [map_multiset_prod, Multiset.map_map]

end Polynomial
