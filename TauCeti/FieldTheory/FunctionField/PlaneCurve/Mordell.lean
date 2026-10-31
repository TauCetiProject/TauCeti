/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Radical.Genus
public import TauCeti.FieldTheory.RatFunc.Transcendental
-- Proof-only: the place at infinity of `k(y)` and its orders.
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
-- Proof-only: separability of a radical extension.
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The curve `y ^ 2 = x ^ 3 + a`

Let `k` be a field, `a ∈ k`, and `F = k(x, y)` with `y` transcendental over `k` and

`y ^ 2 = x ^ 3 + a`.

Then `F / k(y)` has degree three. If `3` is invertible in `k`, then `y` is a separating element,
`F / k(y)` being separable, and `k` is the exact constant field of `F`. If moreover `Y ^ 2 - a` is
squarefree, then `F / k` has genus one. These follow from the radical extension
`x ^ 3 = y ^ 2 - a` of `k(y)`, which is tame because `3` is invertible in `k`, with the
superelliptic genus formula `TauCeti.two_mul_genus_eq_of_pow_eq_of_squarefree`: the zeros of
`Y ^ 2 - a`, of total degree two, and the place at infinity are totally ramified, so
`2g - 2 = 3 (-2) + 2 · 2 + 2 · 1 = 0`.

## Main results

* `TauCeti.finrank_adjoin_eq_three_of_sq_eq_pow_three_add` and
  `TauCeti.isSeparable_adjoin_of_sq_eq_pow_three_add`: `F / k(y)` is separable of degree three.
* `TauCeti.isIntegrallyClosedIn_of_sq_eq_pow_three_add`: `k` is the exact constant field of `F`.
* `TauCeti.genus_eq_one_of_sq_eq_pow_three_add`: `F / k` has genus one.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6 and Proposition 3.7.3.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {a : k} {x y : F}

/-- Over `k(y)`, the equation reads `x ^ 3 = y ^ 2 - a`. -/
private theorem pow_three_eq_algebraMap (hy : Transcendental k y)
    (heq : y ^ 2 = x ^ 3 + algebraMap k F a) :
    let := ratFuncAlgebraOfTranscendental hy
    x ^ 3 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (X ^ 2 - C a)) := by
  intro
  have := isScalarTower_ratFuncAlgebraOfTranscendental hy
  rw [map_sub, map_sub, map_pow, map_pow, RatFunc.algebraMap_X,
    algebraMap_ratFuncAlgebraOfTranscendental_X hy, RatFunc.algebraMap_C,
    ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply, heq, add_sub_cancel_right]

/-- At the place at infinity of `k(y)`, `Y ^ 2 - a` has order `-2`, prime to `3`. -/
private theorem gcd_ord_infty :
    Int.gcd (3 : ℕ) ((Place.infty k).ord (algebraMap k[X] (RatFunc k) (X ^ 2 - C a))) = 1 := by
  rw [Place.ord_infty, RatFunc.intDegree_polynomial, natDegree_X_pow_sub_C, Int.gcd_neg]
  rfl

variable (h3 : (3 : k) ≠ 0) (hy : Transcendental k y) (hgen : k⟮x, y⟯ = ⊤)
  (heq : y ^ 2 = x ^ 3 + algebraMap k F a)
include hy hgen heq

/-- **`y ^ 2 = x ^ 3 + a` has degree three over `k(y)`**, in every characteristic. -/
theorem finrank_adjoin_eq_three_of_sq_eq_pow_three_add : Module.finrank k⟮y⟯ F = 3 := by
  let := ratFuncAlgebraOfTranscendental hy
  have := isScalarTower_ratFuncAlgebraOfTranscendental hy
  rw [← algebraMap_ratFuncAlgebraOfTranscendental_X hy, finrank_adjoin_algebraMap_X]
  refine (Place.infty k).valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one
    (adjoin_eq_top_ratFunc_of_adjoin_pair_eq_top hy hgen) (pow_three_eq_algebraMap hy heq)
    three_ne_zero ?_
  rw [Valuation.ord_def, ← Place.ord_def]
  exact gcd_ord_infty

include h3

/-- **`y` is a separating element of `y ^ 2 = x ^ 3 + a`** when `3` is invertible in `k`:
`F / k(y)` is separable. -/
theorem isSeparable_adjoin_of_sq_eq_pow_three_add : Algebra.IsSeparable k⟮y⟯ F := by
  let := ratFuncAlgebraOfTranscendental hy
  have := isScalarTower_ratFuncAlgebraOfTranscendental hy
  rw [← algebraMap_ratFuncAlgebraOfTranscendental_X hy, isSeparable_adjoin_algebraMap_X_iff]
  exact isSeparable_of_pow_eq_of_adjoin_eq_top (by rwa [Nat.cast_ofNat, ← map_ofNat
      (algebraMap k (RatFunc k)), ne_eq, map_eq_zero])
    (RatFunc.algebraMap_ne_zero (X_pow_sub_C_ne_zero two_pos a)) (pow_three_eq_algebraMap hy heq)
    (adjoin_eq_top_ratFunc_of_adjoin_pair_eq_top hy hgen)

/-- **`y ^ 2 = x ^ 3 + a` has exact constants** when `3` is invertible in `k`: `k` is
algebraically closed in `F`. -/
theorem isIntegrallyClosedIn_of_sq_eq_pow_three_add : IsIntegrallyClosedIn k F := by
  let := ratFuncAlgebraOfTranscendental hy
  have := isScalarTower_ratFuncAlgebraOfTranscendental hy
  exact isIntegrallyClosedIn_of_pow_eq_of_gcd_ord_eq_one (IsFunctionField.ratFunc k)
    inferInstance (adjoin_eq_top_ratFunc_of_adjoin_pair_eq_top hy hgen)
    (pow_three_eq_algebraMap hy heq) (by rwa [Nat.cast_ofNat])
    (RatFunc.algebraMap_ne_zero (X_pow_sub_C_ne_zero two_pos a)) (Place.infty k) gcd_ord_infty

/-- **`y ^ 2 = x ^ 3 + a` has genus one** when `3` is invertible in `k` and `Y ^ 2 - a` is
squarefree. -/
theorem genus_eq_one_of_sq_eq_pow_three_add (ha : Squarefree (X ^ 2 - C a)) :
    genus k F = 1 := by
  let := ratFuncAlgebraOfTranscendental hy
  have := isScalarTower_ratFuncAlgebraOfTranscendental hy
  have hg := two_mul_genus_eq_of_pow_eq_of_squarefree
    (adjoin_eq_top_ratFunc_of_adjoin_pair_eq_top hy hgen) (pow_three_eq_algebraMap hy heq)
    (by rwa [Nat.cast_ofNat]) ha (by rw [natDegree_X_pow_sub_C]; exact two_pos)
  rw [natDegree_X_pow_sub_C] at hg
  norm_num at hg
  omega

end TauCeti
