/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The degree of the radical extensions `y ^ n = c t ^ a (t - 1) ^ b` of `k(t)`

Let `F = k(t)(y)` with `y ^ n = c t ^ a (t - 1) ^ b` for a nonzero `c ∈ k` and `a, b ∈ ℤ`. The
orders of the radicand at the places `0`, `1` and `∞` of `k(t)` are `a`, `b` and `-(a + b)`
(`TauCeti.Place.ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow` and its specializations). If `n` is
coprime to one of them, then `X ^ n - c t ^ a (t - 1) ^ b` is irreducible over `k(t)` and
`[F : k(t)] = n` (Stichtenoth, Corollary 3.7.4; this is
`Valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one`).

## Main results

* `TauCeti.finrank_eq_of_pow_eq_X_zpow_mul_X_sub_one_zpow`: the degree of
  `y ^ n = c t ^ a (t - 1) ^ b` over `k(t)` is `n`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.7.4.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra (RatFunc k) F]

/-- **The degree of `y ^ n = c t ^ a (t - 1) ^ b`**: if `F = k(t)(y)` with
`y ^ n = c t ^ a (t - 1) ^ b` for a nonzero `c ∈ k`, and `n ≠ 0` is coprime to one of `a`, `b` and
`a + b`, then `[F : k(t)] = n`. -/
theorem finrank_eq_of_pow_eq_X_zpow_mul_X_sub_one_zpow {y : F} {n : ℕ} {c : k} {a b : ℤ}
    (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ n = algebraMap (RatFunc k) F
      (algebraMap k (RatFunc k) c * RatFunc.X ^ a * (RatFunc.X - 1) ^ b))
    (hn : n ≠ 0) (hc : c ≠ 0) (hcop : Int.gcd n a = 1 ∨ Int.gcd n b = 1 ∨ Int.gcd n (a + b) = 1) :
    Module.finrank (RatFunc k) F = n := by
  obtain ⟨P, hP⟩ := Place.exists_gcd_ord_algebraMap_mul_X_zpow_mul_X_sub_one_zpow_eq_one hc hcop
  exact P.valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one hgen hy hn
    (by rwa [Place.ord_valuation])

end TauCeti
