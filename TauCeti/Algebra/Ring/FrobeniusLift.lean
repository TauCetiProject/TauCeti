/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorization.Defs

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Basic

/-!
# Iterates of lifts of power maps

Let `φ` be a ring endomorphism of a commutative ring `R` that lifts the `q`-th power map modulo
an element `c`, in the sense that `c ∣ φ a - a ^ q` for every `a`. The typical case is a lift of
the Frobenius of `R / p R`, for a prime `p`, with `c = p` and `q = p`. Then the `i`-th iterate of
`φ` lifts the `q ^ i`-th power map modulo `c`. This is the congruence `σⁱ(a) ≡ a ^ (pⁱ)` modulo
`p` used in integrality arguments for Hazewinkel's functional equation.

## Main results

* `TauCeti.dvd_pow_apply_sub_pow_pow`: if `c ∣ φ a - a ^ q` for all `a`, then
  `c ∣ φⁱ a - a ^ q ^ i`.
* `TauCeti.pow_factorization_succ_dvd_pow_sub_pow`: if `p ∣ u - v`, then
  `p ^ (m.factorization p + 1) ∣ u ^ m - v ^ m`, without primality assumptions on `p`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A congruence modulo a natural number `p` gives a congruence between `m`-th powers modulo
`p ^ (m.factorization p + 1)`. This holds for all `p` and `m`, including zero, without assuming
that `p` is prime. -/
theorem pow_factorization_succ_dvd_pow_sub_pow {p : ℕ} {u v : R}
    (h : (p : R) ∣ u - v) (m : ℕ) :
    (p : R) ^ (m.factorization p + 1) ∣ u ^ m - v ^ m := by
  refine (dvd_sub_pow_of_dvd_sub h (m.factorization p)).trans ?_
  conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p, pow_mul, pow_mul]
  exact sub_dvd_pow_sub_pow _ _ _

/-- If a ring endomorphism `φ` lifts the `q`-th power map modulo `c`, that is `c ∣ φ a - a ^ q`
for every `a`, then its `i`-th iterate lifts the `q ^ i`-th power map: `c ∣ φⁱ a - a ^ q ^ i`. -/
theorem dvd_pow_apply_sub_pow_pow {c : R} {q : ℕ} {φ : R →+* R} (hφ : ∀ a, c ∣ φ a - a ^ q)
    (i : ℕ) (a : R) : c ∣ (φ ^ i) a - a ^ q ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, pow_succ, pow_mul]
    -- `φ (φⁱ a) ≡ (φⁱ a) ^ q ≡ (a ^ q ^ i) ^ q`
    have := dvd_add (hφ ((φ ^ i) a)) (ih.trans (sub_dvd_pow_sub_pow _ _ q))
    rwa [sub_add_sub_cancel] at this

end TauCeti
