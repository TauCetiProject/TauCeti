/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum

/-!
# Iterates of lifts of power maps

Let `φ` be a ring endomorphism of a commutative ring `R` that lifts the `q`-th power map modulo
an element `c`, in the sense that `c ∣ φ a - a ^ q` for every `a`. The typical case is a lift of
the Frobenius of `R / p R`, for a prime `p`, with `c = p` and `q = p`. Then the `i`-th iterate of
`φ` lifts the `q ^ i`-th power map modulo `c`. This is the congruence `σⁱ(a) ≡ a ^ (pⁱ)` modulo
`p` used in integrality arguments for Hazewinkel's functional equation.

Similarly, if `φ` sends a single element `q` exactly to `q ^ p`, as the Frobenius lift of the
`q`-de Rham prism does, then `φˢ` sends `q` to `q ^ p ^ s`.

## Main results

* `TauCeti.pow_apply_of_apply_eq_pow`: if `φ q = q ^ p` exactly, then `φˢ q = q ^ p ^ s`.
* `TauCeti.dvd_pow_apply_sub_pow_pow`: if `c ∣ φ a - a ^ q` for all `a`, then
  `c ∣ φⁱ a - a ^ q ^ i`.
-/

public section

namespace TauCeti

/-- If a ring endomorphism `φ` satisfies `φ(q) = q ^ p`, its iterates satisfy
`φ^s(q) = q ^ (p ^ s)`. -/
theorem pow_apply_of_apply_eq_pow {R : Type*} [Semiring R] {φ : R →+* R} {q : R} {p : ℕ}
    (hq : φ q = q ^ p) (s : ℕ) : (φ ^ s) q = q ^ p ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [RingHom.coe_pow, Function.iterate_succ_apply', ← RingHom.coe_pow, ih, map_pow, hq,
      ← pow_mul, ← pow_succ']

variable {R : Type*} [CommRing R]

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
