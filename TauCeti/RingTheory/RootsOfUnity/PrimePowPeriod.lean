/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frobenius-orbit periods of prime-power powers of primitive roots

Let `q > 1` satisfy `9 ∣ q - 1`, let `ξ` be a primitive `(q ^ (3 ^ (e + 1)) - 1)`-th root of unity
in a commutative integral domain `K`, and let `l` be a prime. Then for every `a : ℕ`, the element
`ξ ^ (l ^ a)` has minimal period `3 ^ (e + 1)` under the `q`-th power map `x ↦ x ^ q`, and in
particular its first `3 ^ (e + 1)` iterates `(ξ ^ (l ^ a)) ^ (q ^ i)` (`0 ≤ i < 3 ^ (e + 1)`) are
pairwise distinct.

The key arithmetic fact is a lifting-the-exponent step: writing `q ^ (3 ^ e) = 9 * s + 1`, we have
`q ^ (3 ^ (e + 1)) - 1 = 9 * s * b` with `b = s * (81 * s + 27) + 3`, which is divisible by `3`
but not by `9`, and strictly larger than `3`, so `b` cannot divide any prime power `l ^ a`.

## Main statements

* `TauCeti.minimalPeriod_pow_of_isPrimitiveRoot`: `Function.minimalPeriod (· ^ q) (ξ ^ l ^ a) =
  3 ^ (e + 1)`.
* `TauCeti.injOn_Iio_pow_pow_of_isPrimitiveRoot`: the iterates `i ↦ (ξ ^ l ^ a) ^ (q ^ i)` are
  injective on `Set.Iio (3 ^ (e + 1))`.
* `TauCeti.pow_pow_ne_self_of_lt_three_pow`: for `0 < i < 3 ^ (e + 1)`,
  `(ξ ^ l ^ a) ^ (q ^ i) ≠ ξ ^ l ^ a`.

## Provenance

Adapted from `New.injOn_Iio_pow_card_pow_of_isPrimitiveRoot` in
`grh/src/Lib/LocalGL/Green/LabelCharacters.lean` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
generalized from a finite field cardinality `Nat.card k` and algebraically closed field `K` to an
arbitrary integer `q > 1` with `9 ∣ q - 1` and any commutative integral domain `K`, and factored
through `minimalPeriod_pow_of_isPrimitiveRoot`.
-/

@[expose] public section

namespace TauCeti

variable {K : Type*} [CommRing K] [IsDomain K]

/-- If `1 < q`, `9 ∣ q - 1`, `ξ` is a primitive `(q ^ (3 ^ (e + 1)) - 1)`-th root of unity in an
integral domain `K`, and `l` is prime, then `ξ ^ (l ^ a)` has minimal period `3 ^ (e + 1)` under
the `q`-th power map `x ↦ x ^ q`. -/
theorem minimalPeriod_pow_of_isPrimitiveRoot {q e l : ℕ} {ξ : K} (a : ℕ)
    (hq : 1 < q) (h_nine : 9 ∣ q - 1) (hξ : IsPrimitiveRoot ξ (q ^ 3 ^ (e + 1) - 1))
    (hl : Nat.Prime l) :
    Function.minimalPeriod (fun x : K ↦ x ^ q) (ξ ^ l ^ a) = 3 ^ (e + 1) := by
  have h_one_lt_pow : 1 < q ^ 3 ^ e := one_lt_pow₀ hq (by positivity)
  have h_one_lt_pow1 : 1 < q ^ 3 ^ (e + 1) := one_lt_pow₀ hq (by positivity)
  obtain ⟨s, hs_sub⟩ : 9 ∣ q ^ 3 ^ e - 1 := (Nat.modEq_iff_dvd' h_one_lt_pow.le).mp
    (by simpa using ((Nat.modEq_iff_dvd' hq.le).mpr h_nine).pow (3 ^ e))
  have hs : q ^ 3 ^ e = 9 * s + 1 := by omega
  have : s ≠ 0 := by omega
  have hξ_ne : ξ ≠ 0 := hξ.ne_zero (by omega)
  have hξ_fixed : ξ ^ q ^ 3 ^ (e + 1) = ξ := by
    have h := congrArg (· * ξ) hξ.pow_eq_one
    rwa [one_mul, ← pow_succ, Nat.sub_add_cancel h_one_lt_pow1.le] at h
  set b : ℕ := s * (81 * s + 27) + 3
  have h_order_eq : q ^ 3 ^ (e + 1) - 1 = 9 * s * b := by rw [pow_succ, pow_mul, hs]; lia
  have h_primitive : IsPrimitiveRoot (ξ ^ (9 * s)) b := hξ.pow (by omega) h_order_eq
  have h_not_dvd : ¬b ∣ l ^ a := by
    intro h_dvd_pow
    obtain rfl : 3 = l :=
      Nat.prime_eq_prime_of_dvd_pow Nat.prime_three hl ((by lia : 3 ∣ b).trans h_dvd_pow)
    obtain ⟨i, _, hb_eq⟩ : ∃ i ≤ a, b = 3 ^ i := (Nat.dvd_prime_pow hl).mp h_dvd_pow
    rcases i with _ | _ | i
    · lia
    · lia
    · have : 9 ∣ b := hb_eq ▸ ⟨3 ^ i, by ring⟩; lia
  have h_iter (m : ℕ) (x : K) : (fun y : K ↦ y ^ q)^[m] x = x ^ q ^ m := by
    induction m with | zero => simp | succ m ih => simp [Function.iterate_succ_apply', ih, pow_succ,
      pow_mul]
  refine Function.minimalPeriod_eq_prime_pow (hp := ⟨Nat.prime_three⟩) ?_ ?_
  · have h_pow_ne_one : ¬(ξ ^ (9 * s)) ^ l ^ a = 1 :=
      mt (h_primitive.dvd_of_pow_eq_one _) h_not_dvd
    rw [Function.IsPeriodicPt, Function.IsFixedPt, h_iter, hs, pow_succ, pow_mul,
      pow_right_comm ξ (l ^ a)]
    intro h_eq
    exact h_pow_ne_one (mul_right_cancel₀ (pow_ne_zero _ hξ_ne)
      (by simpa [one_mul, ← pow_mul, mul_comm, mul_left_comm, mul_assoc] using h_eq))
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, h_iter, pow_right_comm ξ (l ^ a), hξ_fixed]

/-- Under the hypotheses of `minimalPeriod_pow_of_isPrimitiveRoot`, the `q ^ i`-th powers of
`ξ ^ (l ^ a)` for `0 ≤ i < 3 ^ (e + 1)` are pairwise distinct. -/
theorem injOn_Iio_pow_pow_of_isPrimitiveRoot {q e l : ℕ} {ξ : K} (a : ℕ)
    (hq : 1 < q) (h_nine : 9 ∣ q - 1) (hξ : IsPrimitiveRoot ξ (q ^ 3 ^ (e + 1) - 1))
    (hl : Nat.Prime l) :
    (Set.Iio (3 ^ (e + 1))).InjOn fun i : ℕ ↦ (ξ ^ l ^ a) ^ q ^ i := by
  have h_iter (m : ℕ) (x : K) : (fun y : K ↦ y ^ q)^[m] x = x ^ q ^ m := by
    induction m with
    | zero => simp
    | succ m ih => simp [Function.iterate_succ_apply', ih, pow_succ, pow_mul]
  have h_per := minimalPeriod_pow_of_isPrimitiveRoot a hq h_nine hξ hl
  have h_inj := Function.iterate_injOn_Iio_minimalPeriod (f := fun x : K ↦ x ^ q) (x := ξ ^ l ^ a)
  rw [h_per] at h_inj
  refine fun i hi j hj hij ↦ h_inj hi hj ?_
  simpa [h_iter] using hij

/-- Under the hypotheses of `minimalPeriod_pow_of_isPrimitiveRoot`, `ξ ^ (l ^ a)` is not fixed
by `x ↦ x ^ (q ^ i)` for any `0 < i < 3 ^ (e + 1)`. -/
theorem pow_pow_ne_self_of_lt_three_pow {q e l : ℕ} {ξ : K} (a : ℕ)
    (hq : 1 < q) (h_nine : 9 ∣ q - 1) (hξ : IsPrimitiveRoot ξ (q ^ 3 ^ (e + 1) - 1))
    (hl : Nat.Prime l) {i : ℕ} (hi0 : 0 < i) (hi : i < 3 ^ (e + 1)) :
    (ξ ^ l ^ a) ^ q ^ i ≠ ξ ^ l ^ a := by
  intro h
  have h_inj := injOn_Iio_pow_pow_of_isPrimitiveRoot a hq h_nine hξ hl
  have h0 : (0 : ℕ) ∈ Set.Iio (3 ^ (e + 1)) := Nat.pos_of_ne_zero (by positivity)
  have := h_inj hi h0 (by simpa using h)
  omega

end TauCeti
