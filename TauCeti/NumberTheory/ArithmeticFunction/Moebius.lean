/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Divisor sums of the Möbius function over coprime divisors

For a prime `p` and a natural number `n`, the divisors of `n` coprime to `p` are the divisors of
the `p`-free part `ordCompl[p] n`. Summing the Möbius function `μ` over those divisors for `m ≠ 0`
evaluates to `(μ * ζ) (ordCompl[p] m)`: it is `1` when `ordCompl[p] m = 1`, that is, when `m` is a
power of `p`, and `0` otherwise.

This indicator identity is the arithmetic mechanism behind Cartier's `p`-typicalization operator on
curves of a formal group law, which applies a Möbius-weighted sum over positive integers coprime to
`p` to project a formal logarithm onto its `p`-power degrees.

## Main results

* `Nat.filter_coprime_divisors_eq_divisors_ordCompl`: the divisors of `n` coprime to a prime `p`
  are the divisors of `ordCompl[p] n`.
* `Nat.ordCompl_eq_one_iff_exists_eq_pow`: for `m ≠ 0` and prime `p`, `ordCompl[p] m = 1` iff `m`
  is a power of `p`.
* `ArithmeticFunction.sum_divisors_moebius`: `∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0`.
* `ArithmeticFunction.sum_divisors_filter_coprime_moebius`: for `m ≠ 0` and prime `p`,
  `∑ d ∈ m.divisors with d.Coprime p, μ d = if ∃ k, m = p ^ k then 1 else 0`.
-/

public section

namespace Nat

/-- For a prime `p`, the divisors of `n` coprime to `p` are the divisors of the prime-to-`p` part
`ordCompl[p] n`. -/
theorem filter_coprime_divisors_eq_divisors_ordCompl {n p : ℕ} (hp : p.Prime) :
    {d ∈ n.divisors | d.Coprime p} = (ordCompl[p] n).divisors := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  ext d
  simp only [Finset.mem_filter, mem_divisors, hn, (ordCompl_pos p hn).ne', ne_eq, not_false_eq_true,
    and_true]
  refine ⟨fun ⟨hdn, hcop⟩ ↦ dvd_ordCompl_of_dvd_not_dvd hdn ?_, fun hd ↦
    ⟨dvd_trans hd (ordCompl_dvd n p), (coprime_ordCompl hp hn).symm.coprime_dvd_left hd⟩⟩
  exact fun hpd ↦ hp.not_dvd_one (hcop ▸ dvd_gcd hpd dvd_rfl)

/-- A nonzero natural number `m` has `p`-free part `1`, for a prime `p`, precisely when `m` is a
power of `p`. -/
theorem ordCompl_eq_one_iff_exists_eq_pow {m p : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    ordCompl[p] m = 1 ↔ ∃ k : ℕ, m = p ^ k := by
  refine ⟨fun h ↦ ⟨m.factorization p, ?_⟩, ?_⟩
  · have hmul := ordProj_mul_ordCompl_eq_self m p
    rwa [h, mul_one, eq_comm] at hmul
  · rintro ⟨k, rfl⟩
    exact ordCompl_self_pow hp

end Nat

namespace ArithmeticFunction

open scoped Moebius zeta

/-- Summing the Möbius function over the divisors of `n` gives `1` at `n = 1` and `0` otherwise. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · simp [hn]

/-- For a prime `p` and `m ≠ 0`, summing `μ d` over the divisors `d` of `m` coprime to `p` gives
`1` when `m` is a power of `p` and `0` otherwise. -/
theorem sum_divisors_filter_coprime_moebius {m p : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    [Decidable (∃ k : ℕ, m = p ^ k)] :
    (∑ d ∈ m.divisors with d.Coprime p, μ d) =
      if (∃ k : ℕ, m = p ^ k) then (1 : ℤ) else 0 := by
  rw [Nat.filter_coprime_divisors_eq_divisors_ordCompl hp, sum_divisors_moebius]
  simp [Nat.ordCompl_eq_one_iff_exists_eq_pow hp hm]

end ArithmeticFunction
