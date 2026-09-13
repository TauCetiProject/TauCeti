/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Sequences with a Hecke-type recurrence at the primes

A sequence `a : ℕ → R` satisfying, at every prime `p` coprime to an auxiliary `L` and every `m`
coprime to `L`, a recurrence `a_{pm} = c · a_m − d · a_{m/p}` (the last term present only when
`p ∣ m`) for some scalars `c`, `d`, vanishes at every `n ≠ 0` coprime to `L` as soon as `a₁ = 0`.
This is the combinatorial content of the vanishing of the Fourier coefficients of a Hecke
eigenform with `a₁ = 0` at the good indices, where `c` is the eigenvalue at `p` and
`d = χ(p) p^{k−1}`.

## Main results

* `TauCeti.eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime`: the vanishing
  at the indices coprime to `L`.

## References

* [T. Miyake, *Modular forms*][miyake1989], §4.6 — the vanishing induction this lemma is the
  arithmetic core of.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
-/

public section

namespace TauCeti

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- **A sequence with a Hecke-type prime recurrence and `a₁ = 0` vanishes at the indices
coprime to `L`.** If at every prime `p` coprime to `L` there are scalars `c`, `d` with
`a_{pm} = c · a_m − d · a_{m/p}` (the last term only when `p ∣ m`) for every `m` coprime to `L`,
and `a₁ = 0`, then `a_n = 0` for every `n ≠ 0` coprime to `L`. -/
theorem eq_zero_of_forall_prime_mul_eq_of_one_eq_zero_of_ne_zero_of_coprime {a : ℕ → R} {L : ℕ}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p L → ∃ c d : R, ∀ m : ℕ, Nat.Coprime m L →
      a (p * m) = c * a m - if p ∣ m then d * a (m / p) else 0)
    (h1 : a 1 = 0) (n : ℕ) (hn0 : n ≠ 0) (hn : Nat.Coprime n L) : a n = 0 := by
  -- Strong induction on `n`: the recurrence at the least prime factor of `n` expresses `a n`
  -- through terms at smaller indices, which remain coprime to `L`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exact absurd rfl hn0
    · exact h1
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  have hpL : Nat.Coprime n.minFac L := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) hn
  have hmL : Nat.Coprime m L := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hm.symm) hn
  have hm0 : m ≠ 0 := fun h0 ↦ hn0 (by rw [hm, h0, mul_zero])
  have hmn : m < n :=
    hm ▸ (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hm0)).mpr hp.one_lt
  obtain ⟨c, d, hcd⟩ := ha _ hp hpL
  rw [hm, hcd m hmL, ih m hmn hm0 hmL, mul_zero, zero_sub]
  split_ifs with hpm
  · rw [ih (m / n.minFac) ((Nat.div_le_self m _).trans_lt hmn)
      (Nat.div_ne_zero_iff_of_dvd hpm |>.mpr ⟨hm0, hp.ne_zero⟩)
      (Nat.Coprime.coprime_div_left hmL hpm), mul_zero, neg_zero]
  · exact neg_zero

end TauCeti
