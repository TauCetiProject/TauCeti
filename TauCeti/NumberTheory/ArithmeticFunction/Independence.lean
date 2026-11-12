/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Multiplicative functions with a common prime-power recurrence

A Hecke eigensystem is multiplicative and satisfies, at every prime `p`, the recurrence

```text
a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - w p * a (p ^ r),
```

whose weight `w p` depends on the level and weight but **not** on the eigenform. This file
records what that shared recurrence buys: such a function is determined by its values at the
primes alone, so two of them that agree at every prime are equal.

Distinct such functions are therefore **linearly independent**. That is the arithmetic half of
multiplicity one for Hecke eigenforms: eigenforms with different eigenvalue systems cannot cancel
each other, whatever the coefficients. It is stated twice, because the two forms suit different
consumers: pointwise, as "a relation `∑ᵢ cᵢ · Gᵢ n = 0` holding for every `n ≥ 1` forces every
coefficient to vanish", and as `LinearIndependent R G`. The two agree because an
`ArithmeticFunction` vanishes at `0` by definition, so a module relation is exactly a pointwise
relation at every `n ≥ 1`.

## Main results

* `ArithmeticFunction.eq_on_prime_pow_of_eq_on_primes_of_rec`: the recurrence alone — no
  multiplicativity — propagates agreement from the primes to the prime powers.
* `ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_primes_of_rec`: two multiplicative functions
  obeying the same recurrence are equal if and only if they agree at every prime.
* `ArithmeticFunction.IsMultiplicative.exists_prime_ne_of_ne_of_rec`: contrapositively, two
  distinct such functions differ at some prime.
* `ArithmeticFunction.IsMultiplicative.sum_mul_prime_eq_zero`: multiplying a vanishing relation by
  the value at a prime leaves it vanishing.
* `ArithmeticFunction.IsMultiplicative.eq_zero_of_sum_mul_eq_zero`: **the independence theorem**,
  in its finite-support form, which is the elimination engine.
* `ArithmeticFunction.IsMultiplicative.linearIndependent_of_rec`: the same as
  `LinearIndependent R G`.

## References

Ported from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit
`6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`, Apache 2.0),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Newforms/MainLemmaProof.lean`
(`eq_prime_powers_of_eq_primes_of_rec`, `support_eq_empty_of_pairwise_distinct_rec`). That project
works over a bare `ℕ → ℂ` with its own multiplicativity predicate; here the statements are over
Mathlib's `ArithmeticFunction.IsMultiplicative`. The recurrence and its propagation to prime
powers need only a zero, a multiplication and a subtraction; the equality criterion needs a
commutative monoid with zero carrying a subtraction; and the independence results hold over any
commutative ring without zero divisors.

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], Theorem 5.8.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.12.
-/

public section

namespace ArithmeticFunction

section Recurrence

variable {R : Type*} [Zero R] [Mul R] [Sub R]

/-- **A common prime-power recurrence**: `f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - w p * f (p ^ r)`
at every prime `p`, with the weight `w` a function of the prime alone. For Hecke eigensystems
`w p = χ p * p ^ (k - 1)`, which is why the weight is shared by every eigenform of a given level
and weight — and that sharing is what the results here need. -/
def HasPrimePowerRec (f : ArithmeticFunction R) (w : ℕ → R) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ r : ℕ, f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - w p * f (p ^ r)

/-- **Prime values determine prime-power values, given a shared recurrence.** Two functions
obeying the same recurrence, agreeing at `1` and at every prime, agree at every prime power: the
recurrence propagates the agreement upward from `r = 0, 1`. Multiplicativity is not needed —
only the value at `1`, which is where the induction starts. -/
theorem eq_on_prime_pow_of_eq_on_primes_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (h1 : f 1 = g 1) (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w)
    (hp : ∀ p : ℕ, p.Prime → f p = g p) {p : ℕ} (hprime : p.Prime) (a : ℕ) :
    f (p ^ a) = g (p ^ a) := by
  induction a using Nat.twoStepInduction with
  | zero => rwa [pow_zero]
  | one => rw [pow_one, hp p hprime]
  | more r ih₀ ih₁ => rw [hfr p hprime r, hgr p hprime r, hp p hprime, ih₀, ih₁]

end Recurrence

namespace IsMultiplicative

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [Sub R]

/-- **Two multiplicative functions with a common recurrence are equal iff they agree at the
primes.** Compare `ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`, which needs
agreement at every prime power. -/
theorem eq_iff_eq_on_primes_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p :=
  -- equality reduces to the prime powers, where the recurrence propagates agreement upward
  ⟨fun h _ _ ↦ h ▸ rfl, fun hp ↦ (eq_iff_eq_on_prime_powers f hf g hg).2 fun _p a hprime ↦
    eq_on_prime_pow_of_eq_on_primes_of_rec (hf.1.trans hg.1.symm) hfr hgr hp hprime a⟩

/-- **Distinct multiplicative functions with a common recurrence differ at a prime.** The
contrapositive of `eq_iff_eq_on_primes_of_rec`, and the form the independence argument uses: it
is what lets a relation be cut down at a single prime. -/
theorem exists_prime_ne_of_ne_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w) (hne : f ≠ g) :
    ∃ p : ℕ, p.Prime ∧ f p ≠ g p := by
  by_contra! hcon
  exact hne ((eq_iff_eq_on_primes_of_rec hf hg hfr hgr).2 hcon)

end CommMonoidWithZero

section CommRing

variable {R : Type*} [CommRing R]

/-- **Multiplying a vanishing relation by the value at a prime keeps it vanishing.** If the `Gᵢ`
are multiplicative and share the recurrence with weight `w`, and `∑ᵢ cᵢ · Gᵢ n = 0` for every
`n ≥ 1`, then `∑ᵢ cᵢ · Gᵢ p · Gᵢ n = 0` for every prime `p` and every `n`. The weight must be
the same for every `i`. -/
theorem sum_mul_prime_eq_zero {ι : Type*} {w : ℕ → R} {s : Finset ι}
    {G : ι → ArithmeticFunction R} (hmul : ∀ i ∈ s, (G i).IsMultiplicative)
    (hrec : ∀ i ∈ s, HasPrimePowerRec (G i) w) {c : ι → R}
    (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * G i n = 0)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∑ i ∈ s, c i * (G i p * G i n) = 0 := by
  -- Split `n = p ^ a · m` with `p ∤ m`. The shared recurrence rewrites `Gᵢ p · Gᵢ (p ^ (r + 1))`
  -- as `Gᵢ (p ^ (r + 2)) + w p · Gᵢ (p ^ r)`, and both resulting sums are instances of the
  -- original relation; the weight being shared is what lets `w p` leave the sum.
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  -- split off the `p`-part once and for all, keeping the cofactor opaque
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpow : ∀ i ∈ s, ∀ k : ℕ, G i (p ^ k * m) = G i (p ^ k) * G i m :=
    fun i hi k ↦ (hmul i hi).2 (hcop.pow_left k)
  cases a with
  | zero =>
    -- `p ∤ n`: the prime value merges straight into the argument
    rw [pow_zero, one_mul, Finset.sum_congr rfl fun i hi ↦ by rw [← (hmul i hi).2 hcop]]
    exact hrel _ (Nat.one_le_iff_ne_zero.2 (by positivity))
  | succ r =>
    -- `p ∣ n`: the recurrence trades one factor of `Gᵢ p` for two lower arguments
    have hstep : ∀ i ∈ s, c i * (G i p * G i (p ^ (r + 1) * m)) =
        c i * G i (p ^ (r + 2) * m) + w p * (c i * G i (p ^ r * m)) := fun i hi ↦ by
      rw [hpow i hi, hpow i hi, hpow i hi, hrec i hi p hp r]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hrel (p ^ (r + 2) * m) (Nat.one_le_iff_ne_zero.2 (by positivity)),
      hrel (p ^ r * m) (Nat.one_le_iff_ne_zero.2 (by positivity))]

/-- **Distinct multiplicative functions with a common prime-power recurrence are independent.**
If `∑ᵢ cᵢ · Gᵢ n = 0` for every `n ≥ 1`, where the `Gᵢ` are pairwise distinct, multiplicative and
share the recurrence, then every `cᵢ` vanishes.

See Diamond–Shurman Theorem 5.8.2 and Miyake Theorem 4.6.12. -/
theorem eq_zero_of_sum_mul_eq_zero {ι : Type*} [NoZeroDivisors R] {w : ℕ → R}
    {s : Finset ι} {G : ι → ArithmeticFunction R} (hmul : ∀ i ∈ s, (G i).IsMultiplicative)
    (hrec : ∀ i ∈ s, HasPrimePowerRec (G i) w) (hdist : Set.InjOn G s) {c : ι → R}
    (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * G i n = 0) :
    ∀ i ∈ s, c i = 0 := by
  -- The textbook elimination argument, by induction on `s`. For `s = insert r t` and `j ∈ t`,
  -- pick a prime `p` where `G j` and `G r` differ; then `cᵢ' := cᵢ · (Gᵢ p − G r p)` satisfies
  -- the same vanishing relation and `c' r = 0`, so it is a relation over `t`, and the induction
  -- hypothesis gives `c' j = 0`, hence `c j = 0`. With every coefficient on `t` vanishing, the
  -- relation at `n = 1` reads `c r = 0`.
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | insert r t hr ih =>
    have hmulr := hmul r (Finset.mem_insert_self r t)
    have hrecr := hrec r (Finset.mem_insert_self r t)
    -- every coefficient on `t` vanishes: weighting the relation at a prime where `G j` and `G r`
    -- differ kills the `r`-term, and the induction hypothesis applies to the rest
    have ht : ∀ j ∈ t, c j = 0 := fun j hj ↦ by
      have hjt : j ∈ insert r t := Finset.mem_insert_of_mem hj
      obtain ⟨p, hp, hpne⟩ := exists_prime_ne_of_ne_of_rec (hmul j hjt) hmulr (hrec j hjt) hrecr
        fun h ↦ hr (hdist (by simpa using hjt) (by simp) h ▸ hj)
      have hrel' : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ t, c i * (G i p - G r p) * G i n = 0 := fun n hn ↦ by
        have h : ∑ i ∈ insert r t, c i * (G i p - G r p) * G i n =
            ∑ i ∈ insert r t, c i * (G i p * G i n) - G r p * ∑ i ∈ insert r t, c i * G i n := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
        rw [sum_mul_prime_eq_zero hmul hrec hrel hp n, hrel n hn, Finset.sum_insert hr] at h
        simpa using h
      have := ih (fun i hi ↦ hmul i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hrec i (Finset.mem_insert_of_mem hi))
        (hdist.mono (by simp)) hrel' j hj
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hpne)
    -- the relation at `n = 1` then reads `c r = 0`
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · have h1 := hrel 1 le_rfl
      rw [Finset.sum_insert hr, Finset.sum_eq_zero fun j hj ↦ by rw [ht j hj, zero_mul]] at h1
      simpa [hmulr.map_one] using h1
    · exact ht i hi

/-- **Distinct multiplicative functions with a common prime-power recurrence are linearly
independent**, in Mathlib's sense: the family `G` is `LinearIndependent R`.

This is `eq_zero_of_sum_mul_eq_zero` read through `linearIndependent_iff'`. The two say the same
thing, because an `ArithmeticFunction` vanishes at `0` by definition: a module relation
`∑ᵢ gᵢ • Gᵢ = 0` is exactly a pointwise relation at every `n ≥ 1`. Which form is convenient
depends on the consumer — the finite-support statement is the elimination engine, this one is what
plugs into the linear-algebra API. -/
theorem linearIndependent_of_rec {ι : Type*} [NoZeroDivisors R] {w : ℕ → R}
    {G : ι → ArithmeticFunction R} (hmul : ∀ i, (G i).IsMultiplicative)
    (hrec : ∀ i, HasPrimePowerRec (G i) w) (hdist : Function.Injective G) :
    LinearIndependent R G := by
  classical
  have happly : ∀ (t : Finset ι) (g : ι → R) (n : ℕ),
      (∑ i ∈ t, g i • G i) n = ∑ i ∈ t, g i * G i n := by
    intro t g n
    induction t using Finset.induction with
    | empty => simp
    | insert a t ha ih => simp [Finset.sum_insert ha, ih]
  refine linearIndependent_iff'.2 fun t g hg ↦
    eq_zero_of_sum_mul_eq_zero (fun i _ ↦ hmul i) (fun i _ ↦ hrec i) hdist.injOn fun n _ ↦ ?_
  rw [← happly t g n, hg, _root_.zero_apply]

end CommRing

end IsMultiplicative

end ArithmeticFunction
