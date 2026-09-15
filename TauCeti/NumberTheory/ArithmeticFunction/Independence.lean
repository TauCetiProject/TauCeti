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
* `ArithmeticFunction.IsMultiplicative.eq_of_eq_on_primes_of_rec`: two multiplicative functions
  obeying the same recurrence and agreeing at every prime are equal.
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
Mathlib's `ArithmeticFunction.IsMultiplicative` and an arbitrary commutative ring, with the
independence results asking only that it have no zero divisors.

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], Theorem 5.8.2.
* Miyake, *Modular forms*, Theorem 4.6.12.
-/

public section

namespace ArithmeticFunction

variable {R : Type*} [CommRing R]

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
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 => rw [pow_zero, h1]
    | 1 => simpa using hp p hprime
    | (r + 2) =>
      rw [hfr p hprime r, hgr p hprime r, hp p hprime, ih (r + 1) (by omega), ih r (by omega)]

namespace IsMultiplicative

/-- **Two multiplicative functions with a common recurrence agreeing at the primes are equal.**
`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers` reduces equality to the prime
powers, and `eq_on_prime_pow_of_eq_on_primes_of_rec` supplies those. -/
theorem eq_of_eq_on_primes_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w)
    (hp : ∀ p : ℕ, p.Prime → f p = g p) : f = g :=
  (eq_iff_eq_on_prime_powers f hf g hg).2 fun _p a hprime ↦
    eq_on_prime_pow_of_eq_on_primes_of_rec (hf.1.trans hg.1.symm) hfr hgr hp hprime a

/-- **Distinct multiplicative functions with a common recurrence differ at a prime.** The
contrapositive of `eq_of_eq_on_primes_of_rec`, and the form the independence argument uses: it
is what lets a minimal relation be cut down at a single prime. -/
theorem exists_prime_ne_of_ne_of_rec {f g : ArithmeticFunction R} {w : ℕ → R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hfr : HasPrimePowerRec f w) (hgr : HasPrimePowerRec g w) (hne : f ≠ g) :
    ∃ p : ℕ, p.Prime ∧ f p ≠ g p := by
  by_contra hcon
  refine hne (eq_of_eq_on_primes_of_rec hf hg hfr hgr fun p hprime ↦ ?_)
  by_contra hne'
  exact hcon ⟨p, hprime, hne'⟩

/-- **Multiplying a vanishing relation by the value at a prime keeps it vanishing.** If
`∑ᵢ cᵢ · Gᵢ n = 0` for every `n ≥ 1` then so is `∑ᵢ cᵢ · Gᵢ p · Gᵢ n`: splitting `n = p ^ a · m`
with `p ∤ m`, the shared recurrence rewrites `Gᵢ p · Gᵢ (p ^ a)` as
`Gᵢ (p ^ (a+1)) + w p · Gᵢ (p ^ (a-1))`, and both resulting sums are instances of the original
relation. **This is the step that needs the weight to be shared by every `i`** — otherwise `w p`
could not be pulled out of the sum. -/
theorem sum_mul_prime_eq_zero {ι : Type*} {w : ℕ → R} {s : Finset ι}
    {G : ι → ArithmeticFunction R} (hmul : ∀ i ∈ s, (G i).IsMultiplicative)
    (hrec : ∀ i ∈ s, HasPrimePowerRec (G i) w) {c : ι → R}
    (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * G i n = 0)
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ s, c i * (G i p * G i n) = 0 := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hp0 : p ≠ 0 := hp.pos.ne'
  -- split off the `p`-part once and for all, keeping the cofactor opaque
  obtain ⟨a, m, hm0, hcop, rfl⟩ : ∃ a m, m ≠ 0 ∧ Nat.Coprime p m ∧ n = p ^ a * m :=
    ⟨n.factorization p, ordCompl[p] n, (Nat.ordCompl_pos p hn0).ne',
      Nat.coprime_ordCompl hp hn0, (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  have harg : ∀ k : ℕ, 1 ≤ p ^ k * m := fun k ↦
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero k hp0) hm0)
  have hpm : ∀ i ∈ s, ∀ k : ℕ, G i (p ^ k * m) = G i (p ^ k) * G i m :=
    fun i hi k ↦ (hmul i hi).2 (Nat.Coprime.pow_left k hcop)
  match a with
  | 0 =>
    -- `p ∤ n`: the prime value merges straight into the argument
    have hcop' : Nat.Coprime p (p ^ 0 * m) := by simpa using hcop
    have hmerge : ∀ i ∈ s, c i * (G i p * G i (p ^ 0 * m)) = c i * G i (p * (p ^ 0 * m)) :=
      fun i hi ↦ by rw [(hmul i hi).2 hcop']
    rw [Finset.sum_congr rfl hmerge]
    exact hrel _ (Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero hp0 (Nat.one_le_iff_ne_zero.1 (harg 0))))
  | (r + 1) =>
    -- `p ∣ n`: the recurrence trades one factor of `Gᵢ p` for two lower arguments
    have hstep : ∀ i ∈ s, c i * (G i p * G i (p ^ (r + 1) * m)) =
        c i * G i (p ^ (r + 2) * m) + w p * (c i * G i (p ^ r * m)) := fun i hi ↦ by
      have hkey : G i p * G i (p ^ (r + 1)) = G i (p ^ (r + 2)) + w p * G i (p ^ r) := by
        rw [hrec i hi p hp r]; ring
      rw [hpm i hi (r + 1), hpm i hi (r + 2), hpm i hi r]
      calc c i * (G i p * (G i (p ^ (r + 1)) * G i m))
          = c i * (G i p * G i (p ^ (r + 1)) * G i m) := by ring
        _ = c i * ((G i (p ^ (r + 2)) + w p * G i (p ^ r)) * G i m) := by rw [hkey]
        _ = _ := by ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
      hrel _ (harg (r + 2)), hrel _ (harg r), mul_zero, add_zero]

/-- **Distinct multiplicative functions with a common prime-power recurrence are independent.**
If `∑ᵢ cᵢ · Gᵢ n = 0` for every `n ≥ 1`, where the `Gᵢ` are pairwise distinct, multiplicative and
share the recurrence, then every `cᵢ` vanishes.

The textbook minimal-relation argument (Diamond–Shurman Theorem 5.8.2, Miyake Theorem 4.6.12).
Take a relation whose support is as small as possible and pick `r` in it. If the support is `{r}`
the relation at `n = 1` reads `c r = 0`. Otherwise pick another `i₀` in it and, by
`exists_prime_ne_of_ne_of_rec`, a prime `p₀` where `G r` and `G i₀` differ; then
`cᵢ' := cᵢ · (Gᵢ p₀ − G r p₀)` satisfies the same vanishing relation by
`sum_mul_prime_eq_zero`, has `c' r = 0` and `c' i₀ ≠ 0`, and so has strictly smaller nonempty
support — contradicting minimality. -/
theorem eq_zero_of_sum_mul_eq_zero {ι : Type*} [NoZeroDivisors R] {w : ℕ → R}
    {s : Finset ι} {G : ι → ArithmeticFunction R} (hmul : ∀ i ∈ s, (G i).IsMultiplicative)
    (hrec : ∀ i ∈ s, HasPrimePowerRec (G i) w)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → G i ≠ G j) {c : ι → R}
    (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * G i n = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  -- it suffices to show that a relation all of whose coefficients are nonzero has empty support
  have key : ∀ N : ℕ, ∀ t : Finset ι, ∀ d : ι → R, t.card = N → t ⊆ s → (∀ i ∈ t, d i ≠ 0) →
      (∀ n : ℕ, 1 ≤ n → ∑ i ∈ t, d i * G i n = 0) → t = ∅ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro t d hcard hsub hne hrelt
      rcases Finset.eq_empty_or_nonempty t with h | ⟨r, hr⟩
      · exact h
      exfalso
      by_cases hcard1 : t.card ≤ 1
      · -- a single term: the relation at `n = 1` says its coefficient vanishes
        have hts : t = {r} :=
          Finset.eq_singleton_iff_unique_mem.2
            ⟨hr, fun x hx ↦ Finset.card_le_one.1 hcard1 x hx r hr⟩
        have h1 := hrelt 1 le_rfl
        rw [hts, Finset.sum_singleton, (hmul r (hsub hr)).1, mul_one] at h1
        exact hne r hr h1
      · -- at least two terms: cut the support down at a prime where two of them differ
        obtain ⟨i₀, hi₀, hne₀⟩ : ∃ i₀ ∈ t, i₀ ≠ r := by
          by_contra hcon
          refine hcard1 (Finset.card_le_one.2 fun x hx y hy ↦ ?_)
          have hx' : x = r := by by_contra h; exact hcon ⟨x, hx, h⟩
          have hy' : y = r := by by_contra h; exact hcon ⟨y, hy, h⟩
          rw [hx', hy']
        obtain ⟨p, hp, hpne⟩ := exists_prime_ne_of_ne_of_rec (hmul i₀ (hsub hi₀))
          (hmul r (hsub hr)) (hrec i₀ (hsub hi₀)) (hrec r (hsub hr))
          (hdist i₀ (hsub hi₀) r (hsub hr) hne₀)
        set d' : ι → R := fun i ↦ d i * (G i p - G r p) with hd'
        have hrel' : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ t, d' i * G i n = 0 := fun n hn ↦ by
          have hmul' : ∀ i ∈ t, (G i).IsMultiplicative := fun i hi ↦ hmul i (hsub hi)
          have hrec' : ∀ i ∈ t, HasPrimePowerRec (G i) w := fun i hi ↦ hrec i (hsub hi)
          have h1 := sum_mul_prime_eq_zero hmul' hrec' hrelt hp hn
          have h2 := hrelt n hn
          calc ∑ i ∈ t, d' i * G i n
              = (∑ i ∈ t, d i * (G i p * G i n)) - G r p * ∑ i ∈ t, d i * G i n := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ ↦ by rw [hd']; ring
            _ = 0 := by rw [h1, h2]; ring
        -- the new support omits `r`, keeps `i₀`, and still satisfies the relation
        set u : Finset ι := t.filter fun i ↦ d' i ≠ 0 with hu
        have husub : u ⊆ t := Finset.filter_subset _ _
        have hru : r ∉ u := by simp [hu, hd']
        have hi₀u : i₀ ∈ u := by
          refine Finset.mem_filter.2 ⟨hi₀, ?_⟩
          exact mul_ne_zero (hne i₀ hi₀) (sub_ne_zero.2 hpne)
        have hcardu : u.card < N := by
          rw [← hcard]
          exact Finset.card_lt_card ⟨husub, fun hcon ↦ hru (hcon hr)⟩
        have hrelu : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ u, d' i * G i n = 0 := fun n hn ↦ by
          rw [Finset.sum_subset husub fun x hx hxu ↦ ?_]
          · exact hrel' n hn
          · have hzero : d' x = 0 := by
              by_contra h
              exact hxu (Finset.mem_filter.2 ⟨hx, h⟩)
            rw [hzero, zero_mul]
        have hempty : u = ∅ := ih u.card hcardu u d' rfl (husub.trans hsub)
          (fun i hi ↦ (Finset.mem_filter.1 hi).2) hrelu
        rw [hempty] at hi₀u
        exact absurd hi₀u (Finset.notMem_empty i₀)
  -- apply it to the support of `c` inside `s`
  intro i hi
  by_contra hci
  have hsupp : (s.filter fun j ↦ c j ≠ 0) = ∅ := by
    refine key _ _ c rfl (Finset.filter_subset _ _)
      (fun j hj ↦ (Finset.mem_filter.1 hj).2) ?_
    intro n hn
    rw [Finset.sum_subset (Finset.filter_subset _ _) fun x hx hxf ↦ ?_]
    · exact hrel n hn
    · have hzero : c x = 0 := by
        by_contra h
        exact hxf (Finset.mem_filter.2 ⟨hx, h⟩)
      rw [hzero, zero_mul]
  rw [Finset.eq_empty_iff_forall_notMem] at hsupp
  exact hsupp i (Finset.mem_filter.2 ⟨hi, hci⟩)

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
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, smul_map, ih,
        smul_eq_mul]
  refine linearIndependent_iff'.2 fun t g hg ↦
    eq_zero_of_sum_mul_eq_zero (fun i _ ↦ hmul i) (fun i _ ↦ hrec i)
      (fun i _ j _ hij hGij ↦ hij (hdist hGij)) fun n _ ↦ ?_
  rw [← happly t g n, hg, zero_apply]

end IsMultiplicative

end ArithmeticFunction
