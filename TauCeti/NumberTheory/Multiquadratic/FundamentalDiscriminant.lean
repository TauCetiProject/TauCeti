/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

/-!
# Fundamental discriminants

A **fundamental discriminant** is an integer `D` which is either congruent to `1` modulo `4` and
squarefree, or of the form `4 * m` with `m` squarefree and congruent to `2` or `3` modulo `4`.
These are exactly the discriminants of quadratic fields (together with `1`, the discriminant of
`ℚ` itself, which arises as the empty product below).

The genus-field layer of the multiquadratic roadmap needs the passage between a fundamental
discriminant and the **prime discriminants** dividing it: the genus field of `ℚ(√d)` is the
compositum of the quadratic fields `ℚ(√p*)` attached to the prime discriminants dividing
`disc ℚ(√d)`, and it is those prime discriminants, not the squarefree radicands, that behave
correctly at `2`. This file supplies the *synthesis* half of that passage: a product of prime
discriminants with pairwise distinct underlying primes is again a fundamental discriminant. The
analysis half (every fundamental discriminant factors as such a product, uniquely) is left to a
later file.

Since two distinct even prime discriminants are both divisible by `4`, a product of prime
discriminants can only be fundamental if at most one factor is even. The two theorems below
therefore split along exactly that line: a product of odd prime discriminants at pairwise
distinct primes, and such a product multiplied by one even prime discriminant. Every product of
pairwise coprime prime discriminants is of one of these two shapes.

## Main definitions and results

* `TauCeti.Multiquadratic.IsFundamentalDiscriminant`: the defining congruence-and-squarefreeness
  condition.
* `TauCeti.Multiquadratic.IsPrimeDiscriminant.isFundamentalDiscriminant`: every prime
  discriminant is a fundamental discriminant.
* `TauCeti.Multiquadratic.isFundamentalDiscriminant_prod_oddPrimeDiscriminant`: a product of odd
  prime discriminants at pairwise distinct odd primes is a fundamental discriminant.
* `TauCeti.Multiquadratic.isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant`: the same
  product multiplied by an even prime discriminant is a fundamental discriminant.
* `TauCeti.Multiquadratic.IsFundamentalDiscriminant.not_isSquare_rat`: a fundamental
  discriminant other than `1` is not a rational square, so `ℚ(√D)` is a genuine quadratic field.
-/

public section

namespace TauCeti.Multiquadratic

/-- A **fundamental discriminant**: either `D ≡ 1 (mod 4)` with `D` squarefree, or `D = 4 * m`
with `m` squarefree and `m ≡ 2` or `3 (mod 4)`. These are the discriminants of quadratic fields,
together with `1`. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨
    ∃ m : ℤ, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m

/-- The defining disjunction for `IsFundamentalDiscriminant`. -/
theorem isFundamentalDiscriminant_iff {D : ℤ} :
    IsFundamentalDiscriminant D ↔
      (D % 4 = 1 ∧ Squarefree D) ∨
        ∃ m : ℤ, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m :=
  Iff.rfl

/-- The discriminant of `ℚ` itself. It is the empty product of prime discriminants, and the
degenerate case of the first branch of the definition. -/
@[simp] theorem isFundamentalDiscriminant_one : IsFundamentalDiscriminant 1 :=
  Or.inl ⟨by norm_num, squarefree_one⟩

/-- A fundamental discriminant is nonzero. -/
theorem IsFundamentalDiscriminant.ne_zero {D : ℤ} (hD : IsFundamentalDiscriminant D) : D ≠ 0 := by
  rcases hD with ⟨h4, -⟩ | ⟨m, rfl, hm4, -⟩ <;> omega

/-- A fundamental discriminant is `0` or `1` modulo `4`. -/
theorem IsFundamentalDiscriminant.mod_four_eq_zero_or_one {D : ℤ}
    (hD : IsFundamentalDiscriminant D) : D % 4 = 0 ∨ D % 4 = 1 := by
  rcases hD with ⟨h4, -⟩ | ⟨m, rfl, -, -⟩
  · exact Or.inr h4
  · omega

/-- Every prime discriminant is a fundamental discriminant: the odd ones land in the first branch
of the definition, the even ones `-4, 8, -8` in the second, with radicands `-1, 2, -2`. -/
theorem IsPrimeDiscriminant.isFundamentalDiscriminant {D : ℤ} (hD : IsPrimeDiscriminant D) :
    IsFundamentalDiscriminant D := by
  rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, hodd, rfl⟩
  · refine Or.inr ⟨evenPrimeDiscriminantRadicand D, evenPrimeDiscriminant_eq_four_mul_radicand hev,
      (evenPrimeDiscriminantRadicand_mod_four_eq_three_or_two hev).symm,
      squarefree_evenPrimeDiscriminantRadicand hev⟩
  · exact Or.inl ⟨oddPrimeDiscriminant_mod_four_eq_one hodd,
      squarefree_oddPrimeDiscriminant hp.squarefree⟩

section Products

variable {ι : Type*} {s : Finset ι} {p : ι → ℕ}

/-- A product of odd prime discriminants is congruent to `1` modulo `4`: each factor is, and the
residue `1` is closed under multiplication modulo `4`. No distinctness of the primes is needed
for this. -/
theorem prod_oddPrimeDiscriminant_mod_four_eq_one (hodd : ∀ i ∈ s, Odd (p i)) :
    (∏ i ∈ s, oddPrimeDiscriminant (p i)) % 4 = 1 := by
  refine Finset.prod_induction _ (fun n => n % 4 = 1) (fun a b ha hb => ?_) (by norm_num)
    fun i hi => oddPrimeDiscriminant_mod_four_eq_one (hodd i hi)
  have hmul : a * b % 4 = a % 4 * (b % 4) % 4 := Int.mul_emod a b 4
  rw [ha, hb] at hmul
  simpa using hmul

/-- A product of odd prime discriminants is odd. -/
theorem odd_prod_oddPrimeDiscriminant (hodd : ∀ i ∈ s, Odd (p i)) :
    ¬ (2 : ℤ) ∣ ∏ i ∈ s, oddPrimeDiscriminant (p i) := by
  intro hdvd
  have h := prod_oddPrimeDiscriminant_mod_four_eq_one hodd
  omega

/-- A product of odd prime discriminants at pairwise distinct primes is squarefree: the factors
are distinct primes of `ℤ` up to sign, hence pairwise relatively prime, and each is squarefree. -/
theorem squarefree_prod_oddPrimeDiscriminant (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p s) :
    Squarefree (∏ i ∈ s, oddPrimeDiscriminant (p i)) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i hi j hj hij => ?_)
    fun i hi => squarefree_oddPrimeDiscriminant (hp i hi).squarefree
  have hpij : p i ≠ p j := fun h => hij (hinj hi hj h)
  refine (Irreducible.isRelPrime_iff_not_dvd
    (Prime.irreducible (prime_oddPrimeDiscriminant (hp i hi)))).mpr ?_
  simp only [oddPrimeDiscriminant_dvd_iff, dvd_oddPrimeDiscriminant_iff, Int.natCast_dvd_natCast]
  exact fun hdvd => hpij ((Nat.prime_dvd_prime_iff_eq (hp i hi) (hp j hj)).mp hdvd)

/-- **A product of odd prime discriminants is a fundamental discriminant**, provided the
underlying odd primes are pairwise distinct. The empty product recovers
`isFundamentalDiscriminant_one`. -/
theorem isFundamentalDiscriminant_prod_oddPrimeDiscriminant (hp : ∀ i ∈ s, (p i).Prime)
    (hodd : ∀ i ∈ s, Odd (p i)) (hinj : Set.InjOn p s) :
    IsFundamentalDiscriminant (∏ i ∈ s, oddPrimeDiscriminant (p i)) :=
  Or.inl ⟨prod_oddPrimeDiscriminant_mod_four_eq_one hodd,
    squarefree_prod_oddPrimeDiscriminant hp hinj⟩

/-- Negation preserves squarefreeness in `ℤ`. -/
private theorem squarefree_neg {n : ℤ} (hn : Squarefree n) : Squarefree (-n) := by
  rwa [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]

/-- **An even prime discriminant times a product of odd prime discriminants is a fundamental
discriminant**, provided the underlying odd primes are pairwise distinct. Together with
`isFundamentalDiscriminant_prod_oddPrimeDiscriminant` this covers every product of pairwise
coprime prime discriminants, since two even prime discriminants are never coprime.

The `2`-adic bookkeeping is the content: writing `Q` for the odd product, we have `Q ≡ 1 (mod 4)`,
and the three even cases produce `4 * (-Q)`, `4 * (2 * Q)` and `4 * (-(2 * Q))`, whose inner
factors are `3`, `2` and `2` modulo `4` respectively. -/
theorem isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant {e : ℤ}
    (he : IsEvenPrimeDiscriminant e) (hp : ∀ i ∈ s, (p i).Prime) (hodd : ∀ i ∈ s, Odd (p i))
    (hinj : Set.InjOn p s) :
    IsFundamentalDiscriminant (e * ∏ i ∈ s, oddPrimeDiscriminant (p i)) := by
  set Q : ℤ := ∏ i ∈ s, oddPrimeDiscriminant (p i) with hQ
  have hQ4 : Q % 4 = 1 := prod_oddPrimeDiscriminant_mod_four_eq_one hodd
  have hQsf : Squarefree Q := squarefree_prod_oddPrimeDiscriminant hp hinj
  have hQ2 : ¬ (2 : ℤ) ∣ Q := odd_prod_oddPrimeDiscriminant hodd
  have hsf2 : Squarefree (2 * Q) :=
    squarefree_mul_iff.mpr
      ⟨(Irreducible.isRelPrime_iff_not_dvd (Prime.irreducible Int.prime_two)).mpr hQ2,
        Prime.squarefree Int.prime_two, hQsf⟩
  rcases he with rfl | rfl | rfl
  · exact Or.inr ⟨-Q, by ring, Or.inr (by omega), squarefree_neg hQsf⟩
  · exact Or.inr ⟨2 * Q, by ring, Or.inl (by omega), hsf2⟩
  · exact Or.inr ⟨-(2 * Q), by ring, Or.inl (by omega), squarefree_neg hsf2⟩

end Products

/-- A fundamental discriminant other than `1` is not a rational square. Consequently `ℚ(√D)` is a
genuine quadratic field: this is what keeps the genus-field constructions non-degenerate. -/
theorem IsFundamentalDiscriminant.not_isSquare_rat {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (h1 : D ≠ 1) : ¬ IsSquare ((D : ℤ) : ℚ) := by
  rcases hD with ⟨h4, hsf⟩ | ⟨m, rfl, hm4, hmsf⟩
  · rw [Rat.isSquare_intCast_iff]
    refine hsf.not_isSquare fun hu => ?_
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · exact h1 rfl
    · omega
  · rintro ⟨x, hx⟩
    have hx' : (4 : ℚ) * (m : ℚ) = x * x := by exact_mod_cast hx
    have hm : IsSquare ((m : ℤ) : ℚ) := ⟨x / 2, by field_simp; linarith⟩
    rw [Rat.isSquare_intCast_iff] at hm
    rcases eq_or_ne m (-1) with rfl | hm1
    · exact absurd hm.nonneg (by norm_num)
    · refine hmsf.not_isSquare (fun hu => ?_) hm
      rcases Int.isUnit_iff.mp hu with rfl | rfl
      · omega
      · exact hm1 rfl

section Examples

/-- **Worked example.** `-20`, the discriminant of `ℚ(√-5)`, is a fundamental discriminant: it is
the product of the prime discriminants `-4` and `5`, whose square roots generate the genus field
`ℚ(√-1, √5)`. -/
theorem isFundamentalDiscriminant_neg_twenty : IsFundamentalDiscriminant (-20) := by
  have h := isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant
    isEvenPrimeDiscriminant_neg_four (s := ({5} : Finset ℕ)) (p := id)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst hi; norm_num)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst hi; exact Nat.odd_iff.mpr rfl)
    (by simp)
  norm_num [oddPrimeDiscriminant] at h
  exact h

/-- **Worked example.** `-84`, the discriminant of `ℚ(√-21)`, is a fundamental discriminant: it is
the product of the prime discriminants `-4`, `-3` and `-7`, whose square roots generate the genus
field `ℚ(√-1, √-3, √-7)`. -/
theorem isFundamentalDiscriminant_neg_eightyfour : IsFundamentalDiscriminant (-84) := by
  have h := isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant
    isEvenPrimeDiscriminant_neg_four (s := ({3, 7} : Finset ℕ)) (p := id)
    (by intro i hi; fin_cases hi <;> norm_num)
    (by intro i hi; fin_cases hi <;> exact Nat.odd_iff.mpr rfl)
    (by intro i hi j hj hij; simpa using hij)
  norm_num [oddPrimeDiscriminant] at h
  exact h

end Examples

end TauCeti.Multiquadratic
