/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FundamentalDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants

/-!
# Fundamental discriminants

A **fundamental discriminant** is an integer `D` which is either congruent to `1` modulo `4` and
squarefree, or of the form `4 * m` with `m` squarefree and congruent to `2` or `3` modulo `4`.
These are exactly the discriminants of quadratic fields (together with `1`, the discriminant of
`ℚ` itself, which arises as the empty product below). The predicate is Mathlib's
`Int.IsFundamentalDiscr`, and this description is its characterization
`Int.isFundamentalDiscr_iff_squarefree`.

The genus-field layer of the multiquadratic roadmap needs the passage between a fundamental
discriminant and the **prime discriminants** dividing it: the genus field of `ℚ(√d)` is the
compositum of the quadratic fields `ℚ(√p*)` attached to the prime discriminants dividing
`disc ℚ(√d)`, and it is those prime discriminants, not the squarefree radicands, that behave
correctly at `2`. This file supplies the *synthesis* half of that passage: a product of prime
discriminants with pairwise distinct underlying primes is again a fundamental discriminant. The
analysis half (every fundamental discriminant factors as such a product, uniquely) is left to a
later file.

Since two distinct even prime discriminants are both divisible by `4`, a product of prime
discriminants can only be fundamental if at most one factor is even. The two component theorems
below therefore split along exactly that line: a product of odd prime discriminants at pairwise
distinct primes, and such a product multiplied by one even prime discriminant. Every product of
pairwise coprime prime discriminants is of one of these two shapes, and the general theorem
`isFundamentalDiscr_prod` assembles the two cases for distinct prime discriminants with at
most one even value; `isFundamentalDiscr_prod_of_pairwise_isCoprime` gives the
pairwise-coprime specialization.

The definition of a fundamental discriminant and the fact that products of prime discriminants
are fundamental are classical; see Cox, *Primes of the Form x² + ny²*, and Lemmermeyer,
*Reciprocity Laws*, following the same prime-discriminant convention as the sibling files in this
directory. The `-20` and `-84` worked examples of the `Worked examples` section of
`TauCetiRoadmap/Multiquadratic/README.md` have their fundamental-discriminant component established
in `FundamentalDiscriminant/Examples.lean`; their class-group and concrete genus-field
identifications remain future work.

## Main results

* `TauCeti.Multiquadratic.IsPrimeDiscriminant.isFundamentalDiscr`: every prime
  discriminant is a fundamental discriminant.
* `TauCeti.Multiquadratic.isFundamentalDiscr_prod`: a product of distinct prime
  discriminants with at most one even value is a fundamental discriminant.
* `TauCeti.Multiquadratic.isFundamentalDiscr_prod_of_pairwise_isCoprime`: the
  pairwise-coprime specialization.
* `TauCeti.Multiquadratic.isFundamentalDiscr_prod_oddPrimeDiscriminant` and its even-factor
  companion `..._of_isEvenPrimeDiscriminant`: the two shape-specific component theorems that
  `isFundamentalDiscr_prod` assembles.

The generic `Int.IsFundamentalDiscr` fact `Int.IsFundamentalDiscr.not_isSquare_rat` lives in
`TauCeti.NumberTheory.FundamentalDiscriminant`.
-/

public section

namespace TauCeti.Multiquadratic

/-- Every prime discriminant is a fundamental discriminant: the odd ones are `1` modulo `4` and
squarefree, the even ones `-4, 8, -8` are `4` times the radicands `-1, 2, -2`. -/
theorem IsPrimeDiscriminant.isFundamentalDiscr {D : ℤ} (hD : IsPrimeDiscriminant D) :
    Int.IsFundamentalDiscr D := by
  rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, hodd, rfl⟩
  · rw [evenPrimeDiscriminant_eq_four_mul_radicand hev]
    exact Int.isFundamentalDiscr_four_mul.mpr ⟨squarefree_evenPrimeDiscriminantRadicand hev,
      (evenPrimeDiscriminantRadicand_mod_four_eq_three_or_two hev).symm⟩
  · exact Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl
      ⟨oddPrimeDiscriminant_mod_four_eq_one hodd, squarefree_oddPrimeDiscriminant hp.squarefree⟩)

/-- A prime discriminant is not a unit: its absolute value is `4`, `8`, or an odd prime. -/
private theorem IsPrimeDiscriminant.not_isUnit {D : ℤ} (hD : IsPrimeDiscriminant D) :
    ¬ IsUnit D := by
  rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, -, rfl⟩
  · rcases hev with rfl | rfl | rfl <;> simp [Int.isUnit_iff]
  · exact (prime_oddPrimeDiscriminant hp).not_isUnit

/-- A prime discriminant that is not even is `oddPrimeDiscriminant` of its (odd, prime) absolute
value. -/
private theorem eq_oddPrimeDiscriminant_natAbs {D : ℤ} (hD : IsPrimeDiscriminant D)
    (hev : ¬ IsEvenPrimeDiscriminant D) :
    (D.natAbs).Prime ∧ Odd D.natAbs ∧ D = oddPrimeDiscriminant D.natAbs := by
  rcases isPrimeDiscriminant_iff.mp hD with h | ⟨p, hp, hpodd, rfl⟩
  · exact absurd h hev
  · rw [oddPrimeDiscriminant_natAbs]
    exact ⟨hp, hpodd, rfl⟩

section Products

variable {ι : Type*} {s : Finset ι} {p : ι → ℕ}

/-- A product of odd prime discriminants is congruent to `1` modulo `4`. No distinctness of the
underlying primes is needed. -/
theorem prod_oddPrimeDiscriminant_mod_four_eq_one (hodd : ∀ i ∈ s, Odd (p i)) :
    (∏ i ∈ s, oddPrimeDiscriminant (p i)) % 4 = 1 := by
  rw [Finset.prod_int_mod,
    Finset.prod_congr rfl fun i hi => oddPrimeDiscriminant_mod_four_eq_one (hodd i hi)]
  simp

/-- A product of odd prime discriminants is odd. -/
theorem odd_prod_oddPrimeDiscriminant (hodd : ∀ i ∈ s, Odd (p i)) :
    Odd (∏ i ∈ s, oddPrimeDiscriminant (p i)) := by
  rw [Int.odd_iff]
  have h := prod_oddPrimeDiscriminant_mod_four_eq_one hodd
  omega

/-- A product of odd prime discriminants at pairwise distinct primes is squarefree. -/
theorem squarefree_prod_oddPrimeDiscriminant (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    Squarefree (∏ i ∈ s, oddPrimeDiscriminant (p i)) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i hi j hj hij => ?_)
    fun i hi => squarefree_oddPrimeDiscriminant (hp i hi).squarefree
  have hpij : p i ≠ p j := fun h => hij (hinj hi hj h)
  refine (Irreducible.isRelPrime_iff_not_dvd
    (Prime.irreducible (prime_oddPrimeDiscriminant (hp i hi)))).mpr ?_
  simp only [oddPrimeDiscriminant_dvd_iff, dvd_oddPrimeDiscriminant_iff, Int.natCast_dvd_natCast]
  exact fun hdvd => hpij ((Nat.prime_dvd_prime_iff_eq (hp i hi) (hp j hj)).mp hdvd)

/-- **A product of odd prime discriminants is a fundamental discriminant**, provided the
underlying odd primes are pairwise distinct. The empty product recovers the fundamental
discriminant `1` of `ℚ`. -/
theorem isFundamentalDiscr_prod_oddPrimeDiscriminant (hp : ∀ i ∈ s, (p i).Prime)
    (hodd : ∀ i ∈ s, Odd (p i)) (hinj : Set.InjOn p s) :
    Int.IsFundamentalDiscr (∏ i ∈ s, oddPrimeDiscriminant (p i)) :=
  Int.isFundamentalDiscr_iff_squarefree.mpr <|
    Or.inl ⟨prod_oddPrimeDiscriminant_mod_four_eq_one hodd,
      squarefree_prod_oddPrimeDiscriminant hp hinj⟩

/-- **An even prime discriminant times a product of odd prime discriminants is a fundamental
discriminant**, provided the underlying odd primes are pairwise distinct. Together with
`isFundamentalDiscr_prod_oddPrimeDiscriminant` this covers every product of pairwise
coprime prime discriminants, since two even prime discriminants are never coprime; see
`isFundamentalDiscr_prod` for the assembled statement. -/
theorem isFundamentalDiscr_mul_prod_oddPrimeDiscriminant_of_isEvenPrimeDiscriminant {e : ℤ}
    (he : IsEvenPrimeDiscriminant e) (hp : ∀ i ∈ s, (p i).Prime) (hodd : ∀ i ∈ s, Odd (p i))
    (hinj : Set.InjOn p s) :
    Int.IsFundamentalDiscr (e * ∏ i ∈ s, oddPrimeDiscriminant (p i)) := by
  -- Writing `Q` for the odd product, `Q ≡ 1 (mod 4)`, and the three even cases produce
  -- `4 * (-Q)`, `4 * (2 * Q)` and `4 * (-(2 * Q))`, whose inner factors are `3`, `2` and `2`
  -- modulo `4` respectively.
  set Q : ℤ := ∏ i ∈ s, oddPrimeDiscriminant (p i)
  have hQ4 : Q % 4 = 1 := prod_oddPrimeDiscriminant_mod_four_eq_one hodd
  have hQsf : Squarefree Q := squarefree_prod_oddPrimeDiscriminant hp hinj
  have hQ2 : ¬ (2 : ℤ) ∣ Q := by omega
  have hsf2 : Squarefree (2 * Q) :=
    squarefree_mul_iff.mpr
      ⟨(Irreducible.isRelPrime_iff_not_dvd (Prime.irreducible Int.prime_two)).mpr hQ2,
        Prime.squarefree Int.prime_two, hQsf⟩
  rcases he with rfl | rfl | rfl
  · convert (Int.isFundamentalDiscr_four_mul (m := -Q)).mpr
      ⟨hQsf.neg, Or.inr (by omega)⟩ using 1
    ring
  · convert (Int.isFundamentalDiscr_four_mul (m := 2 * Q)).mpr
      ⟨hsf2, Or.inl (by omega)⟩ using 1
    ring
  · convert (Int.isFundamentalDiscr_four_mul (m := -(2 * Q))).mpr
      ⟨hsf2.neg, Or.inl (by omega)⟩ using 1
    ring

/-- The shared normalisation step of `isFundamentalDiscr_prod`: over a set `t` of prime
discriminants, none of them even and with pairwise distinct values, each `D i` is
`oddPrimeDiscriminant` of an odd prime, that odd-prime map is injective on `t`, and the product
rewrites as a product of odd prime discriminants. Applied to both branches of the case split. -/
private theorem prod_oddPrimeDiscriminant_natAbs_of_not_isEvenPrimeDiscriminant {D : ι → ℤ}
    {t : Finset ι} (hD : ∀ i ∈ t, IsPrimeDiscriminant (D i))
    (hev : ∀ i ∈ t, ¬ IsEvenPrimeDiscriminant (D i)) (hDinj : Set.InjOn D t) :
    (∀ i ∈ t, ((D i).natAbs).Prime) ∧ (∀ i ∈ t, Odd (D i).natAbs) ∧
      Set.InjOn (fun i => (D i).natAbs) t ∧
      ∏ i ∈ t, D i = ∏ i ∈ t, oddPrimeDiscriminant (D i).natAbs := by
  have hrepr : ∀ i ∈ t, D i = oddPrimeDiscriminant (D i).natAbs := fun i hi =>
    (eq_oddPrimeDiscriminant_natAbs (hD i hi) (hev i hi)).2.2
  refine ⟨fun i hi => (eq_oddPrimeDiscriminant_natAbs (hD i hi) (hev i hi)).1,
    fun i hi => (eq_oddPrimeDiscriminant_natAbs (hD i hi) (hev i hi)).2.1, ?_,
    Finset.prod_congr rfl hrepr⟩
  intro i hi j hj hpij
  apply hDinj hi hj
  rw [hrepr i hi, hrepr j hj]
  exact congrArg oddPrimeDiscriminant hpij

/-- **A product of distinct prime discriminants with at most one even value is a fundamental
discriminant.** -/
theorem isFundamentalDiscr_prod {D : ι → ℤ} (hD : ∀ i ∈ s, IsPrimeDiscriminant (D i))
    (hDinj : Set.InjOn D s) (heven : ∀ i ∈ s, ∀ j ∈ s, IsEvenPrimeDiscriminant (D i) →
      IsEvenPrimeDiscriminant (D j) → D i = D j) :
    Int.IsFundamentalDiscr (∏ i ∈ s, D i) := by
  classical
  by_cases hev : ∃ i ∈ s, IsEvenPrimeDiscriminant (D i)
  · obtain ⟨i₀, hi₀, hev₀⟩ := hev
    have huniq : ∀ j ∈ s, IsEvenPrimeDiscriminant (D j) → j = i₀ := by
      intro j hj hevj
      exact hDinj hj hi₀ (heven j hj i₀ hi₀ hevj hev₀)
    have hoddset : ∀ j ∈ s.erase i₀, ¬ IsEvenPrimeDiscriminant (D j) := fun j hj hevj =>
      Finset.ne_of_mem_erase hj (huniq j (Finset.mem_of_mem_erase hj) hevj)
    obtain ⟨hpprime, hpodd, hpinj, hproderase⟩ :=
      prod_oddPrimeDiscriminant_natAbs_of_not_isEvenPrimeDiscriminant
        (fun j hj => hD j (Finset.mem_of_mem_erase hj)) hoddset
        (hDinj.mono (Finset.coe_subset.mpr (Finset.erase_subset i₀ s)))
    have hprod : ∏ i ∈ s, D i
        = D i₀ * ∏ i ∈ s.erase i₀, oddPrimeDiscriminant (D i).natAbs := by
      rw [← Finset.mul_prod_erase s D hi₀, hproderase]
    rw [hprod]
    exact isFundamentalDiscr_mul_prod_oddPrimeDiscriminant_of_isEvenPrimeDiscriminant
      (s := s.erase i₀) (p := fun i => (D i).natAbs) hev₀ hpprime hpodd hpinj
  · have hev' : ∀ j ∈ s, ¬ IsEvenPrimeDiscriminant (D j) := fun j hj hevj => hev ⟨j, hj, hevj⟩
    obtain ⟨hpprime, hpodd, hpinj, hprod⟩ :=
      prod_oddPrimeDiscriminant_natAbs_of_not_isEvenPrimeDiscriminant hD hev' hDinj
    rw [hprod]
    exact isFundamentalDiscr_prod_oddPrimeDiscriminant
      (p := fun i => (D i).natAbs) hpprime hpodd hpinj

/-- A product of pairwise coprime prime discriminants is a fundamental discriminant. -/
theorem isFundamentalDiscr_prod_of_pairwise_isCoprime {D : ι → ℤ}
    (hD : ∀ i ∈ s, IsPrimeDiscriminant (D i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) :
    Int.IsFundamentalDiscr (∏ i ∈ s, D i) := by
  apply isFundamentalDiscr_prod hD
  · intro i hi j hj hij
    by_contra hne
    exact (hD i hi).not_isUnit
      ((hcop i hi j hj hne).isUnit_of_dvd' dvd_rfl ⟨1, by rw [mul_one]; exact hij.symm⟩)
  · intro i hi j hj hevi hevj
    by_cases hij : i = j
    · exact congrArg D hij
    · have h2i : (2 : ℤ) ∣ D i := by rcases hevi with h | h | h <;> rw [h] <;> norm_num
      have h2j : (2 : ℤ) ∣ D j := by rcases hevj with h | h | h <;> rw [h] <;> norm_num
      have h2 : IsUnit (2 : ℤ) := (hcop i hi j hj hij).isUnit_of_dvd' h2i h2j
      simp [Int.isUnit_iff] at h2

end Products

end TauCeti.Multiquadratic
