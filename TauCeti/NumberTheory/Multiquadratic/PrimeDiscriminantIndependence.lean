/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Degree
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminants
public import Mathlib.Data.Int.NatAbs
public import Mathlib.RingTheory.Int.Basic

/-!
# Square-class independence of prime discriminants

The genus-field layer of the multiquadratic roadmap builds the genus field of `ℚ(√d)` as the
compositum of the quadratic fields `ℚ(√D*)` over the **prime discriminants** `D*` dividing the
discriminant of `ℚ(√d)`. To know this compositum is multiquadratic of full degree `2ᵗ` (and so
to apply the degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range`), one needs the prime
discriminants to be **square-class independent**: no nonempty subset product of their radicands
is a rational square.

This file supplies that independence. The discriminant of a quadratic field is a *fundamental*
discriminant, whose prime-discriminant factorization contains at most one even factor (one of
`-4`, `8`, `-8`); so the relevant hypothesis is that the family of prime discriminants is
injective and has **at most one even** member. The radicands are then pairwise coprime — their
absolute values are `1`, `2`, and distinct odd primes — and a nonempty subset product is a
squarefree integer different from `1`, hence not a square.

## Main results

* `TauCeti.Multiquadratic.isCoprime_primeDiscriminantRadicand`: the radicands of two distinct
  prime discriminants, not both even, are coprime.
* `TauCeti.Multiquadratic.not_isSquare_prod_primeDiscriminantRadicands`: for an injective family
  of prime discriminants with at most one even member, no nonempty subset product of their
  radicands is a rational square — square-class independence in the form the degree theorem
  consumes.
* `TauCeti.Multiquadratic.finrank_adjoin_primeDiscriminantRadicands`: the multiquadratic
  compositum of the `√(radicand D i)` over such a family has degree `2^|ι|` — the genus field is
  multiquadratic of full degree.
-/

public section

open scoped Function

namespace TauCeti.Multiquadratic

/-- A squarefree integer other than `1` is not a rational square. If `(n : ℚ)` were a square then
`n = a * a` for some integer `a`; squarefreeness forces `a` to be a unit, so `n = 1`. -/
private theorem not_isSquare_intCast_of_squarefree_of_ne_one {n : ℤ}
    (hsf : Squarefree n) (hne : n ≠ 1) : ¬ IsSquare ((n : ℤ) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨a, ha⟩
  have hu : IsUnit a := hsf a (ha ▸ dvd_rfl)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp_all

/-- If the radicand of a prime discriminant has absolute value `1`, the discriminant is `-4`.
The odd prime discriminants have radicand of absolute value their underlying prime `≥ 2`, and the
even radicands `-1`, `2`, `-2` have absolute value `1` only in the `-4` case. -/
theorem eq_neg_four_of_primeDiscriminantRadicand_natAbs_eq_one {D : ℤ}
    (hD : IsPrimeDiscriminant D) (h : (primeDiscriminantRadicand D).natAbs = 1) :
    D = -4 := by
  rcases isPrimeDiscriminant_iff.mp hD with hev | ⟨p, hp, hpodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hev] at h
    rcases evenPrimeDiscriminantRadicand_eq_neg_one_or_eq_two_or_eq_neg_two hev with h1 | h2 | h3
    · exact (evenPrimeDiscriminantRadicand_eq_neg_one_iff hev).mp h1
    · rw [h2] at h; exact absurd h (by decide)
    · rw [h3] at h; exact absurd h (by decide)
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd, oddPrimeDiscriminant_natAbs] at h
    exact absurd h hp.ne_one

/-- **Coprimality of distinct prime-discriminant radicands.** The radicands of two distinct prime
discriminants that are not both even are coprime. Their absolute values are `1`, `2` (the even
radicands), or distinct odd primes (the odd ones), which are pairwise coprime. -/
theorem isCoprime_primeDiscriminantRadicand {D E : ℤ}
    (hD : IsPrimeDiscriminant D) (hE : IsPrimeDiscriminant E) (hDE : D ≠ E)
    (hnot : ¬ (IsEvenPrimeDiscriminant D ∧ IsEvenPrimeDiscriminant E)) :
    IsCoprime (primeDiscriminantRadicand D) (primeDiscriminantRadicand E) := by
  rw [Int.isCoprime_iff_nat_coprime]
  rcases isPrimeDiscriminant_iff.mp hD with hevD | ⟨p, hp, hpodd, rfl⟩
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · exact absurd ⟨hevD, hevE⟩ hnot
    · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevD,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd, oddPrimeDiscriminant_natAbs]
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevD with h1 | h2
      · rw [h1]; exact Nat.coprime_one_left q
      · rw [h2]; exact Nat.coprime_two_left.mpr hqodd
  · rcases isPrimeDiscriminant_iff.mp hE with hevE | ⟨q, hq, hqodd, rfl⟩
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd, oddPrimeDiscriminant_natAbs,
        primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hevE]
      rcases evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two hevE with h1 | h2
      · rw [h1]; exact Nat.coprime_one_right p
      · rw [h2]; exact Nat.coprime_two_right.mpr hpodd
    · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hpodd,
        primeDiscriminantRadicand_oddPrimeDiscriminant hqodd, oddPrimeDiscriminant_natAbs,
        oddPrimeDiscriminant_natAbs]
      exact (Nat.coprime_primes hp hq).mpr fun h => hDE (by rw [h])

/-- **Square-class independence of prime discriminants.** Let `D : ι → ℤ` be an injective family
of prime discriminants with at most one even member (the shape of the prime-discriminant
factorization of a fundamental discriminant). Then no nonempty subset product of the radicands
`primeDiscriminantRadicand (D i)` is a rational square. This is the `hindep` hypothesis the
multiquadratic degree theorem `finrank_adjoin_range` consumes, applied to the genus-field
generators. -/
theorem not_isSquare_prod_primeDiscriminantRadicands {ι : Type*} (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → i = j) :
    ∀ S : Finset ι, S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
  intro S hS
  rw [← Int.cast_prod]
  refine not_isSquare_intCast_of_squarefree_of_ne_one ?_ ?_
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => ?_)
      (fun i _ => squarefree_primeDiscriminantRadicand (hD i))
    exact (isCoprime_primeDiscriminantRadicand (hD i) (hD j) (fun h => hij (hinj h))
      (fun h => hij (heven i j h.1 h.2))).isRelPrime
  · intro hP
    have hnp := map_prod Int.natAbsHom (fun i => primeDiscriminantRadicand (D i)) S
    simp only [Int.natAbsHom_apply] at hnp
    have habs : ∏ i ∈ S, (primeDiscriminantRadicand (D i)).natAbs = 1 := by
      rw [← hnp, hP, Int.natAbs_one]
    have hall : ∀ i ∈ S, (primeDiscriminantRadicand (D i)).natAbs = 1 :=
      (Finset.prod_eq_one_iff).mp habs
    have hallD : ∀ i ∈ S, D i = -4 := fun i hi =>
      eq_neg_four_of_primeDiscriminantRadicand_natAbs_eq_one (hD i) (hall i hi)
    obtain ⟨i₀, hi₀⟩ := hS
    have hsingle : S = {i₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hi₀, fun x hx => hinj (by rw [hallD x hx, hallD i₀ hi₀])⟩
    rw [hsingle, Finset.prod_singleton, hallD i₀ hi₀, primeDiscriminantRadicand_neg_four] at hP
    exact absurd hP (by decide)

/-- **The genus field is multiquadratic of full degree.** Over any field `L ⊇ ℚ` carrying square
roots `root i` of the radicands of an injective family of prime discriminants with at most one
even member, the compositum `ℚ(root i : i)` has degree `2^|ι|`. Specialised to the prime
discriminants dividing a fundamental discriminant, this says the genus field is multiquadratic
of full degree. It is the prime-discriminant instance of `finrank_adjoin_range`, fed the
square-class independence `not_isSquare_prod_primeDiscriminantRadicands`. -/
theorem finrank_adjoin_primeDiscriminantRadicands {ι : Type*} [Finite ι]
    {L : Type*} [Field L] [Algebra ℚ L] (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → i = j)
    (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
  finrank_adjoin_range hroot
    (not_isSquare_prod_primeDiscriminantRadicands D hD hinj heven)

/-- **Worked example.** The prime discriminants `-4` and `5` divide the discriminant `-20` of
`ℚ(√-5)`, and are its genus-field generators (`ℚ(√-5)` has genus field `ℚ(√-1, √5)`). They are
square-class independent: no nonempty subset product of their radicands `-1` and `5` is a
rational square. -/
example : ∀ S : Finset (Fin 2), S.Nonempty →
    ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (![(-4 : ℤ), 5] i) : ℤ) : ℚ)) := by
  refine not_isSquare_prod_primeDiscriminantRadicands _ (fun i => ?_) (fun a b h => ?_)
    (fun i j hi hj => ?_)
  · fin_cases i
    · simp
    · have h5 : IsPrimeDiscriminant (5 : ℤ) := by
        rw [show (5 : ℤ) = oddPrimeDiscriminant 5 from
          (oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num)).symm]
        exact isPrimeDiscriminant_oddPrimeDiscriminant (by decide) (by decide)
      simpa using h5
  · fin_cases a <;> fin_cases b <;> simp_all
  · fin_cases i <;> fin_cases j <;> simp_all [IsEvenPrimeDiscriminant]

end TauCeti.Multiquadratic
