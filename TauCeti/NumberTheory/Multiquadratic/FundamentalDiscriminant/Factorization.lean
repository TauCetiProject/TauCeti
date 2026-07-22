/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import Mathlib.Data.Int.NatAbs

/-!
# Prime-discriminant factorization of a fundamental discriminant

`FundamentalDiscriminant/Basic` supplies the *synthesis* half of the prime-discriminant/
fundamental-discriminant correspondence: a product of distinct prime discriminants with at most
one even value is a fundamental discriminant. This file supplies the **analysis** half, the
converse existence statement: every fundamental discriminant `D` is a product of a finite set of
prime discriminants, at most one of which is even.

This is the piece the genus-field layer needs to attach a *family* of prime discriminants to a
quadratic field `ℚ(√d)`: with the family in hand, the square-class independence and degree
theorems of `Multiquadratic/Prime/Discriminant/Independence.lean` present the genus field as a
multiquadratic field of degree `2ᵗ`.

The engine is `prod_oddPrimeDiscriminant_primeFactors_eq`: for an odd squarefree `x ≡ 1 (mod 4)`,
the product of the odd prime discriminants `p*` over the prime factors `p` of `x` is `x` itself.
The two sides share an absolute value (each `p*` has `|p*| = p`, and `x` is squarefree) and are
both `≡ 1 (mod 4)`, so they agree by sign uniqueness. The three shapes of a fundamental
discriminant — odd, `4 ·` odd, `8 ·` odd — then differ only in the single even prime discriminant
(`-4`, `-8`, `8`) prepended to that odd product.

## Main results

* `TauCeti.Multiquadratic.IsFundamentalDiscriminant.exists_finset_primeDiscriminant`: every
  fundamental discriminant is a product of a finite set of prime discriminants with at most one
  even value — the converse of `isFundamentalDiscriminant_prod`.
-/

public section

namespace TauCeti.Multiquadratic

open Finset

/-- Sign uniqueness modulo `4`: two integers with the same absolute value that are both
`≡ 1 (mod 4)` are equal (they cannot be negatives of each other). -/
private lemma eq_of_natAbs_eq_of_mod_four_eq_one {x y : ℤ} (h : x.natAbs = y.natAbs)
    (hx : x % 4 = 1) (hy : y % 4 = 1) : x = y := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with h1 | h1
  · exact h1
  · omega

/-- Every prime factor of an odd natural number is odd. -/
private lemma odd_of_mem_primeFactors_of_odd {n : ℕ} (hn : Odd n) {p : ℕ}
    (hp : p ∈ n.primeFactors) : Odd p := by
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd' with h2 | hodd
  · exact absurd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
      (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hn))
  · exact hodd

/-- **The odd prime discriminants recover the odd `≡ 1 (mod 4)` part.** For an odd squarefree
integer `x ≡ 1 (mod 4)`, the product of the odd prime discriminants `p*` over the prime factors
`p` of `x` equals `x`. -/
private lemma prod_oddPrimeDiscriminant_primeFactors_eq {x : ℤ} (hsf : Squarefree x)
    (hodd : Odd x) (hmod : x % 4 = 1) :
    ∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p = x := by
  have hoddn : Odd x.natAbs := Int.natAbs_odd.mpr hodd
  have hsfn : Squarefree x.natAbs := Int.squarefree_natAbs.mpr hsf
  have hnat : (∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p).natAbs = x.natAbs :=
    calc (∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p).natAbs
        = ∏ p ∈ x.natAbs.primeFactors, (oddPrimeDiscriminant p).natAbs :=
          map_prod Int.natAbsHom _ _
      _ = ∏ p ∈ x.natAbs.primeFactors, p :=
          Finset.prod_congr rfl fun p _ => oddPrimeDiscriminant_natAbs p
      _ = x.natAbs := Nat.prod_primeFactors_of_squarefree hsfn
  have hmod4 : (∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p) % 4 = 1 :=
    prod_oddPrimeDiscriminant_mod_four_eq_one
      (fun p hp => odd_of_mem_primeFactors_of_odd hoddn hp)
  exact eq_of_natAbs_eq_of_mod_four_eq_one hnat hmod4 hmod

/-- The image family `{p* : p ∣ n}` of odd prime discriminants over the prime factors of an odd
`n`: each member is a non-even prime discriminant, and the assignment is injective, so its `Finset`
product is the indexed product over the prime factors. -/
private lemma oddPrimeDiscriminant_image_prod {n : ℕ} (hn : Odd n) :
    (∀ P ∈ n.primeFactors.image oddPrimeDiscriminant, IsPrimeDiscriminant P ∧
        ¬ IsEvenPrimeDiscriminant P) ∧
      ∏ P ∈ n.primeFactors.image oddPrimeDiscriminant, P =
        ∏ p ∈ n.primeFactors, oddPrimeDiscriminant p := by
  refine ⟨fun P hP => ?_, ?_⟩
  · rw [Finset.mem_image] at hP
    obtain ⟨p, hp, rfl⟩ := hP
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpo := odd_of_mem_primeFactors_of_odd hn hp
    exact ⟨isPrimeDiscriminant_oddPrimeDiscriminant hpp hpo,
      not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hpo⟩
  · refine Finset.prod_image fun p _ q _ h => ?_
    have : (oddPrimeDiscriminant p).natAbs = (oddPrimeDiscriminant q).natAbs := by rw [h]
    simpa only [oddPrimeDiscriminant_natAbs] using this

/-- **Analysis half of the prime-discriminant correspondence.** Every fundamental discriminant
`D` is a product of a finite set of prime discriminants, at most one of which is even. This is the
converse of `TauCeti.Multiquadratic.isFundamentalDiscriminant_prod`. -/
theorem IsFundamentalDiscriminant.exists_finset_primeDiscriminant {D : ℤ}
    (hD : IsFundamentalDiscriminant D) :
    ∃ s : Finset ℤ, (∀ P ∈ s, IsPrimeDiscriminant P) ∧
      (∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) ∧
      ∏ P ∈ s, P = D := by
  rcases hD.mod_four_eq_zero_or_one with h0 | h1
  · -- `D = 4 * m`, `m` squarefree, `m ≡ 2` or `3 (mod 4)`.
    have hsf : Squarefree (D / 4) := hD.squarefree_div_four h0
    have hmm : D / 4 % 4 = 2 ∨ D / 4 % 4 = 3 := hD.div_four_mod_four_eq_two_or_three h0
    have hDm : D = 4 * (D / 4) := by omega
    set m := D / 4 with hm
    rcases hmm with hm2 | hm3
    · -- `m ≡ 2 (mod 4)`: write `m = 2 * k` with `k` odd; the even factor is `±8`.
      have hk2 : m = 2 * (m / 2) := by omega
      set k := m / 2 with hk
      have hkodd : Odd k := Int.odd_iff.mpr (by omega)
      have hksf : Squarefree k := hsf.squarefree_of_dvd ⟨2, by omega⟩
      have hD8 : D = 8 * k := by omega
      obtain ⟨himg, hprodimg⟩ := oddPrimeDiscriminant_image_prod (Int.natAbs_odd.mpr hkodd)
      rcases (by omega : k % 4 = 1 ∨ k % 4 = 3) with hk1 | hk3
      · -- `k ≡ 1 (mod 4)`: even factor `8`; the odd product is `k`.
        have hcore : ∏ p ∈ k.natAbs.primeFactors, oddPrimeDiscriminant p = k :=
          prod_oddPrimeDiscriminant_primeFactors_eq hksf hkodd hk1
        refine ⟨insert 8 (k.natAbs.primeFactors.image oddPrimeDiscriminant), ?_, ?_, ?_⟩
        · intro P hP
          rcases Finset.mem_insert.mp hP with rfl | hP
          · exact isPrimeDiscriminant_eight
          · exact (himg P hP).1
        · intro P hP Q hQ hPe hQe
          rcases Finset.mem_insert.mp hP with rfl | hP <;>
            rcases Finset.mem_insert.mp hQ with rfl | hQ
          · rfl
          · exact absurd hQe (himg Q hQ).2
          · exact absurd hPe (himg P hP).2
          · exact absurd hPe (himg P hP).2
        · have hne : (8 : ℤ) ∉ k.natAbs.primeFactors.image oddPrimeDiscriminant :=
            fun hmem => (himg _ hmem).2 (by simp)
          rw [Finset.prod_insert hne, hprodimg, hcore]; omega
      · -- `k ≡ 3 (mod 4)`: even factor `-8`; the odd product is `-k`.
        have hcore : ∏ p ∈ (-k).natAbs.primeFactors, oddPrimeDiscriminant p = -k :=
          prod_oddPrimeDiscriminant_primeFactors_eq hksf.neg hkodd.neg (by omega)
        have hnatabs : (-k).natAbs = k.natAbs := Int.natAbs_neg k
        rw [hnatabs] at hcore
        refine ⟨insert (-8) (k.natAbs.primeFactors.image oddPrimeDiscriminant), ?_, ?_, ?_⟩
        · intro P hP
          rcases Finset.mem_insert.mp hP with rfl | hP
          · exact isPrimeDiscriminant_neg_eight
          · exact (himg P hP).1
        · intro P hP Q hQ hPe hQe
          rcases Finset.mem_insert.mp hP with rfl | hP <;>
            rcases Finset.mem_insert.mp hQ with rfl | hQ
          · rfl
          · exact absurd hQe (himg Q hQ).2
          · exact absurd hPe (himg P hP).2
          · exact absurd hPe (himg P hP).2
        · have hne : (-8 : ℤ) ∉ k.natAbs.primeFactors.image oddPrimeDiscriminant :=
            fun hmem => (himg _ hmem).2 (by simp)
          rw [Finset.prod_insert hne, hprodimg, hcore]; omega
    · -- `m ≡ 3 (mod 4)`, `m` odd: even factor `-4`; the odd product is `-m`.
      have hmodd : Odd m := Int.odd_iff.mpr (by omega)
      obtain ⟨himg, hprodimg⟩ := oddPrimeDiscriminant_image_prod (Int.natAbs_odd.mpr hmodd)
      have hcore : ∏ p ∈ (-m).natAbs.primeFactors, oddPrimeDiscriminant p = -m :=
        prod_oddPrimeDiscriminant_primeFactors_eq hsf.neg hmodd.neg (by omega)
      have hnatabs : (-m).natAbs = m.natAbs := Int.natAbs_neg m
      rw [hnatabs] at hcore
      refine ⟨insert (-4) (m.natAbs.primeFactors.image oddPrimeDiscriminant), ?_, ?_, ?_⟩
      · intro P hP
        rcases Finset.mem_insert.mp hP with rfl | hP
        · exact isPrimeDiscriminant_neg_four
        · exact (himg P hP).1
      · intro P hP Q hQ hPe hQe
        rcases Finset.mem_insert.mp hP with rfl | hP <;>
          rcases Finset.mem_insert.mp hQ with rfl | hQ
        · rfl
        · exact absurd hQe (himg Q hQ).2
        · exact absurd hPe (himg P hP).2
        · exact absurd hPe (himg P hP).2
      · have hne : (-4 : ℤ) ∉ m.natAbs.primeFactors.image oddPrimeDiscriminant :=
          fun hmem => (himg _ hmem).2 (by simp)
        rw [Finset.prod_insert hne, hprodimg, hcore]; omega
  · -- `D ≡ 1 (mod 4)`, `D` odd squarefree: no even factor.
    have hsf : Squarefree D := hD.squarefree_of_mod_four_eq_one h1
    have hodd : Odd D := Int.odd_iff.mpr (by omega)
    obtain ⟨himg, hprodimg⟩ := oddPrimeDiscriminant_image_prod (Int.natAbs_odd.mpr hodd)
    refine ⟨D.natAbs.primeFactors.image oddPrimeDiscriminant, fun P hP => (himg P hP).1, ?_, ?_⟩
    · intro P hP Q _ hPe _
      exact absurd hPe (himg P hP).2
    · rw [hprodimg]
      exact prod_oddPrimeDiscriminant_primeFactors_eq hsf hodd h1

end TauCeti.Multiquadratic
