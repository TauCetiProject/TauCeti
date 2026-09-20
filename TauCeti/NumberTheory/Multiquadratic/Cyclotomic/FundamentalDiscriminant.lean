/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Basic
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.GaussSum
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
public import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification

/-!
# A quadratic field lies in the cyclotomic field of its discriminant

Let `D` be a fundamental discriminant. The quadratic field `ℚ(√D)` lies in the cyclotomic field
`ℚ(ζ_|D|)`: inside any field `L` of characteristic zero, an intermediate field of `L / ℚ` holding a
primitive `N`-th root of unity with `|D| ∣ N` contains both square roots of `D`. For a squarefree
integer `d` this says `ℚ(√d) ⊆ ℚ(ζ_|D|)` with `D = fundamentalDiscriminant d`, which is `d` or
`4d`. The same level carries the whole genus field: the compositum of the quadratic fields of the
prime discriminants dividing `D` also lies in `ℚ(ζ_|D|)`.

This sharpens `TauCeti.Multiquadratic.mem_of_sq_eq_intCast`, which asks for the order `4 |m|`
for a square root of an integer `m`. That order is never needed for a fundamental discriminant:
`√-3` already lies in `ℚ(ζ₃)` and `√5` in `ℚ(ζ₅)`, where the cruder bound asks for `ζ₁₂` and
`ζ₂₀`. Classically `|D|` is the conductor of `ℚ(√D)`, the least such level; this file proves the
containment only, not the minimality.

The proof is factor by factor. A fundamental discriminant is a product of prime discriminants
(`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`), each of which divides it. An odd
prime discriminant `p*` has a square root in `ℚ(ζ_p)`, namely a quadratic Gauss sum
(`exists_mem_sq_eq_oddPrimeDiscriminant`); the even prime discriminants `-4`, `8`, `-8` have
square roots in `ℚ(ζ₄)` and `ℚ(ζ₈)` (`exists_mem_sq_eq_neg_one`, `exists_mem_sq_eq_two`,
`exists_mem_sq_eq_neg_two`). Multiplying these square roots together gives one of `D`.

For the classical account see K. Ireland and M. Rosen, *A Classical Introduction to Modern Number
Theory*, Chapter 6, and D. A. Cox, *Primes of the Form x² + ny²*, §6.A.

## Main results

* `TauCeti.Multiquadratic.mem_of_sq_eq_primeDiscriminantRadicand`: the square roots of the radicand
  of a prime discriminant `P` lie in any field holding a primitive `N`-th root of unity with
  `|P| ∣ N`.
* `TauCeti.Multiquadratic.mem_of_sq_eq_of_isFundamentalDiscriminant`: the square roots of a
  fundamental discriminant `D` lie in any field holding a primitive `N`-th root of unity with
  `|D| ∣ N`.
* `TauCeti.Multiquadratic.mem_of_sq_eq_of_squarefree`: the square roots of a squarefree integer
  `d` lie in any such field with `|fundamentalDiscriminant d| ∣ N`.
* `TauCeti.Multiquadratic.candidateGenusField_le_of_isPrimitiveRoot`: the same containment for the
  prime-discriminant compositum `candidateGenusField`.
* `TauCeti.Multiquadratic.adjoin_simple_le_adjoin_exp_of_isFundamentalDiscriminant` and
  `TauCeti.Multiquadratic.candidateGenusField_le_adjoin_exp`: over `ℂ`, the quadratic field and
  the prime-discriminant compositum lie in `ℚ(exp (2πi / |D|))`.
* `TauCeti.Multiquadratic.prime_dvd_level_of_dvd_fundamentalDiscriminant`: every prime factor of
  the fundamental discriminant divides the level of any cyclotomic field containing its square
  root.
* `TauCeti.Multiquadratic.prod_primeFactors_fundamentalDiscriminant_dvd_level`: equivalently, the
  product of the distinct prime factors of the fundamental discriminant divides the level.
* `TauCeti.Multiquadratic.natAbs_dvd_level_of_squarefree`: the squarefree radicand itself divides
  every cyclotomic level containing its square root.
* `TauCeti.Multiquadratic.natAbs_dvd_level_of_isFundamentalDiscriminant_of_odd`: an odd
  fundamental discriminant divides every cyclotomic level containing its square root.
* `TauCeti.Multiquadratic.fundamentalDiscriminant_natAbs_dvd_level_of_mod_four_eq_three`: the same
  conductor-minimality statement when the radicand is `3` modulo `4`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {L : Type*} [Field L] [CharZero L] {F : IntermediateField ℚ L} {ζ : L} {N : ℕ}

/-- **A root of unity of order divisible by `|P|` carries a square root of the radicand of the
prime discriminant `P`.** The radicands of `-4`, `8`, `-8` are `-1`, `2`, `-2`, whose square roots
come from a primitive fourth or eighth root of unity; the radicand of an odd prime discriminant
`p*` is `p*` itself, whose square root is a Gauss sum over a primitive `p`-th root of unity. -/
theorem exists_mem_sq_eq_primeDiscriminantRadicand (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {P : ℤ} (hP : IsPrimeDiscriminant P) (hdvd : P.natAbs ∣ N) :
    ∃ x ∈ F, x ^ 2 = (primeDiscriminantRadicand P : L) := by
  rcases isPrimeDiscriminant_iff.mp hP with hE | ⟨p, hp, hodd, rfl⟩
  · rcases isEvenPrimeDiscriminant_iff.mp hE with rfl | rfl | rfl
    · have h4 : 4 ∣ N := by simpa using hdvd
      obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_neg_one
        (hζ.pow hN (Nat.div_mul_cancel h4).symm) (pow_mem hmem _)
      exact ⟨x, hxF, by rw [hx, primeDiscriminantRadicand_neg_four]; push_cast; ring⟩
    · have h8 : 8 ∣ N := by simpa using hdvd
      obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_two
        (hζ.pow hN (Nat.div_mul_cancel h8).symm) (pow_mem hmem _)
      exact ⟨x, hxF, by rw [hx, primeDiscriminantRadicand_eight]; push_cast; ring⟩
    · have h8 : 8 ∣ N := by simpa using hdvd
      obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_neg_two
        (hζ.pow hN (Nat.div_mul_cancel h8).symm) (pow_mem hmem _)
      exact ⟨x, hxF, by rw [hx, primeDiscriminantRadicand_neg_eight]; push_cast; ring⟩
  · have hpN : p ∣ N := by simpa using hdvd
    rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    exact exists_mem_sq_eq_oddPrimeDiscriminant hp (hodd.ne_two_of_dvd_nat dvd_rfl)
      (hζ.pow hN (Nat.div_mul_cancel hpN).symm) (pow_mem hmem _)

/-- **Every square root of the radicand of a prime discriminant `P` lies in a field of roots of
unity of order divisible by `|P|`.** -/
theorem mem_of_sq_eq_primeDiscriminantRadicand (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {P : ℤ} (hP : IsPrimeDiscriminant P) (hdvd : P.natAbs ∣ N) {x : L}
    (hx : x ^ 2 = (primeDiscriminantRadicand P : L)) : x ∈ F := by
  obtain ⟨y, hyF, hy⟩ := exists_mem_sq_eq_primeDiscriminantRadicand hN hζ hmem hP hdvd
  rcases eq_or_eq_neg_of_sq_eq_sq x y (hx.trans hy.symm) with rfl | rfl
  exacts [hyF, neg_mem hyF]

/-- **A root of unity of order divisible by `|P|` carries a square root of the prime discriminant
`P`.** The prime discriminant is its radicand, or four times its radicand in the even cases. -/
theorem exists_mem_sq_eq_of_isPrimeDiscriminant (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {P : ℤ} (hP : IsPrimeDiscriminant P) (hdvd : P.natAbs ∣ N) :
    ∃ x ∈ F, x ^ 2 = (P : L) := by
  obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_primeDiscriminantRadicand hN hζ hmem hP hdvd
  rcases primeDiscriminant_eq_radicand_or_eq_four_mul_radicand hP with h | h
  · exact ⟨x, hxF, by rw [hx, ← h]⟩
  · refine ⟨2 * x, mul_mem (ofNat_mem F 2) hxF, ?_⟩
    rw [mul_pow, hx]
    conv_rhs => rw [h]
    push_cast
    ring

/-- **A root of unity of order divisible by `|D|` carries a square root of the fundamental
discriminant `D`.** The square roots of the prime-discriminant factors of `D` multiply together;
each factor divides `D`, so its absolute value divides the order. -/
theorem exists_mem_sq_eq_of_isFundamentalDiscriminant (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {D : ℤ} (hD : IsFundamentalDiscriminant D) (hdvd : D.natAbs ∣ N) :
    ∃ x ∈ F, x ^ 2 = (D : L) := by
  obtain ⟨s, hs, -, rfl⟩ := hD.exists_finset_primeDiscriminant
  obtain ⟨r, hr⟩ : IsSquare (∏ P ∈ s, (P : F)) := Finset.isSquare_prod _ fun P hP => by
    obtain ⟨x, hxF, hx⟩ := exists_mem_sq_eq_of_isPrimeDiscriminant hN hζ hmem (hs P hP)
      ((Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem _ hP)).trans hdvd)
    exact ⟨⟨x, hxF⟩, Subtype.ext (by simp [← sq, hx])⟩
  exact ⟨r, r.2, by simpa [sq] using congrArg ((↑) : F → L) hr.symm⟩

/-- **Every square root of a fundamental discriminant `D` lies in a field of roots of unity of order
divisible by `|D|`.** In particular `ℚ(√D) ⊆ ℚ(ζ_|D|)`. -/
theorem mem_of_sq_eq_of_isFundamentalDiscriminant (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (hmem : ζ ∈ F) {D : ℤ} (hD : IsFundamentalDiscriminant D) (hdvd : D.natAbs ∣ N) {x : L}
    (hx : x ^ 2 = (D : L)) : x ∈ F := by
  obtain ⟨y, hyF, hy⟩ := exists_mem_sq_eq_of_isFundamentalDiscriminant hN hζ hmem hD hdvd
  rcases eq_or_eq_neg_of_sq_eq_sq x y (hx.trans hy.symm) with rfl | rfl
  exacts [hyF, neg_mem hyF]

/-- **Every square root of a squarefree integer `d` lies in a field of roots of unity of order
divisible by the absolute value of its fundamental discriminant.** Since
`fundamentalDiscriminant d = c² d` with `c ∈ {1, 2}`, a square root `x` of `d` gives the square
root `c x` of the fundamental discriminant. -/
theorem mem_of_sq_eq_of_squarefree (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F)
    {d : ℤ} (hd : Squarefree d) (hdvd : (fundamentalDiscriminant d).natAbs ∣ N) {x : L}
    (hx : x ^ 2 = (d : L)) : x ∈ F := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  have hc0 : (c : L) ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have hcx : c * x ∈ F := mem_of_sq_eq_of_isFundamentalDiscriminant hN hζ hmem
    (isFundamentalDiscriminant_fundamentalDiscriminant hd) hdvd
    (by rw [← hcd, mul_pow, hx]; push_cast; ring)
  have hxeq : x = c * x / c := by field_simp
  rw [hxeq]
  exact div_mem hcx (intCast_mem F c)

/-- **The candidate genus field of `ℚ(√d)` lies in any field of roots of unity of order divisible
by the absolute value of the fundamental discriminant of `d`.** Each of its generators is a square
root of the radicand of a prime discriminant dividing `fundamentalDiscriminant d`. -/
theorem candidateGenusField_le_of_isPrimitiveRoot {d : ℤ} (hd : Squarefree d)
    {F : IntermediateField ℚ ℂ} {ζ : ℂ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hmem : ζ ∈ F)
    (hdvd : (fundamentalDiscriminant d).natAbs ∣ N) : candidateGenusField hd ≤ F := by
  obtain ⟨hs, -, hprod⟩ := genusPrimeDiscriminants_spec hd
  rw [candidateGenusField_le_iff]
  intro P
  refine mem_of_sq_eq_primeDiscriminantRadicand hN hζ hmem (hs P.1 P.2) ?_ (genusFieldRoot_sq hd P)
  rw [← hprod] at hdvd
  exact (Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem _ P.2)).trans hdvd

/-! ### Over `ℂ`: the cyclotomic field `ℚ(exp (2πi / |D|))` -/

/-- **A quadratic field lies in the cyclotomic field of its discriminant.** For a fundamental
discriminant `D` and a complex square root `x` of `D`, `ℚ(x) ⊆ ℚ(exp (2πi / |D|))`. -/
theorem adjoin_simple_le_adjoin_exp_of_isFundamentalDiscriminant {D : ℤ}
    (hD : IsFundamentalDiscriminant D) {x : ℂ} (hx : x ^ 2 = (D : ℂ)) :
    ℚ⟮x⟯ ≤ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / (D.natAbs : ℂ))⟯ := by
  have hN : 0 < D.natAbs := Int.natAbs_pos.mpr hD.ne_zero
  rw [adjoin_simple_le_iff]
  exact mem_of_sq_eq_of_isFundamentalDiscriminant hN (Complex.isPrimitiveRoot_exp _ hN.ne')
    (mem_adjoin_simple_self ℚ _) hD dvd_rfl hx

/-- **The candidate genus field of `ℚ(√d)` lies in the cyclotomic field of the discriminant.** For
squarefree `d` with fundamental discriminant `D`, the compositum of the quadratic fields of the
prime discriminants dividing `D` is contained in `ℚ(exp (2πi / |D|))`. -/
theorem candidateGenusField_le_adjoin_exp {d : ℤ} (hd : Squarefree d) :
    candidateGenusField hd ≤
      ℚ⟮Complex.exp (2 * Real.pi * Complex.I / ((fundamentalDiscriminant d).natAbs : ℂ))⟯ := by
  have hN : 0 < (fundamentalDiscriminant d).natAbs :=
    Int.natAbs_pos.mpr (fundamentalDiscriminant_ne_zero hd.ne_zero)
  exact candidateGenusField_le_of_isPrimitiveRoot hd hN (Complex.isPrimitiveRoot_exp _ hN.ne')
    (mem_adjoin_simple_self ℚ _) dvd_rfl

/-! ### The necessary prime divisors of a cyclotomic level -/

/-- **Every prime factor of a quadratic discriminant divides any cyclotomic level containing the
quadratic field.** Let `d` be squarefree and let `x ∈ M` satisfy `x² = d`, where `M` is an
`N`-th cyclotomic extension of `ℚ`. If a rational prime `p` divides
`fundamentalDiscriminant d`, then `p ∣ N`.

Thus the squarefree kernel of `|fundamentalDiscriminant d|` divides every possible cyclotomic
level. Together with `mem_of_sq_eq_of_squarefree`, this gives the prime-by-prime part of the
classical assertion that the conductor of `ℚ(√d)` is `|fundamentalDiscriminant d|`; determining
the full power of `2` in the conductor requires a finer ramification argument. -/
theorem prime_dvd_level_of_dvd_fundamentalDiscriminant {M : Type*} [Field M] [NumberField M]
    {N : ℕ} [IsCyclotomicExtension {N} ℚ M] {d : ℤ} (hd : Squarefree d) {x : M}
    (hx : x ^ 2 = (d : M)) {p : ℕ} (hp : p.Prime)
    (hpd : (p : ℤ) ∣ fundamentalDiscriminant d) : p ∣ N := by
  apply IsCyclotomicExtension.dvd_level_of_mem_ramifiedPrimes M N (adjoin ℚ {x})
  exact (mem_ramifiedPrimes_adjoin_iff_dvd_fundamentalDiscriminant hd hx hp).mpr hpd

/-- **The squarefree kernel of a quadratic discriminant divides any cyclotomic level containing
the quadratic field.** Under the hypotheses of
`prime_dvd_level_of_dvd_fundamentalDiscriminant`, the product of the distinct prime divisors of
`|fundamentalDiscriminant d|` divides `N`.

For odd fundamental discriminants this product is the whole absolute discriminant. At the prime
`2` it records only one factor of `2`; the results below recover exponent `2` when the radicand is
`3` modulo `4`, while exponent `3` for radicands `2` modulo `4` remains a finer local step. -/
theorem prod_primeFactors_fundamentalDiscriminant_dvd_level {M : Type*} [Field M] [NumberField M]
    {N : ℕ} [IsCyclotomicExtension {N} ℚ M] {d : ℤ} (hd : Squarefree d) {x : M}
    (hx : x ^ 2 = (d : M)) :
    ∏ p ∈ (fundamentalDiscriminant d).natAbs.primeFactors, p ∣ N := by
  by_cases hN : N = 0
  · simp [hN]
  rw [Nat.prod_primeFactors_dvd_iff hN]
  intro p hp
  rw [Nat.mem_primeFactors_of_ne_zero hN]
  refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
  apply prime_dvd_level_of_dvd_fundamentalDiscriminant hd hx
    (Nat.prime_of_mem_primeFactors hp)
  apply Int.natAbs_dvd_natAbs.mp
  simpa using Nat.dvd_of_mem_primeFactors hp

/-- **A squarefree radicand divides every cyclotomic level containing its square root.** If `d`
is squarefree and an `N`-th cyclotomic extension of `ℚ` contains a square root of `d`, then
`|d| ∣ N`.

Every prime factor of `d` divides `fundamentalDiscriminant d`, hence divides `N` by
`prime_dvd_level_of_dvd_fundamentalDiscriminant`; squarefreeness then reassembles the prime
factors into `|d|`. -/
theorem natAbs_dvd_level_of_squarefree {M : Type*} [Field M] [NumberField M]
    {N : ℕ} [IsCyclotomicExtension {N} ℚ M] {d : ℤ} (hd : Squarefree d) {x : M}
    (hx : x ^ 2 = (d : M)) : d.natAbs ∣ N := by
  rw [← Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hd)]
  by_cases hN : N = 0
  · simp [hN]
  rw [Nat.prod_primeFactors_dvd_iff hN]
  intro p hp
  rw [Nat.mem_primeFactors_of_ne_zero hN]
  have hpprime := Nat.prime_of_mem_primeFactors hp
  refine ⟨hpprime, prime_dvd_level_of_dvd_fundamentalDiscriminant hd hx hpprime ?_⟩
  obtain ⟨c, -, hc⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  rw [← hc]
  apply dvd_mul_of_dvd_right
  apply Int.natAbs_dvd_natAbs.mp
  simpa using Nat.dvd_of_mem_primeFactors hp

/-- **An odd quadratic discriminant divides every cyclotomic level containing its quadratic
field.** Let `D` be an odd fundamental discriminant and suppose that the `N`-th cyclotomic field
contains a square root of `D`. Then `|D| ∣ N`.

Combined with `mem_of_sq_eq_of_isFundamentalDiscriminant`, which puts the square roots of `D` in
every level divisible by `|D|`, this proves that `|D|` is the least cyclotomic level for the odd
fundamental-discriminant case. -/
theorem natAbs_dvd_level_of_isFundamentalDiscriminant_of_odd {M : Type*} [Field M]
    [NumberField M] {N : ℕ} [IsCyclotomicExtension {N} ℚ M] {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hodd : Odd D) {x : M} (hx : x ^ 2 = (D : M)) :
    D.natAbs ∣ N := by
  have hmod : D % 4 = 1 := by
    rw [Int.odd_iff] at hodd
    rcases hD.mod_four_eq_zero_or_one with h | h
    · omega
    · exact h
  have hsf : Squarefree D := hD.squarefree_of_mod_four_eq_one hmod
  exact natAbs_dvd_level_of_squarefree (N := N) hsf hx

/-- **The conductor level is necessary when the squarefree radicand is `3` modulo `4`.** Let `d`
be squarefree with `d ≡ 3 (mod 4)`. If an `N`-th cyclotomic extension of `ℚ` contains a square
root of `d`, then `|fundamentalDiscriminant d| = 4 |d|` divides `N`.

The odd factor `|d|` divides `N` by `natAbs_dvd_level_of_squarefree`. The prime `2` ramifies in
`ℚ(√d)`, so `four_dvd_level_of_two_mem_ramifiedPrimes` supplies the full factor `4`; it is
coprime to the odd number `|d|`. Together with `mem_of_sq_eq_of_squarefree`, this proves that the
fundamental discriminant is the least cyclotomic level in this case. -/
theorem fundamentalDiscriminant_natAbs_dvd_level_of_mod_four_eq_three {M : Type*} [Field M]
    [NumberField M] {N : ℕ} [IsCyclotomicExtension {N} ℚ M] {d : ℤ} (hd : Squarefree d)
    (hmod : d % 4 = 3) {x : M} (hx : x ^ 2 = (d : M)) :
    (fundamentalDiscriminant d).natAbs ∣ N := by
  have hdN : d.natAbs ∣ N := natAbs_dvd_level_of_squarefree (N := N) hd hx
  have h4N : 4 ∣ N := by
    apply IsCyclotomicExtension.four_dvd_level_of_two_mem_ramifiedPrimes M N (adjoin ℚ {x})
    apply (mem_ramifiedPrimes_adjoin_iff_dvd_fundamentalDiscriminant hd hx Nat.prime_two).mpr
    rw [fundamentalDiscriminant_of_mod_four_ne_one (by omega)]
    exact ⟨2 * d, by ring⟩
  have hodd : Odd d := by rw [Int.odd_iff]; omega
  have hcop : Nat.Coprime 4 d.natAbs := by
    simpa [show 4 = 2 ^ 2 by norm_num] using
      (Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hodd)).pow_left 2
  rw [fundamentalDiscriminant_of_mod_four_ne_one (by omega), Int.natAbs_mul]
  norm_num
  exact hcop.mul_dvd_of_dvd_of_dvd h4N hdN

/-- **Worked example: `√-3 ∈ ℚ(ζ₃)`.** The fundamental discriminant `-3` needs only a primitive cube
root of unity, where the bound `4 |m|` of `mem_of_sq_eq_intCast` asks for a twelfth root. -/
example {ζ x : L} (hζ : IsPrimitiveRoot ζ 3) (hx : x ^ 2 = -3) : x ∈ ℚ⟮ζ⟯ := by
  have h3 : oddPrimeDiscriminant 3 = -3 := oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num)
  refine mem_of_sq_eq_of_isFundamentalDiscriminant (by norm_num) hζ (mem_adjoin_simple_self ℚ ζ)
    (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_three ⟨1, rfl⟩).isFundamentalDiscriminant
    (by rw [h3]; rfl) ?_
  rw [hx, h3]
  push_cast
  ring

end TauCeti.Multiquadratic
