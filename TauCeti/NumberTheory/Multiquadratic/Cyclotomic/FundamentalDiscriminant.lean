/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Basic
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.GaussSum
public import Mathlib.RingTheory.RootsOfUnity.Complex

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
