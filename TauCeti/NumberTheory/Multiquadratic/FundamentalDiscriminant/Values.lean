/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Values of fundamental-discriminant characters

The primitive character `fundamentalDiscriminantChar D hD` is the Kronecker character
`TauCeti.kroneckerChar` of `D`. At an odd natural number `n` its value is `jacobiSym D n`, including
zero when `n` is not coprime to `D`. At even arguments the Jacobi symbol need not agree with the
character.

At any odd natural number `n`, the factor `4` separating a discriminant `D` from its radicand
`fundamentalDiscriminantRadicand D` is coprime to `n` and a square, so `jacobiSym D n` and
`jacobiSym (fundamentalDiscriminantRadicand D) n` coincide (and hence `legendreSym p D` and
`legendreSym p (fundamentalDiscriminantRadicand D)` coincide at every odd prime `p`, including `0`
when `p ∣ D`). Consequently `fundamentalDiscriminantChar D hD n` at odd `n` may be read off either
parameter.

This file also identifies the characters of prime discriminants, including `-4`, `-3`, `8`,
and `-8`, and proves multiplicativity in coprime fundamental discriminants.

For the classical Kronecker convention, see K. Ireland and M. Rosen, *A Classical Introduction
to Modern Number Theory*, Chapter 6, and J. Voight, *Quaternion Algebras*, §24.3.3.
-/

public section

namespace TauCeti.Multiquadratic

/-- At an odd natural number, the fundamental-discriminant character is the Jacobi symbol.
No coprimality is required, so the formula includes vanishing at ramified primes. -/
theorem fundamentalDiscriminantChar_natCast_eq_jacobiSym {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) {n : ℕ} (hn : Odd n) :
    fundamentalDiscriminantChar D hD (n : ℤ) = jacobiSym D n := by
  rw [fundamentalDiscriminantChar_intCast, kroneckerSym_eq_jacobiSym D hn]

/-- At an odd natural number `n`, replacing an integer `d` by `fundamentalDiscriminant d` does not
change its Jacobi symbol modulo `n`, since the two differ at most by `2 ^ 2`. -/
@[simp]
theorem jacobiSym_fundamentalDiscriminant {n : ℕ} (hn : Odd n) (d : ℤ) :
    jacobiSym (fundamentalDiscriminant d) n = jacobiSym d n := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  have hcop : c.gcd n = 1 := by
    rcases hc with rfl | rfl
    · exact Int.gcd_one_left n
    · exact Nat.coprime_two_left.mpr hn
  rw [← hcd, jacobiSym.mul_left, jacobiSym.sq_one' hcop, one_mul]

/-- At an odd prime `p`, replacing an integer `d` by `fundamentalDiscriminant d` does not change
its Legendre symbol modulo `p`. -/
@[simp]
theorem legendreSym_fundamentalDiscriminant {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (d : ℤ) :
    legendreSym p (fundamentalDiscriminant d) = legendreSym p d := by
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_fundamentalDiscriminant ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-- At an odd natural number `n`, a discriminant `D ≡ 0` or `1 (mod 4)` has the same Jacobi symbol
modulo `n` as `fundamentalDiscriminantRadicand D`. -/
theorem jacobiSym_fundamentalDiscriminantRadicand {n : ℕ} (hn : Odd n) {D : ℤ}
    (hD : D % 4 = 0 ∨ D % 4 = 1) :
    jacobiSym (fundamentalDiscriminantRadicand D) n = jacobiSym D n := by
  rcases hD with h0 | h1
  · rw [fundamentalDiscriminantRadicand_of_mod_four_ne_one (by omega)]
    have h4 : D = (2 : ℤ) ^ 2 * (D / 4) := by omega
    have hcop : (2 : ℤ).gcd n = 1 := Nat.coprime_two_left.mpr hn
    conv_rhs => rw [h4, jacobiSym.mul_left, jacobiSym.sq_one' hcop, one_mul]
  · rw [fundamentalDiscriminantRadicand_of_mod_four_eq_one h1]

/-- At an odd prime `p`, a discriminant `D ≡ 0` or `1 (mod 4)` has the same Legendre symbol modulo
`p` as `fundamentalDiscriminantRadicand D`. -/
theorem legendreSym_fundamentalDiscriminantRadicand {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    legendreSym p (fundamentalDiscriminantRadicand D) = legendreSym p D := by
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_fundamentalDiscriminantRadicand ((Fact.out : p.Prime).odd_of_ne_two hp) hD]

/-- At an odd natural number `n`, the fundamental-discriminant character of `D` equals the Jacobi
symbol modulo `n` of `fundamentalDiscriminantRadicand D`, including `0` when `gcd D n ≠ 1`. -/
theorem fundamentalDiscriminantChar_natCast_eq_jacobiSym_radicand {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) {n : ℕ} (hn : Odd n) :
    fundamentalDiscriminantChar D hD (n : ℤ) =
      jacobiSym (fundamentalDiscriminantRadicand D) n :=
  (fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hn).trans
    (jacobiSym_fundamentalDiscriminantRadicand hn hD.emod_four_eq_zero_or_one).symm

/-- At an odd prime `p`, the fundamental-discriminant character of `D` equals the Legendre symbol
modulo `p` of its squarefree radicand `fundamentalDiscriminantRadicand D`, including `0` when
`p ∣ D`. -/
theorem fundamentalDiscriminantChar_natCast_eq_legendreSym_radicand {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    fundamentalDiscriminantChar D hD (p : ℤ) =
      legendreSym p (fundamentalDiscriminantRadicand D) := by
  rw [fundamentalDiscriminantChar_natCast_eq_jacobiSym_radicand hD
      ((Fact.out : p.Prime).odd_of_ne_two hp),
    jacobiSym.legendreSym.to_jacobiSym]

/-- At an odd natural number `n`, the character of `fundamentalDiscriminant d` for squarefree `d`
takes the value `jacobiSym d n`. -/
theorem fundamentalDiscriminantChar_fundamentalDiscriminant_natCast_eq_jacobiSym {d : ℤ}
    (hd : Squarefree d) {n : ℕ} (hn : Odd n) :
    fundamentalDiscriminantChar (fundamentalDiscriminant d)
      (isFundamentalDiscr_fundamentalDiscriminant hd) (n : ℤ) = jacobiSym d n := by
  rw [fundamentalDiscriminantChar_natCast_eq_jacobiSym_radicand _ hn,
    fundamentalDiscriminantRadicand_fundamentalDiscriminant]

/-- At an odd prime `p`, the character of `fundamentalDiscriminant d` for squarefree `d` takes the
value `legendreSym p d`, including `0` when `p ∣ d`. -/
theorem fundamentalDiscriminantChar_fundamentalDiscriminant_natCast_eq_legendreSym {d : ℤ}
    (hd : Squarefree d) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    fundamentalDiscriminantChar (fundamentalDiscriminant d)
      (isFundamentalDiscr_fundamentalDiscriminant hd) (p : ℤ) = legendreSym p d := by
  rw [fundamentalDiscriminantChar_fundamentalDiscriminant_natCast_eq_jacobiSym hd
      ((Fact.out : p.Prime).odd_of_ne_two hp),
    jacobiSym.legendreSym.to_jacobiSym]

-- Simplify these integer evaluations before reducing their casts.
/-- A prime discriminant gives its previously defined prime-discriminant character. -/
@[simp↓]
theorem fundamentalDiscriminantChar_apply_primeDiscriminant {P : ℤ}
    (hP : IsPrimeDiscriminant P) (n : ℤ) :
    fundamentalDiscriminantChar P hP.isFundamentalDiscr n = primeDiscriminantCharFun P n := by
  rw [fundamentalDiscriminantChar_apply_int hP.isFundamentalDiscr
    (s := {P}) (by simpa using hP) (by simp), genusCharFun_singleton]

/-- At an odd prime discriminant `p*`, the character is the Legendre symbol modulo `p`. -/
theorem fundamentalDiscriminantChar_oddPrimeDiscriminant {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (n : ℤ) :
    fundamentalDiscriminantChar (oddPrimeDiscriminant p)
      (isPrimeDiscriminant_oddPrimeDiscriminant Fact.out hp).isFundamentalDiscr n =
      legendreSym p n := by
  rw [fundamentalDiscriminantChar_apply_primeDiscriminant
    (isPrimeDiscriminant_oddPrimeDiscriminant Fact.out hp),
    primeDiscriminantCharFun_oddPrimeDiscriminant hp, jacobiSym.legendreSym.to_jacobiSym]

/-- Characters multiply with coprime fundamental discriminants, at every integer, including
arguments at which one of the characters vanishes. -/
theorem fundamentalDiscriminantChar_mul {D E : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hE : Int.IsFundamentalDiscr E) (hcop : IsCoprime D E) (n : ℤ) :
    fundamentalDiscriminantChar (D * E) (hD.mul hE hcop) n =
      fundamentalDiscriminantChar D hD n * fundamentalDiscriminantChar E hE n := by
  classical
  obtain ⟨s, hs, _, hsprod⟩ := hD.exists_finset_primeDiscriminant
  obtain ⟨t, ht, _, htprod⟩ := hE.exists_finset_primeDiscriminant
  have hdisj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro P hPs hPt
    have hPD : P ∣ D := hsprod ▸ Finset.dvd_prod_of_mem id hPs
    have hPE : P ∣ E := htprod ▸ Finset.dvd_prod_of_mem id hPt
    have hu := Int.isUnit_iff_natAbs_eq.mp (hcop.isUnit_of_dvd' hPD hPE)
    exact (hs P hPs).one_lt_natAbs.ne' hu
  have hst : ∀ P ∈ s ∪ t, IsPrimeDiscriminant P := by
    simpa only [Finset.mem_union, or_imp, forall_and] using And.intro hs ht
  have hprod : ∏ P ∈ s ∪ t, P = D * E := by
    rw [Finset.prod_union hdisj, hsprod, htprod]
  rw [fundamentalDiscriminantChar_apply_int (hD.mul hE hcop) hst hprod,
    fundamentalDiscriminantChar_apply_int hD hs hsprod,
    fundamentalDiscriminantChar_apply_int hE ht htprod]
  simp only [genusCharFun_def, Finset.prod_union hdisj]

-- Prefer these explicit evaluations to the generic prime-discriminant rule.
/-- The character of `-4` is `χ₄` at every integer. -/
@[simp↓ high]
theorem fundamentalDiscriminantChar_neg_four (n : ℤ) :
    fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr n =
      ZMod.χ₄ (n : ZMod 4) := by
  rw [fundamentalDiscriminantChar_apply_primeDiscriminant isPrimeDiscriminant_neg_four,
    primeDiscriminantCharFun_neg_four]

/-- The character of `-3` is the Legendre symbol modulo `3` at every integer. -/
@[simp↓ high]
theorem fundamentalDiscriminantChar_neg_three (hD : Int.IsFundamentalDiscr (-3)) (n : ℤ) :
    fundamentalDiscriminantChar (-3) hD n = legendreSym 3 n :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  fundamentalDiscriminantChar_oddPrimeDiscriminant (p := 3) (by decide) n

/-- The character of `8` is `χ₈` at every integer. -/
@[simp↓ high]
theorem fundamentalDiscriminantChar_eight (n : ℤ) :
    fundamentalDiscriminantChar 8 isPrimeDiscriminant_eight.isFundamentalDiscr n =
      ZMod.χ₈ (n : ZMod 8) := by
  rw [fundamentalDiscriminantChar_apply_primeDiscriminant isPrimeDiscriminant_eight,
    primeDiscriminantCharFun_eight]

/-- The character of `-8` is `χ₈'` at every integer. -/
@[simp↓ high]
theorem fundamentalDiscriminantChar_neg_eight (n : ℤ) :
    fundamentalDiscriminantChar (-8) isPrimeDiscriminant_neg_eight.isFundamentalDiscr n =
      ZMod.χ₈' (n : ZMod 8) := by
  rw [fundamentalDiscriminantChar_apply_primeDiscriminant isPrimeDiscriminant_neg_eight,
    primeDiscriminantCharFun_neg_eight]

/-! The Jacobi comparison includes ramified primes and odd composite arguments. -/

example (h12 : Int.IsFundamentalDiscr 12) :
    fundamentalDiscriminantChar 12 h12 (5 : ℤ) = -1 ∧
      fundamentalDiscriminantChar 12 h12 (7 : ℤ) = -1 ∧
      fundamentalDiscriminantChar 12 h12 (11 : ℤ) = 1 := by
  have h5 := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 5)
  have h7 := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 7)
  have h11 := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 11)
  norm_num at h5 h7 h11
  exact ⟨h5, h7, h11⟩

example (h12 : Int.IsFundamentalDiscr 12) :
    fundamentalDiscriminantChar 12 h12 (9 : ℤ) = 0 := by
  have h := fundamentalDiscriminantChar_natCast_eq_jacobiSym h12 (by decide : Odd 9)
  norm_num at h ⊢
  exact h

end TauCeti.Multiquadratic
