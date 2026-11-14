/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Values of fundamental-discriminant characters

The primitive character `fundamentalDiscriminantChar D hD` is the Kronecker character
`TauCeti.kroneckerChar` of `D`. At an odd natural number `n` its value is `jacobiSym D n`, including
zero when `n` is not coprime to `D`. At even arguments the Jacobi symbol need not agree with the
character. Since `fundamentalDiscriminant d` differs from `d` by `1` or `4`, its Jacobi symbol and
quadratic-residue status modulo odd arguments, as well as its Legendre symbol at odd primes,
coincide with those of `d`.

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

/-- At an odd natural number `n`, `fundamentalDiscriminant d` has the same Jacobi symbol as `d`,
since the two differ by `1` or `4`, both squares prime to `n`. -/
theorem jacobiSym_fundamentalDiscriminant (d : ℤ) {n : ℕ} (hn : Odd n) :
    jacobiSym (fundamentalDiscriminant d) n = jacobiSym d n := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  have hcop : c.gcd n = 1 := by
    rcases hc with rfl | rfl
    · exact Int.gcd_one_left n
    · exact hn.coprime_two_left
  rw [← hcd, jacobiSym.mul_left, jacobiSym.sq_one' hcop, one_mul]

/-- At an odd prime `p`, `fundamentalDiscriminant d` has the same Legendre symbol as `d`,
including `0` at primes dividing `d`. -/
theorem legendreSym_fundamentalDiscriminant (d : ℤ) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (fundamentalDiscriminant d) = legendreSym p d := by
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_fundamentalDiscriminant d ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-- Modulo an odd natural number `n`, `fundamentalDiscriminant d` is a square if and only if `d`
is a square. -/
theorem isSquare_fundamentalDiscriminant_zmod_iff (d : ℤ) {n : ℕ} (hn : Odd n) :
    IsSquare ((fundamentalDiscriminant d : ℤ) : ZMod n) ↔ IsSquare (d : ZMod n) := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  have hu : IsUnit (c : ZMod n) := by
    rcases hc with rfl | rfl
    · rw [Int.cast_one]
      exact isUnit_one
    · rw [← Nat.cast_two, Int.cast_natCast]
      exact (ZMod.isUnit_iff_coprime 2 n).mpr hn.coprime_two_left
  rw [← hcd, Int.cast_mul, Int.cast_pow]
  refine ⟨fun h ↦ ?_, (IsSquare.sq (c : ZMod n)).mul⟩
  have hinv : ((hu.unit⁻¹ : Units (ZMod n)) : ZMod n) ^ 2 *
      ((c : ZMod n) ^ 2 * (d : ZMod n)) = (d : ZMod n) := by
    rw [← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul]
  exact hinv ▸ (IsSquare.sq ((hu.unit⁻¹ : Units (ZMod n)) : ZMod n)).mul h

/-- At an odd natural number `n`, the character of `fundamentalDiscriminant d` equals
`jacobiSym d n`, including `0` when `n` is not coprime to `d`. -/
theorem fundamentalDiscriminantChar_fundamentalDiscriminant_natCast_eq_jacobiSym {d : ℤ}
    (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d)) {n : ℕ} (hn : Odd n) :
    fundamentalDiscriminantChar (fundamentalDiscriminant d) hD (n : ℤ) = jacobiSym d n := by
  rw [fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hn,
    jacobiSym_fundamentalDiscriminant d hn]

/-- At an odd prime `p`, the character of `fundamentalDiscriminant d` equals `legendreSym p d`,
including `0` when `p ∣ d`. -/
theorem fundamentalDiscriminantChar_fundamentalDiscriminant_natCast_eq_legendreSym {d : ℤ}
    (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d)) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    fundamentalDiscriminantChar (fundamentalDiscriminant d) hD (p : ℤ) = legendreSym p d := by
  rw [fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp,
    legendreSym_fundamentalDiscriminant d hp]

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
