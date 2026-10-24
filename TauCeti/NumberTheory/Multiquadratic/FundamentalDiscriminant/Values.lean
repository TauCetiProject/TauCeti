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

The primitive character `fundamentalDiscriminantChar D hD` is the Kronecker character of `D`.
At an odd natural number `n` its value is `jacobiSym D n`, including zero when `n` is not
coprime to `D`. At even arguments the Jacobi symbol need not agree with the character.

This file also identifies the characters of prime discriminants, including `-4`, `8`, and
`-8`, and proves multiplicativity in coprime fundamental discriminants.
These evaluations allow quadratic splitting characters to be computed without choosing a
prime-discriminant factorization.

The construction and proofs use `fundamentalDiscriminantChar_apply_int` and the value laws
for `primeDiscriminantCharFun`. For the classical Kronecker convention, see K. Ireland and
M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6, and J. Voight,
*Quaternion Algebras*, §24.3.3.
-/

public section

namespace TauCeti.Multiquadratic

/-- At an odd natural number, the fundamental-discriminant character is the Jacobi symbol.
No coprimality is required, so the formula includes vanishing at ramified primes. -/
theorem fundamentalDiscriminantChar_natCast_eq_jacobiSym {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) {n : ℕ} (hn : Odd n) :
    fundamentalDiscriminantChar D hD (n : ℤ) = jacobiSym D n := by
  symm
  simpa only [MulChar.coe_toMonoidHom, Int.cast_natCast] using
    jacobiSym.value_at D (fundamentalDiscriminantChar D hD).toMonoidHom
      (fun p hp hp2 ↦ by
        have : Fact p.Prime := ⟨hp⟩
        simpa only [MulChar.coe_toMonoidHom, Int.cast_natCast] using
          (fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2).symm) hn

-- Simplify these integer evaluations before reducing their casts.
/-- A prime discriminant gives its previously defined prime-discriminant character. -/
@[simp↓]
theorem fundamentalDiscriminantChar_apply_primeDiscriminant {P : ℤ}
    (hP : IsPrimeDiscriminant P) (n : ℤ) :
    fundamentalDiscriminantChar P hP.isFundamentalDiscr n = primeDiscriminantCharFun P n := by
  rw [fundamentalDiscriminantChar_apply_int hP.isFundamentalDiscr
    (s := {P}) (by simpa using hP) (by simp), genusCharFun_singleton]

/-- At an odd prime discriminant `p*`, the character is the Legendre symbol modulo `p`. -/
theorem fundamentalDiscriminantChar_oddPrimeDiscr {p : ℕ} [Fact p.Prime] (hp : Odd p)
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
