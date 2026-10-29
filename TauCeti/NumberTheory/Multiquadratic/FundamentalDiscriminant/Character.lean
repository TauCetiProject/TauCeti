/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Dirichlet

/-!
# The primitive character of a fundamental discriminant

A fundamental discriminant `D` determines a primitive integer-valued Dirichlet character
`fundamentalDiscriminantChar` of level `|D|`: the Kronecker character `TauCeti.kroneckerChar` of
`D`, whose side conditions `D ≡ 0, 1 (mod 4)` and `D ≠ 0` a fundamental discriminant satisfies. It
is the product of the characters of the prime discriminants in any factorization of `D`, which is
how it is shown to be primitive. At an odd prime `q` its value is `legendreSym q D`, including the
value zero when `q` divides `D`, and at `2` it is `χ₈(D)`. It is nontrivial unless `D = 1`.

This identifies the conductor of the quadratic splitting character, which is needed to
determine the least cyclotomic field containing the associated quadratic field. The case
`D = 1` is included and gives the trivial character at level one.

See K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6,
and D. A. Cox, *Primes of the Form x² + ny²*, §3.B.
-/

public section

namespace TauCeti.Multiquadratic

open DirichletCharacter

/-- The quadratic Dirichlet character of a fundamental discriminant, at level `|D|`: the
Kronecker character `(D / ·)`. -/
def fundamentalDiscriminantChar (D : ℤ) (hD : Int.IsFundamentalDiscr D) :
    DirichletCharacter ℤ D.natAbs :=
  kroneckerChar ℤ D (hD.emod_four_eq_zero_or_one.imp id id) hD.ne_zero

/-- The fundamental-discriminant character at the class of an integer `n` is the Kronecker symbol
`(D / n)`. -/
theorem fundamentalDiscriminantChar_intCast {D : ℤ} (hD : Int.IsFundamentalDiscr D) (n : ℤ) :
    fundamentalDiscriminantChar D hD n = kroneckerSym D n :=
  kroneckerChar_intCast _ _ n

/-- Evaluation in terms of the integer-valued genus character of any factorization. -/
theorem fundamentalDiscriminantChar_apply_int {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hprod : ∏ P ∈ s, P = D)
    (n : ℤ) : fundamentalDiscriminantChar D hD n = genusCharFun s n := by
  rw [fundamentalDiscriminantChar_intCast, genusCharFun_def, ← hprod]
  clear hD hprod
  induction s using Finset.induction_on with
  | empty => simp
  | insert P s hP ih =>
    have hs' : ∀ Q ∈ s, IsPrimeDiscriminant Q := fun Q hQ ↦ hs Q (Finset.mem_insert_of_mem hQ)
    rw [Finset.prod_insert hP, Finset.prod_insert hP,
      kroneckerSym_mul_left (hs P (Finset.mem_insert_self P s)).ne_zero
        (Finset.prod_ne_zero_iff.mpr fun Q hQ ↦ (hs' Q hQ).ne_zero),
      primeDiscriminantCharFun_eq_kroneckerSym (hs P (Finset.mem_insert_self P s)), ih hs']

/-- Any prime-discriminant factorization computes the character of a fundamental discriminant. -/
theorem fundamentalDiscriminantChar_eq_genusChar {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hprod : ∏ P ∈ s, P = D) :
    fundamentalDiscriminantChar D hD =
      changeLevel (Int.natAbs_dvd_natAbs.mpr (dvd_of_eq hprod)) (genusChar s hs) := by
  subst D
  rw [changeLevel_self]
  refine MulChar.ext' fun x ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [fundamentalDiscriminantChar_apply_int hD hs rfl, genusChar_apply_int]

/-- The fundamental-discriminant character at `-1` is the sign of the discriminant. -/
theorem fundamentalDiscriminantChar_neg_one {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantChar D hD (-1) = D.sign :=
  kroneckerChar_neg_one _ _

/-- The Dirichlet character of a fundamental discriminant is quadratic. -/
theorem fundamentalDiscriminantChar_isQuadratic {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    (fundamentalDiscriminantChar D hD).IsQuadratic :=
  kroneckerChar_isQuadratic _ _

/-- The character of a fundamental discriminant has conductor exactly `|D|`. -/
theorem isPrimitive_fundamentalDiscriminantChar {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    IsPrimitive (fundamentalDiscriminantChar D hD) := by
  obtain ⟨s, hs, heven, hprod⟩ := hD.exists_finset_primeDiscriminant
  subst D
  rw [fundamentalDiscriminantChar_eq_genusChar hD hs rfl, changeLevel_self]
  exact isPrimitive_genusChar hs heven

/-- At an odd prime, the fundamental-discriminant character is the quadratic splitting symbol. -/
theorem fundamentalDiscriminantChar_natCast_eq_legendreSym {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    fundamentalDiscriminantChar D hD (q : ℤ) = legendreSym q D := by
  rw [fundamentalDiscriminantChar_intCast, kroneckerSym_eq_legendreSym D q hq]

/-- **The fundamental-discriminant character at `2` is `χ₈` of the discriminant.** It vanishes
for even `D`, and for odd `D`, which is `1` modulo `4`, it is `1` when `D ≡ 1 (mod 8)` and `-1`
when `D ≡ 5 (mod 8)`. This is the value of the Kronecker symbol `(D / 2)`. -/
@[simp]
theorem fundamentalDiscriminantChar_two {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantChar D hD 2 = ZMod.χ₈ (D : ZMod 8) := by
  simpa using fundamentalDiscriminantChar_intCast hD 2

/-- **The character of a fundamental discriminant `D ≠ 1` is nontrivial.** -/
theorem fundamentalDiscriminantChar_ne_one {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h1 : D ≠ 1) : fundamentalDiscriminantChar D hD ≠ 1 := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
  have hD1 : D.natAbs ≠ 1 := by
    have := hD.emod_four_eq_zero_or_one
    omega
  rw [Ne, eq_one_iff_conductor_eq_one,
    (isPrimitive_def _).mp (isPrimitive_fundamentalDiscriminantChar hD)]
  exact hD1

end TauCeti.Multiquadratic
