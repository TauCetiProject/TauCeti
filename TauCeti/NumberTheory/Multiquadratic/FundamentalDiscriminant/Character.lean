/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Dirichlet

/-!
# The primitive character of a fundamental discriminant

A fundamental discriminant `D` determines a primitive integer-valued Dirichlet character
`fundamentalDiscriminantChar` of level `|D|`. It is the product of the characters of the
prime discriminants in any factorization of `D`. At an odd prime `q` its value is
`legendreSym q D`, including the value zero when `q` divides `D`.

This identifies the conductor of the quadratic splitting character, which is needed to
determine the least cyclotomic field containing the associated quadratic field. The case
`D = 1` is included and gives the trivial character at level one.

See K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6,
and D. A. Cox, *Primes of the Form x² + ny²*, §3.B.
-/

public section

namespace TauCeti.Multiquadratic

open DirichletCharacter

/-- The quadratic Dirichlet character of a fundamental discriminant, at level `|D|`. -/
noncomputable def fundamentalDiscriminantChar (D : ℤ) (hD : IsFundamentalDiscriminant D) :
    DirichletCharacter ℤ D.natAbs :=
  let h := hD.exists_finset_primeDiscriminant.choose_spec
  changeLevel (Int.natAbs_dvd_natAbs.mpr (dvd_of_eq h.2.2))
    (genusChar _ h.1)

/-- Any prime-discriminant factorization computes the character of a fundamental discriminant. -/
theorem fundamentalDiscriminantChar_eq_genusChar {D : ℤ} (hD : IsFundamentalDiscriminant D)
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hprod : ∏ P ∈ s, P = D) :
    fundamentalDiscriminantChar D hD =
      changeLevel (Int.natAbs_dvd_natAbs.mpr (dvd_of_eq hprod)) (genusChar s hs) := by
  have h := hD.exists_finset_primeDiscriminant.choose_spec
  have heq : hD.exists_finset_primeDiscriminant.choose = s :=
    finset_primeDiscriminant_eq_of_prod_eq h.1 hs (h.2.2.trans hprod.symm)
  subst s
  rfl

/-- Evaluation in terms of the integer-valued genus character of any factorization. -/
theorem fundamentalDiscriminantChar_apply_int {D : ℤ} (hD : IsFundamentalDiscriminant D)
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hprod : ∏ P ∈ s, P = D)
    (n : ℤ) : fundamentalDiscriminantChar D hD n = genusCharFun s n := by
  subst D
  rw [fundamentalDiscriminantChar_eq_genusChar hD hs rfl, changeLevel_self,
    genusChar_apply_int]

/-- The fundamental-discriminant character at `-1` is the sign of the discriminant. -/
theorem fundamentalDiscriminantChar_neg_one {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    fundamentalDiscriminantChar D hD (-1) = D.sign := by
  obtain ⟨s, hs, _, hprod⟩ := hD.exists_finset_primeDiscriminant
  have h := fundamentalDiscriminantChar_apply_int hD hs hprod (-1)
  rw [genusCharFun_neg_one_eq_sign_prod hs, hprod] at h
  simpa using h

/-- The Dirichlet character of a fundamental discriminant is quadratic. -/
theorem fundamentalDiscriminantChar_isQuadratic {D : ℤ}
    (hD : IsFundamentalDiscriminant D) :
    (fundamentalDiscriminantChar D hD).IsQuadratic := by
  let _ : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
  obtain ⟨s, hs, _, hprod⟩ := hD.exists_finset_primeDiscriminant
  intro a
  have hval : fundamentalDiscriminantChar D hD a = genusCharFun s (a.val : ℤ) := by
    calc
      _ = fundamentalDiscriminantChar D hD ((a.val : ℕ) : ZMod D.natAbs) := by
        rw [ZMod.natCast_zmod_val]
      _ = genusCharFun s ((a.val : ℕ) : ℤ) := by
        simpa only [Int.cast_natCast] using
          fundamentalDiscriminantChar_apply_int hD hs hprod ((a.val : ℕ) : ℤ)
  rw [hval]
  by_cases ha : IsCoprime (a.val : ℤ) (∏ P ∈ s, P)
  · exact Or.inr (genusCharFun_eq_one_or_eq_neg_one hs ha)
  · exact Or.inl <| (genusCharFun_eq_zero_iff hs).mpr ha

/-- The character of a fundamental discriminant has conductor exactly `|D|`. -/
theorem isPrimitive_fundamentalDiscriminantChar {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    IsPrimitive (fundamentalDiscriminantChar D hD) := by
  obtain ⟨s, hs, heven, hprod⟩ := hD.exists_finset_primeDiscriminant
  subst D
  rw [fundamentalDiscriminantChar_eq_genusChar hD hs rfl, changeLevel_self]
  exact isPrimitive_genusChar hs heven

/-- At an odd prime, the fundamental-discriminant character is the quadratic splitting symbol. -/
theorem fundamentalDiscriminantChar_natCast_eq_legendreSym {D : ℤ}
    (hD : IsFundamentalDiscriminant D) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    fundamentalDiscriminantChar D hD (q : ℤ) = legendreSym q D := by
  obtain ⟨s, hs, _, hprod⟩ := hD.exists_finset_primeDiscriminant
  rw [fundamentalDiscriminantChar_apply_int hD hs hprod,
    genusCharFun_natCast_eq_legendreSym_prod hs hq, hprod]

end TauCeti.Multiquadratic
