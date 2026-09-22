/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Basic
public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Dirichlet.Group
import Mathlib.Data.Int.NatAbs

/-!
# Primitive Dirichlet characters from prime-discriminant products

`genusChar` bundles the existing integer-valued `genusCharFun` as a Dirichlet character at
the absolute value of the product of its prime discriminants. When at most one factor is even,
this character is primitive. Thus the quadratic character of a fundamental discriminant `D`
has conductor `|D|`, the character-theoretic input for identifying the least cyclotomic level
of its quadratic field.

The construction is the whole-family case of `genusCharAtLevel`, which lifts the primitive
prime-discriminant characters to the common level `|∏ P ∈ s, P|` and multiplies those indexed by
a subset: `genusChar s hs` is `genusCharAtLevel s hs Finset.univ`. Distinct factors, with at most
one even factor, have coprime absolute values, so their conductors multiply
(`conductor_genusCharAtLevel`), which is what makes the whole product primitive. The empty
factorization gives the trivial character at level one.

The character description follows K. Ireland and M. Rosen, *A Classical Introduction to Modern
Number Theory*, Chapter 6, and D. A. Cox, *Primes of the Form x² + ny²*, §3.B.
-/

public section

namespace TauCeti.Multiquadratic

open DirichletCharacter

/-- The product of the prime-discriminant characters, at the absolute value of the product
of the discriminants. Its value on integers is `genusCharFun`. -/
noncomputable def genusChar (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P) :
    DirichletCharacter ℤ (∏ P ∈ s, P).natAbs :=
  genusCharAtLevel s hs Finset.univ

/-- The character indexed by the whole family is the genus character of that family. -/
theorem genusCharAtLevel_univ (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P) :
    genusCharAtLevel s hs Finset.univ = genusChar s hs := (rfl)

/-- The expression for `genusChar` in terms of prime-discriminant characters at a common level. -/
theorem genusChar_def (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P) :
    genusChar s hs = ∏ P : s, primeDiscriminantCharAtLevel s hs P := (rfl)

/-- The bundled genus character agrees with the existing character function on every integer,
including integers not coprime to the level. -/
@[simp] theorem genusChar_apply_int (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (n : ℤ) : genusChar s hs n = genusCharFun s n := by
  by_cases hn : IsCoprime n (∏ P ∈ s, P)
  · have hn' : IsCoprime n ((∏ P ∈ s, P).natAbs : ℤ) := by
      simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hn
    rw [← genusCharAtLevel_univ, genusCharAtLevel_apply_int s hs Finset.univ n hn',
      genusCharFun_def]
    exact Finset.prod_coe_sort s fun P ↦ primeDiscriminantCharFun P n
  · rw [(genusCharFun_eq_zero_iff hs).mpr hn, apply_eq_zero_iff]
    simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hn

/-- A product of distinct prime-discriminant characters with at most one even factor is
primitive: its conductor is the absolute value of the product of the discriminants. -/
theorem isPrimitive_genusChar {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) :
    IsPrimitive (genusChar s hs) := by
  rw [isPrimitive_def, ← genusCharAtLevel_univ,
    conductor_genusCharAtLevel s hs Finset.univ
      (fun P _ Q _ hP hQ ↦ Subtype.ext (heven P P.property Q Q.property hP hQ)),
    Finset.prod_coe_sort s fun P ↦ P.natAbs]
  exact (map_prod Int.natAbsHom (fun P ↦ P) s).symm

end TauCeti.Multiquadratic
