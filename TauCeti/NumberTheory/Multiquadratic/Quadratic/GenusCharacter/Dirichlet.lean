/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Basic
public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Dirichlet.Character
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.Data.Int.NatAbs

/-!
# Primitive Dirichlet characters from prime-discriminant products

`genusChar` bundles the existing integer-valued `genusCharFun` as a Dirichlet character at
the absolute value of the product of its prime discriminants. When at most one factor is even,
this character is primitive. Thus the quadratic character of a fundamental discriminant `D`
has conductor `|D|`, the character-theoretic input for identifying the least cyclotomic level
of its quadratic field.

The construction lifts the primitive prime-discriminant characters to a common level and
multiplies them. Distinct factors, with at most one even factor, have coprime absolute values,
so their conductors multiply. The empty factorization gives the trivial character at level one.

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
  ∏ P : s, changeLevel
    (Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem (fun P : ℤ ↦ P) P.property))
    (primeDiscriminantChar P (hs P P.property))

/-- The expression for `genusChar` in terms of prime-discriminant characters at a common level. -/
theorem genusChar_def (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P) :
    genusChar s hs =
      ∏ P : s, changeLevel
        (Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem (fun P : ℤ ↦ P) P.property))
        (primeDiscriminantChar P (hs P P.property)) := (rfl)

/-- The bundled genus character agrees with the existing character function on every integer,
including integers not coprime to the level. -/
@[simp] theorem genusChar_apply_int (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (n : ℤ) : genusChar s hs n = genusCharFun s n := by
  by_cases hn : IsCoprime n (∏ P ∈ s, P)
  · have hn' : IsCoprime n ((∏ P ∈ s, P).natAbs : ℤ) := by
      simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hn
    have hu : IsUnit (n : ZMod (∏ P ∈ s, P).natAbs) :=
      (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr hn'.symm
    rw [genusChar_def, genusCharFun_def]
    let ev := (Units.coeHom ℤ).comp
      ((MonoidHom.eval hu.unit).comp MulChar.mulEquivToUnitHom.toMonoidHom)
    have heval := map_prod ev (fun P : s ↦ changeLevel
      (Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem (fun P : ℤ ↦ P) P.property))
      (primeDiscriminantChar P (hs P P.property))) Finset.univ
    simp only [ev, MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.eval_apply_apply,
      MulEquiv.coe_toMonoidHom, MulChar.mulEquivToUnitHom_apply, MulChar.coe_equivToUnitHom,
      IsUnit.unit_spec, changeLevel_eq_cast_of_dvd' _ _ hn',
      primeDiscriminantChar_apply_int] at heval
    exact heval.trans (Finset.prod_coe_sort s (fun P ↦ primeDiscriminantCharFun P n))
  · rw [(genusCharFun_eq_zero_iff hs).mpr hn, apply_eq_zero_iff]
    simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hn

/-- A product of distinct prime-discriminant characters with at most one even factor is
primitive: its conductor is the absolute value of the product of the discriminants. -/
theorem isPrimitive_genusChar {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) :
    IsPrimitive (genusChar s hs) := by
  let : NeZero (∏ P ∈ s, P).natAbs :=
    ⟨Int.natAbs_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun P hP ↦ (hs P hP).ne_zero)⟩
  have hc (P : s) :
      (changeLevel (Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem (fun P : ℤ ↦ P) P.property))
        (primeDiscriminantChar P (hs P P.property))).conductor = P.val.natAbs := by
    rw [conductor_changeLevel]
    exact (isPrimitive_primeDiscriminantChar P (hs P P.property))
  rw [isPrimitive_def, genusChar_def, conductor_prod_eq_prod_of_pairwise_coprime]
  · simp_rw [hc]
    rw [Finset.prod_coe_sort]
    exact (map_prod Int.natAbsHom (fun P ↦ P) s).symm
  · intro P _ Q _ hPQ
    rw [hc, hc]
    exact Int.isCoprime_iff_nat_coprime.mp
      (isCoprime_primeDiscriminant_of_ne_of_not_both_even (hs P P.property) (hs Q Q.property)
        (fun h ↦ hPQ (Subtype.ext h))
        (fun h ↦ hPQ (Subtype.ext (heven P P.property Q Q.property h.1 h.2))))

end TauCeti.Multiquadratic
