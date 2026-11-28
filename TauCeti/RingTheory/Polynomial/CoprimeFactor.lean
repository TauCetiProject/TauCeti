/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Coprime factorization of reducible non-power polynomials

This file proves that a monic polynomial over a field that is neither irreducible nor a proper
power `Q ^ j` (`1 < j`) factors as a product of two coprime non-unit polynomials, and in fact as a
product of two coprime monic polynomials of positive degree.

## Main results

* `TauCeti.Polynomial.exists_isCoprime_mul_of_not_irreducible`: a monic polynomial over a field
  that is neither irreducible nor a proper power splits as `A * B` with `IsCoprime A B` and neither
  `A` nor `B` a unit.
* `TauCeti.Polynomial.exists_isCoprime_monic_mul_of_not_irreducible`: the same factorization with
  both factors monic and of positive degree.

## Provenance

Generalized from `New.exists_isCoprime_mul_of_not_irreducible` in
`src/Lib/Adelic/TraceFormula/ReduciblePolynomials.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {F : Type*} [Field F]

/-- A monic polynomial over a field that is neither irreducible nor a proper power `Q ^ j`
(`1 < j`) is a product of two coprime non-unit polynomials. -/
theorem exists_isCoprime_mul_of_not_irreducible {R : F[X]} (h_monic : R.Monic)
    (h_red : ¬Irreducible R) (h_pow : ∀ (Q : F[X]) (j : ℕ), 1 < j → R ≠ Q ^ j) :
    ∃ A B : F[X], IsCoprime A B ∧ ¬IsUnit A ∧ ¬IsUnit B ∧ R = A * B := by
  have h_not_unit : ¬IsUnit R := fun h_unit ↦
    h_pow 1 2 one_lt_two (by simp [h_monic.isUnit_iff.mp h_unit])
  obtain ⟨Q, hQ_monic, hQ_irred, hQ_dvd⟩ := R.exists_monic_irreducible_factor h_not_unit
  obtain ⟨i, A, h_not_dvd, rfl⟩ : ∃ (i : ℕ) (A : F[X]), ¬Q ∣ A ∧ R = Q ^ i * A :=
    WfDvdMonoid.max_power_factor h_monic.ne_zero hQ_irred
  have hi : i ≠ 0 := fun hi ↦ h_not_dvd (by simpa [hi] using hQ_dvd)
  refine ⟨Q ^ i, A, (hQ_irred.coprime_iff_not_dvd.mpr h_not_dvd).pow_left,
    mt (isUnit_pow_iff hi).mp hQ_irred.not_isUnit, fun h_unit ↦ ?_, rfl⟩
  obtain rfl : A = 1 := ((hQ_monic.pow i).of_mul_monic_left h_monic).isUnit_iff.mp h_unit
  obtain rfl | hi_gt : i = 1 ∨ 1 < i := by omega
  · exact h_red (by simpa using hQ_irred)
  · exact h_pow Q i hi_gt (mul_one _)

/-- A monic polynomial over a field that is neither irreducible nor a proper power `Q ^ j`
(`1 < j`) is a product of two coprime monic polynomials of positive degree. -/
theorem exists_isCoprime_monic_mul_of_not_irreducible {R : F[X]} (h_monic : R.Monic)
    (h_red : ¬Irreducible R) (h_pow : ∀ (Q : F[X]) (j : ℕ), 1 < j → R ≠ Q ^ j) :
    ∃ A B : F[X], IsCoprime A B ∧ A.Monic ∧ B.Monic ∧ 0 < A.natDegree ∧ 0 < B.natDegree ∧
      R = A * B := by
  have h_not_unit : ¬IsUnit R := fun h_unit ↦
    h_pow 1 2 one_lt_two (by simp [h_monic.isUnit_iff.mp h_unit])
  obtain ⟨Q, hQ_monic, hQ_irred, hQ_dvd⟩ := R.exists_monic_irreducible_factor h_not_unit
  obtain ⟨i, B, h_not_dvd, rfl⟩ : ∃ (i : ℕ) (B : F[X]), ¬Q ∣ B ∧ R = Q ^ i * B :=
    WfDvdMonoid.max_power_factor h_monic.ne_zero hQ_irred
  have hi : i ≠ 0 := fun hi ↦ h_not_dvd (by simpa [hi] using hQ_dvd)
  have hA_monic : (Q ^ i).Monic := hQ_monic.pow i
  have hB_monic : B.Monic := hA_monic.of_mul_monic_left h_monic
  have hA_nu : ¬IsUnit (Q ^ i) := mt (isUnit_pow_iff hi).mp hQ_irred.not_isUnit
  have hB_nu : ¬IsUnit B := fun h_unit ↦ by
    obtain rfl : B = 1 := hB_monic.isUnit_iff.mp h_unit
    obtain rfl | hi_gt : i = 1 ∨ 1 < i := by omega
    · exact h_red (by simpa using hQ_irred)
    · exact h_pow Q i hi_gt (mul_one _)
  exact ⟨Q ^ i, B, (hQ_irred.coprime_iff_not_dvd.mpr h_not_dvd).pow_left, hA_monic, hB_monic,
    Nat.pos_of_ne_zero (mt hA_monic.natDegree_eq_zero.mp fun h ↦ hA_nu (h ▸ isUnit_one)),
    Nat.pos_of_ne_zero (mt hB_monic.natDegree_eq_zero.mp fun h ↦ hB_nu (h ▸ isUnit_one)), rfl⟩

end TauCeti.Polynomial
