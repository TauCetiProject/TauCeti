/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Degree
public import TauCeti.Algebra.Polynomial.Laurent.Coeff
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Laurent polynomials with unit highest coefficient are regular

Multiplication by a monomial shifts the highest exponent without changing its coefficient.
Clearing negative exponents therefore reduces regularity to Mathlib's polynomial theorem for a
unit leading coefficient. The coefficient ring can have zero divisors, and the result survives
any coefficient homomorphism, including a quotient map.
-/

public section

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Shifting an ordinary polynomial by any Laurent monomial preserves its leading coefficient. -/
theorem leadingCoeff_toLaurent_mul_T (p : Polynomial R) (n : ℤ) :
    (p.toLaurent * T n).leadingCoeff ((↑) : ℤ → WithBot ℤ) = p.leadingCoeff := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  have hc (k : ℕ) : (p.toLaurent * T n).coeff (k + n) = p.coeff k := by
    rw [T, coeff_mul_single_add, mul_one, coeff_toLaurent]
    change p.coeff.mapDomain Nat.castEmbedding (Nat.castEmbedding k) = p.coeff k
    rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
  have hd : (p.toLaurent * T n).supDegree ((↑) : ℤ → WithBot ℤ) =
      ↑((p.natDegree : ℤ) + n) := by
    apply supDegree_eq_of_max ⟨_, rfl⟩
    · rw [Function.leftInverse_invFun WithBot.coe_injective (_ + n),
        Finsupp.mem_support_iff, hc]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    · intro a ha
      have hcoef := Finsupp.mem_support_iff.1 ha
      rw [mul_comm p.toLaurent (T n), coeff_T_mul] at hcoef
      have hm : a - n ∈ p.support.map Nat.castEmbedding := by
        rw [← support_coeff_toLaurent]
        exact Finsupp.mem_support_iff.2 hcoef
      obtain ⟨k, hk, he⟩ := Finset.mem_map.1 hm
      have hkn := Polynomial.le_natDegree_of_mem_supp k hk
      have he' : (k : ℤ) = a - n := he
      exact_mod_cast (show a ≤ (p.natDegree : ℤ) + n by omega)
  rw [leadingCoeff, hd, Function.leftInverse_invFun WithBot.coe_injective (_ + n), hc]
  rfl

/-- A polynomial with unit leading coefficient remains regular in the Laurent polynomial
ring, by clearing the negative exponents of a putative annihilator. -/
theorem isRegular_toLaurent_of_isUnit_leadingCoeff {p : Polynomial R}
    (hp : IsUnit p.leadingCoeff) : IsRegular p.toLaurent := by
  apply (Commute.isRegular_iff (fun q ↦ Commute.all p.toLaurent q)).2
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro q hq
  obtain ⟨n, r, hr⟩ := exists_T_pow q
  have hpr : p * r = 0 := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hr, ← mul_assoc, hq, zero_mul, map_zero]
  have hr0 := (Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hp).1 hpr
  have hz : q * T n = 0 := by simpa [hr0] using hr.symm
  exact (isUnit_T n).isRegular.right.mul_right_eq_zero_iff.1 hz

/-- Unit highest coefficient implies regularity for a Laurent polynomial over any
commutative ring, without a domain hypothesis. -/
theorem isRegular_of_isUnit_leadingCoeff {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsRegular p := by
  induction p using induction_on_mul_T with
  | mul_T p n =>
    rw [leadingCoeff_toLaurent_mul_T] at hp
    exact (isRegular_toLaurent_of_isUnit_leadingCoeff hp).mul (isUnit_T _).isRegular

/-- A Laurent polynomial with unit highest coefficient stays regular after any coefficient
homomorphism, including maps to a zero ring or a ring with zero divisors. -/
theorem isRegular_mapRingHom_of_isUnit_leadingCoeff (φ : R →+* S)
    {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) :
    IsRegular (mapRingHom ℤ φ p) := by
  cases subsingleton_or_nontrivial S
  · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  apply isRegular_of_isUnit_leadingCoeff
  rw [leadingCoeff_mapRingHom_of_ne_zero WithBot.coe_injective φ (hp.map φ).ne_zero]
  exact hp.map φ

end LaurentPolynomial
