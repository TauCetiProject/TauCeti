/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus.Basic
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# The different of an odd-degree squarefree polynomial model

For `y² = f(x)` with `f` squarefree of positive odd degree, there is a unique place above
infinity, and it is rational. Away from characteristic two the different is the zero divisor
of `y` plus that place. In particular, every zero of `y` occurs with coefficient one. This
identifies the different itself, not just its degree, and applies over arbitrary constant
fields, without requiring the roots of `f` to be rational.

This gives an explicit ramification divisor (the different) for odd-degree hyperelliptic
models, including the genus-two model `y² = x⁵ - 1`.

## References

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Proposition 6.2.3 and Example 3.7.6.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra (RatFunc k) F]
variable [Algebra k F] [IsScalarTower k (RatFunc k) F]

/-- **The different of an odd-degree squarefree polynomial model**: away from characteristic
two, `Diff(F/k(x)) = (y)₀ + P∞`. The zero divisor includes the closed points over all irreducible
factors of `f`, not just its roots in the constant field. -/
theorem different_ratFunc_eq_zeros_add_of_sq_eq_of_odd (h2 : (2 : k) ≠ 0)
    {f : k[X]} (hf : Squarefree f) (hodd : Odd f.natDegree) {y : Fˣ}
    (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f))
    {P : Place k F} :
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hodd.pos hgen hy).1
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hodd.pos hgen hy).2
    P.restrict k (RatFunc k) = Place.infty k →
    Divisor.different k F (IsFunctionField.ratFunc k) =
      Divisor.zeros (isFunctionField_iff_functionField.mpr inferInstance) y +
        WeilDivisor.ofPoint P := by
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq h2 hf hodd.pos hgen hy
  intro hP
  have htot := P.isTotallyRamified_of_sq_eq_of_odd hodd hgen hy hP
  refine WeilDivisor.ext fun Q ↦ ?_
  have hord := congrArg Q.ord hy
  rw [Q.ord_pow, Place.ord_algebraMap_restrict k (RatFunc k)] at hord
  rw [Divisor.coeff_different, WeilDivisor.coeff_add, Divisor.coeff_zeros,
    Place.differentExponent_eq_of_pow_eq_of_prime k (RatFunc k) Nat.prime_two hgen hy
      (by exact_mod_cast h2) (RatFunc.algebraMap_ne_zero hf.ne_zero)]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible (Q.restrict k (RatFunc k)) with
    hQ | ⟨q, hq, hQ⟩
  · have hQP : Q = P := Place.eq_of_isTotallyRamified k (RatFunc k) htot
      (hQ.trans hP.symm)
    have he : Place.ramificationIdx (RatFunc k) Q = 2 := by
      rw [hQP, ← finrank_ratFunc_eq_two_of_sq_eq hf hodd.pos hgen hy]
      exact (Place.isTotallyRamified_iff (RatFunc k)).mp htot
    rw [hQ, Place.ord_infty, RatFunc.intDegree_polynomial, he] at hord
    rw [hQ, Place.ord_infty, RatFunc.intDegree_polynomial,
      hQP, WeilDivisor.coeff_ofPoint_self]
    have hmod := Nat.odd_iff.mp hodd
    have hnot : ¬(2 : ℤ) ∣ -(f.natDegree : ℤ) := by omega
    rw [hQP] at hord
    simp only [Nat.cast_ofNat, ite_eq_right hnot]
    omega
  · have hQP : Q ≠ P := fun h ↦ Place.adicOfIrreducible_ne_infty hq
      (hQ.symm.trans ((congrArg (fun R : Place k F ↦ R.restrict k (RatFunc k)) h).trans hP))
    have he := Place.ramificationIdx_eq_of_pow_eq_of_prime k (RatFunc k) (P' := Q)
      Nat.prime_two hgen hy (by exact_mod_cast h2) (RatFunc.algebraMap_ne_zero hf.ne_zero)
    rw [hQ, Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf] at he hord ⊢
    rw [WeilDivisor.coeff_ofPoint_of_ne hQP]
    by_cases hqf : q ∣ f
    · have hnot : ¬(2 : ℤ) ∣ 1 := by omega
      have he2 : Place.ramificationIdx (RatFunc k) Q = 2 := by
        simpa only [ite_eq_left hqf, Nat.cast_ofNat, ite_eq_right hnot] using he
      simp only [ite_eq_left hqf, he2, Nat.cast_ofNat, ite_eq_right hnot, mul_one,
        add_zero] at hord ⊢
      omega
    · simp only [ite_eq_right hqf, dvd_zero, ite_true, mul_zero, add_zero] at hord ⊢
      omega

/-- Every zero of `y` in a squarefree polynomial model has multiplicity one,
in every degree and characteristic. -/
theorem Divisor.coeff_zeros_eq_one_of_sq_eq (hF : IsFunctionField k F)
    {f : k[X]} (hf : Squarefree f) {y : Fˣ}
    (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f))
    {Q : Place k F} (hQ : Q ∈ (zeros hF y).support) :
    (zeros hF y).coeff Q = 1 := by
  have : FunctionField k F := isFunctionField_iff_functionField.mp hF
  have hpos := (mem_support_zeros_iff hF).mp hQ
  have hord := congrArg Q.ord hy
  rw [Q.ord_pow, Place.ord_algebraMap_restrict k (RatFunc k)] at hord
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible (Q.restrict k (RatFunc k)) with
    hQinf | ⟨q, hq, hQadic⟩
  · rw [hQinf, Place.ord_infty, RatFunc.intDegree_polynomial] at hord
    have hnonpos : (Place.ramificationIdx (RatFunc k) Q : ℤ) * -(f.natDegree : ℤ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (neg_nonpos.mpr (Nat.cast_nonneg _))
    simp only [Nat.cast_ofNat] at hord
    omega
  · rw [hQadic, Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf] at hord
    have hqf : q ∣ f := by
      by_contra hqf
      rw [ite_eq_right hqf, mul_zero] at hord
      omega
    have hdeg : 0 < f.natDegree := lt_of_lt_of_le
      (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hq))
      (natDegree_le_of_dvd hqf hf.ne_zero)
    have hrank := finrank_ratFunc_eq_two_of_sq_eq hf hdeg hgen hy
    have he := Place.ramificationIdx_eq_of_pow_eq_of_gcd_ord_eq_one k (RatFunc k)
      (P' := Q) hrank hy two_ne_zero (by
        rw [hQadic, Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf, ite_eq_left hqf]
        exact Int.gcd_one_right _)
    rw [ite_eq_left hqf, he] at hord
    rw [coeff_zeros]
    omega

/-- **The different as the divisor of distinct closed points**: the zeros of `y` in an odd-degree
squarefree polynomial model each contribute once, together with the unique place at infinity.
No splitting assumption on the polynomial over the constant field is needed. -/
theorem different_ratFunc_eq_ofFinset_add_of_sq_eq_of_odd (h2 : (2 : k) ≠ 0)
    {f : k[X]} (hf : Squarefree f) (hodd : Odd f.natDegree) {y : Fˣ}
    (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f))
    {P : Place k F} :
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hodd.pos hgen hy).1
    letI := (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hodd.pos hgen hy).2
    P.restrict k (RatFunc k) = Place.infty k →
    Divisor.different k F (IsFunctionField.ratFunc k) =
      WeilDivisor.ofFinset
        (Divisor.zeros (isFunctionField_iff_functionField.mpr inferInstance) y).support +
          WeilDivisor.ofPoint P := by
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq h2 hf hodd.pos hgen hy
  intro hP
  classical
  let hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  have hdiff := different_ratFunc_eq_zeros_add_of_sq_eq_of_odd h2 hf hodd hgen hy hP
  rw [hdiff]
  congr 1
  refine WeilDivisor.ext fun Q ↦ ?_
  rw [WeilDivisor.coeff_ofFinset]
  by_cases hQ : Q ∈ (Divisor.zeros hF y).support
  · rw [ite_eq_left hQ]
    exact Divisor.coeff_zeros_eq_one_of_sq_eq hF hf hgen hy hQ
  · rw [ite_eq_right hQ]
    exact Finsupp.notMem_support_iff.mp hQ

end TauCeti
