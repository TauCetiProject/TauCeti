/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# The different of an odd-degree squarefree polynomial model

For `y² = f(x)` with `f` squarefree of positive odd degree, there is a unique place above
infinity, and it is rational. Away from characteristic two the different is the zero divisor
of `y` plus that place. In particular, every zero of `y` occurs with coefficient one. This
identifies the different itself, not just its degree, and applies over arbitrary constant
fields, without requiring the roots of `f` to be rational.

This gives an explicit branch divisor for odd-degree hyperelliptic models, including the
genus-two model `y² = x⁵ - 1`.

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
variable [FiniteDimensional (RatFunc k) F]

/-- In a squarefree polynomial model of odd degree, every place above infinity is totally
ramified. This also holds in characteristic two. -/
theorem Place.isTotallyRamified_of_sq_eq_of_odd {f : k[X]} (hf : Squarefree f)
    (hodd : Odd f.natDegree) {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f))
    {P : Place k F} (hP : P.restrict k (RatFunc k) = Place.infty k) :
    P.IsTotallyRamified (RatFunc k) := by
  refine Place.isTotallyRamified_of_pow_eq_of_gcd_ord_eq_one k (RatFunc k)
    (finrank_ratFunc_eq_two_of_sq_eq hf hodd.pos hgen hy) hy two_ne_zero ?_
  simp only [hP, Place.ord_infty, RatFunc.intDegree_polynomial, Int.gcd_neg,
    Int.gcd_natCast_natCast]
  exact hodd.coprime_two_left.gcd_eq_one

/-- An odd-degree squarefree polynomial model has a unique place above infinity; that place
has degree one. No separability or characteristic assumption is needed. -/
theorem Place.existsUnique_restrict_eq_infty_of_sq_eq_of_odd {f : k[X]}
    (hf : Squarefree f) (hodd : Odd f.natDegree) {y : F}
    (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) :
    ∃ P : Place k F, P.restrict k (RatFunc k) = Place.infty k ∧ P.degree = 1 ∧
      ∀ Q : Place k F, Q.restrict k (RatFunc k) = Place.infty k → Q = P := by
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  obtain ⟨P, hP⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc k) hF (Place.infty k)
  -- Eliminate the lambda in the surjectivity statement before rewriting the restriction.
  have hP : P.restrict k (RatFunc k) = Place.infty k := hP
  have htot := P.isTotallyRamified_of_sq_eq_of_odd hf hodd hgen hy hP
  refine ⟨P, hP, ?_, fun Q hQ ↦ Place.eq_of_isTotallyRamified k (RatFunc k) htot
    (hQ.trans hP.symm)⟩
  rw [Place.degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k), hP,
    Place.degree_infty, Place.relativeDegree_eq_one_of_isTotallyRamified k (RatFunc k) htot]

variable [Algebra.IsSeparable (RatFunc k) F]

/-- **The different of an odd-degree squarefree polynomial model**: away from characteristic
two, `Diff(F/k(x)) = (y)₀ + P∞`. The zero divisor includes the closed points over all irreducible
factors of `f`, not just its roots in the constant field. -/
theorem different_ratFunc_eq_zeros_add_of_sq_eq_of_odd (h2 : (2 : k) ≠ 0)
    {f : k[X]} (hf : Squarefree f) (hodd : Odd f.natDegree) {y : Fˣ}
    (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f))
    {P : Place k F} (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Divisor.different k F (IsFunctionField.ratFunc k) =
      Divisor.zeros (isFunctionField_iff_functionField.mpr inferInstance) y +
        WeilDivisor.ofPoint P := by
  have htot := P.isTotallyRamified_of_sq_eq_of_odd hf hodd hgen hy hP
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
    norm_num [hnot]
    norm_num at hord
    omega
  · have hQP : Q ≠ P := fun h ↦ Place.adicOfIrreducible_ne_infty hq
      (hQ.symm.trans ((congrArg (fun R : Place k F ↦ R.restrict k (RatFunc k)) h).trans hP))
    have he := Place.ramificationIdx_eq_of_pow_eq_of_prime k (RatFunc k) (P' := Q)
      Nat.prime_two hgen hy (by exact_mod_cast h2) (RatFunc.algebraMap_ne_zero hf.ne_zero)
    rw [hQ, Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf] at he hord ⊢
    rw [WeilDivisor.coeff_ofPoint_of_ne hQP]
    by_cases hqf : q ∣ f
    · have he2 : Place.ramificationIdx (RatFunc k) Q = 2 := by simpa [hqf] using he
      simp [hqf, he2] at hord ⊢
      omega
    · simp [hqf] at hord ⊢
      omega

/-- **The different as a sum of distinct closed points**: the zeros of `y` in an odd-degree
squarefree polynomial model each contribute once, together with the unique place at infinity.
No splitting assumption on the polynomial over the constant field is needed. -/
theorem different_ratFunc_eq_sum_ofPoint_add_of_sq_eq_of_odd (h2 : (2 : k) ≠ 0)
    {f : k[X]} (hf : Squarefree f) (hodd : Odd f.natDegree) {y : Fˣ}
    (hgen : (RatFunc k)⟮(y : F)⟯ = ⊤)
    (hy : (y : F) ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f))
    {P : Place k F} (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Divisor.different k F (IsFunctionField.ratFunc k) =
      (∑ Q ∈ (Divisor.zeros (isFunctionField_iff_functionField.mpr inferInstance) y).support,
        WeilDivisor.ofPoint Q) + WeilDivisor.ofPoint P := by
  classical
  let hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  have hdiff := different_ratFunc_eq_zeros_add_of_sq_eq_of_odd h2 hf hodd hgen hy hP
  rw [hdiff]
  congr 1
  refine (WeilDivisor.eq_sum_coeff_smul_ofPoint (Divisor.zeros hF y)).trans ?_
  refine Finset.sum_congr rfl fun Q hQ ↦ ?_
  have hc := congrArg (fun D : Divisor k F ↦ D.coeff Q) hdiff
  rw [Divisor.coeff_different, WeilDivisor.coeff_add, Divisor.coeff_zeros] at hc
  have hd := Place.differentExponent_eq_of_pow_eq_of_prime k (RatFunc k) (P' := Q)
    Nat.prime_two hgen hy (by exact_mod_cast h2) (RatFunc.algebraMap_ne_zero hf.ne_zero)
  have hdle : Place.differentExponent k (RatFunc k) Q ≤ 1 := by
    rw [hd]
    split_ifs <;> omega
  have hpnonneg : 0 ≤ (WeilDivisor.ofPoint P).coeff Q := by
    by_cases hQP : Q = P
    · subst Q
      simp
    · simp [WeilDivisor.coeff_ofPoint_of_ne hQP]
  have hpos := (Divisor.mem_support_zeros_iff hF).mp hQ
  have hcoeff : (Divisor.zeros hF y).coeff Q = 1 := by
    rw [Divisor.coeff_zeros]
    omega
  rw [hcoeff, one_smul]

end TauCeti
