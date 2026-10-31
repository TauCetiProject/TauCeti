/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Evaluating multivariate polynomials at dual numbers

Evaluating a polynomial `p` over `R` at the point of `R[ε]`, `ε² = 0`, whose coordinate `i` is
`ε` and whose other coordinates are `0` reads off two coefficients of `p`: its constant
coefficient and its coefficient of the variable `Xᵢ`,

  `p(ε eᵢ) = p(0) + (coefficient of Xᵢ in p) ε`.

As this evaluation is a ring homomorphism, it extracts the linear coefficient of `Xᵢ` from an
element that is only known through a universal property, such as the image of an element of the
Lazard ring in a polynomial ring.

More generally, evaluating `p` at `v + ε w` gives `p(v) + ε ∑ⱼ wⱼ ∂ⱼp(v)`, so derivatives of
polynomials can be computed as values over the dual numbers.

## Main results

* `MvPolynomial.aeval_single_eps`: `p(ε eᵢ) = p(0) + (coefficient of Xᵢ in p) ε`.
* `MvPolynomial.aeval_inl_add_inr`: `p(v + ε w) = p(v) + ε ∑ⱼ wⱼ ∂ⱼp(v)`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- **Evaluation at a dual-number point.** Evaluating a polynomial at `v + ε w`, where `ε² = 0`,
gives its value at `v` plus `ε` times its derivative at `v` in the direction `w`. -/
theorem aeval_inl_add_inr [Fintype σ] (f : MvPolynomial σ R) (v w : σ → R) :
    aeval (fun j ↦ TrivSqZeroExt.inl (v j) + TrivSqZeroExt.inr (w j) :
        σ → TrivSqZeroExt R R) f =
      TrivSqZeroExt.inl (eval v f) + TrivSqZeroExt.inr (∑ j, w j * eval v (pderiv j f)) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    simp only [map_add, hp, hq, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add,
      Finset.sum_add_distrib, mul_add]
    abel
  | mul_X p n hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        add_zero, zero_add]
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X,
        Pi.single_apply, mul_add, Finset.sum_add_distrib]
      simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, Finset.sum_mul]
      rw [mul_comm (eval v p)]
      congr 1
      exact Finset.sum_congr rfl fun _ _ ↦ by ring

variable [DecidableEq σ]

/-- Evaluating `p` at the point `ε eᵢ` of the dual numbers gives
`p(0) + (coefficient of Xᵢ in p) ε`. -/
theorem aeval_single_eps (i : σ) (p : MvPolynomial σ R) :
    aeval (Pi.single i (DualNumber.eps : DualNumber R)) p =
      algebraMap R (DualNumber R) (constantCoeff p) +
        p.coeff (Finsupp.single i 1) • DualNumber.eps := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, constantCoeff_C, coeff_C,
      ite_eq_right (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_smul, add_zero]
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, map_add]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, add_smul]
    abel
  | mul_X p k hp =>
    rw [map_mul, hp, aeval_X, coeff_mul_X', map_mul, constantCoeff_X, mul_zero, map_zero,
      zero_add]
    by_cases hk : k = i
    · subst hk
      ext <;> simp [constantCoeff_eq, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [hk]

end MvPolynomial
