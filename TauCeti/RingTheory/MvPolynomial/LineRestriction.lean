/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Top coefficients of affine line restrictions

Restricting a multivariate polynomial to an affine line does not increase its total degree.
Its coefficient in the original top degree is the top homogeneous component evaluated at
the direction, independently of the starting point. The coefficient homomorphism may take
values in another commutative semiring, so the starting point can itself consist of polynomial
variables. This gives constant leading coefficients for generic shears.
-/

public section

namespace MvPolynomial

open scoped BigOperators

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Restriction to a line through the origin sends a monomial to a monomial of its total
degree, with coefficient given by evaluation at the direction. -/
theorem aeval_C_mul_X_monomial (v : σ → R) (d : σ →₀ ℕ) (r : R) :
    aeval (fun i ↦ Polynomial.C (v i) * Polynomial.X) (monomial d r) =
      Polynomial.monomial d.degree (eval v (monomial d r)) := by
  simp only [aeval_monomial, Polynomial.algebraMap_apply, eval_monomial, Finsupp.prod,
    mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod,
    Finsupp.degree_apply]
  rw [Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Polynomial.C_mul_X_pow_eq_monomial]

/-- The coefficient of a line restriction is the homogeneous component evaluated at its
direction. -/
@[simp]
theorem coeff_aeval_C_mul_X (p : MvPolynomial σ R) (v : σ → R) (m : ℕ) :
    (aeval (fun i ↦ Polynomial.C (v i) * Polynomial.X) p).coeff m =
      eval v (homogeneousComponent m p) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, Polynomial.finsetSum_coeff]
  simp only [aeval_C_mul_X_monomial, Polynomial.coeff_monomial,
    homogeneousComponent_of_mem (isHomogeneous_monomial _ _)]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases h : d.degree = m
  · simp [h]
  · simp [h, Ne.symm h]

/-- Evaluation of the affine-line restriction is evaluation at the corresponding point. -/
@[simp]
theorem eval_aeval_C_add_C_mul_X (p : MvPolynomial σ R) (a v : σ → R) (t : R) :
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).eval t =
      eval (a + t • v) p := by
  have heq :
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).eval t =
        aeval (fun i ↦ a i + v i * t) p := by
    have h := comp_aeval_apply
      (f := fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)
      (Polynomial.aeval t : Polynomial R →ₐ[R] R) p
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at h
    simpa only [Polynomial.coe_aeval_eq_eval] using h
  have hpoint : (fun i ↦ a i + v i * t) = a + t • v := by
    funext i
    simp [mul_comm]
  rw [heq, aeval_eq_eval, hpoint]

/-- Restriction to an affine line, after changing coefficients, has degree at most the original
total degree. -/
theorem natDegree_eval₂_C_add_C_mul_X_le (p : MvPolynomial σ R) (f : R →+* S)
    (a v : σ → S) :
    (eval₂Hom (Polynomial.C.comp f)
      (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).natDegree ≤
        p.totalDegree := by
  simpa only [aeval_def, Polynomial.algebraMap_eq, eval₂_map, coe_eval₂Hom, mul_one] using
    aeval_natDegree_le (map f p)
      (by classical exact Finset.sup_mono (support_map_subset f p))
      (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)
      (n := 1) (fun i ↦ by
        simpa only [add_comm] using
          (Polynomial.natDegree_linear_le (a := v i) (b := a i)))

/-- At any degree bounding the total degree, an affine line restriction has coefficient equal
to the homogeneous component evaluated at its direction. The starting point does not enter. -/
theorem coeff_eval₂_C_add_C_mul_X_of_totalDegree_le (p : MvPolynomial σ R)
    (f : R →+* S) (a v : σ → S) {n : ℕ} (hn : p.totalDegree ≤ n) :
    (eval₂Hom (Polynomial.C.comp f)
      (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff n =
        eval₂ f v (homogeneousComponent n p) := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, Polynomial.finsetSum_coeff]
  conv_rhs => rw [p.as_sum, map_sum, eval₂_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdn : d.degree ≤ n := (le_totalDegree hd).trans hn
  by_cases heq : d.degree = n
  · rw [homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), ite_eq_left heq.symm,
      eval₂Hom_monomial, RingHom.comp_apply, Polynomial.coeff_C_mul, eval₂_monomial, ← heq]
    congr 1
    rw [Finsupp.degree_apply, Finsupp.prod,
      Polynomial.coeff_prod_sum_eq_of_natDegree_le]
    · apply Finset.prod_congr rfl
      intro i hi
      simpa [add_comm] using (Polynomial.coeff_pow_of_natDegree_le (m := d i)
        (Polynomial.natDegree_linear_le (a := v i) (b := a i)))
    · intro i hi
      exact Polynomial.natDegree_pow_le.trans (by
        simpa only [add_comm, mul_one] using
          Nat.mul_le_mul_left (d i)
            (Polynomial.natDegree_linear_le (a := v i) (b := a i)))
  · rw [homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), ite_eq_right (Ne.symm heq),
      eval₂_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_eval₂_C_add_C_mul_X_le (monomial d (p.coeff d)) f a v).trans_lt
        ((totalDegree_monomial_le _ _).trans_lt (lt_of_le_of_ne hdn heq)))

section Shear

variable {n : ℕ}

/-- The algebra homomorphism reading a polynomial in coordinate `i` after the shear that
adds `a j` times that coordinate to each of the other coordinates. The coefficients are
polynomials in those remaining coordinates, indexed by `i.succAbove`. -/
noncomputable def shearToPolynomial (i : Fin (n + 1)) (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  aeval (i.insertNth Polynomial.X
    (fun j ↦ Polynomial.C (X j) + Polynomial.C (C (a j)) * Polynomial.X))

/-- The substitution defining the sheared polynomial. -/
theorem shearToPolynomial_def (p : MvPolynomial (Fin (n + 1)) R)
    (i : Fin (n + 1)) (a : Fin n → R) :
    shearToPolynomial i a p = eval₂Hom (Polynomial.C.comp C) (i.insertNth Polynomial.X
      (fun j ↦ Polynomial.C (X j) + Polynomial.C (C (a j)) * Polynomial.X)) p :=
  (rfl)

/-- The distinguished variable becomes the univariate polynomial variable. -/
@[simp]
theorem shearToPolynomial_X (i : Fin (n + 1)) (a : Fin n → R) :
    shearToPolynomial i a (X i : MvPolynomial (Fin (n + 1)) R) = Polynomial.X := by
  simp [shearToPolynomial_def]

/-- Each remaining variable acquires its prescribed multiple of the distinguished variable. -/
@[simp]
theorem shearToPolynomial_X_succAbove (i : Fin (n + 1)) (a : Fin n → R) (j : Fin n) :
    shearToPolynomial i a (X (i.succAbove j) : MvPolynomial (Fin (n + 1)) R) =
      Polynomial.C (X j) + Polynomial.C (C (a j)) * Polynomial.X := by
  simp [shearToPolynomial_def]

/-- Evaluating the sheared polynomial at a base point and a height is evaluation of the
original polynomial at the sheared point. -/
@[simp]
theorem eval₂_shearToPolynomial (p : MvPolynomial (Fin (n + 1)) R)
    (i : Fin (n + 1)) (a y : Fin n → R) (t : R) :
    Polynomial.eval₂ (eval y) t (shearToPolynomial i a p) =
      eval (i.insertNth t (y + t • a)) p := by
  rw [shearToPolynomial_def, ← Polynomial.coe_eval₂RingHom, map_eval₂Hom]
  have hC : (Polynomial.eval₂RingHom (eval y) t).comp (Polynomial.C.comp C) =
      RingHom.id R := by
    ext c
    simp
  rw [hC, coe_eval₂Hom, eval₂_id]
  congr 2
  funext k
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · simp only [Fin.insertNth_apply_same, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  · simp only [Fin.insertNth_apply_succAbove, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      eval_X, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem shear_variables (i : Fin (n + 1)) (a : Fin n → R) :
    i.insertNth Polynomial.X
        (fun j ↦ Polynomial.C (X j) + Polynomial.C (C (a j)) * Polynomial.X) =
      (fun k ↦ Polynomial.C (i.insertNth (α := fun _ ↦ MvPolynomial (Fin n) R) 0 X k) +
        Polynomial.C (C (i.insertNth (α := fun _ ↦ R) 1 a k)) * Polynomial.X) := by
  funext k
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k <;> simp

/-- The degree after shearing in the distinguished coordinate is bounded by the original
total degree. -/
theorem natDegree_shearToPolynomial_le (p : MvPolynomial (Fin (n + 1)) R)
    (i : Fin (n + 1)) (a : Fin n → R) :
    (shearToPolynomial i a p).natDegree ≤ p.totalDegree := by
  rw [shearToPolynomial_def, shear_variables]
  exact p.natDegree_eval₂_C_add_C_mul_X_le C _ _

/-- The coefficient in the original total degree after a shear is constant in the remaining
variables: it is the top homogeneous part evaluated at the direction `i.insertNth 1 a`,
with 1 in coordinate `i` and `a` in the remaining coordinates. -/
theorem coeff_shearToPolynomial_totalDegree (p : MvPolynomial (Fin (n + 1)) R)
    (i : Fin (n + 1)) (a : Fin n → R) :
    (shearToPolynomial i a p).coeff p.totalDegree =
      C (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)) := by
  rw [shearToPolynomial_def, shear_variables,
    coeff_eval₂_C_add_C_mul_X_of_totalDegree_le p C _ _ le_rfl]
  simpa only [RingHom.comp_id, eval₂_id] using
    (hom_eval₂ (homogeneousComponent p.totalDegree p) (RingHom.id R) C
      (i.insertNth 1 a)).symm

/-- A nonvanishing top homogeneous part in the shear direction makes the degree in the
distinguished coordinate equal to the original total degree. -/
theorem natDegree_shearToPolynomial_eq_of_eval_ne_zero
    (p : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) (a : Fin n → R)
    (ha : eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p) ≠ 0) :
    (shearToPolynomial i a p).natDegree = p.totalDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (p.natDegree_shearToPolynomial_le i a)
  simpa only [coeff_shearToPolynomial_totalDegree, ne_eq, C_eq_zero] using ha

/-- On a good shear direction the leading coefficient is the nonzero constant obtained by
evaluating the top homogeneous component. -/
theorem leadingCoeff_shearToPolynomial_of_eval_ne_zero
    (p : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) (a : Fin n → R)
    (ha : eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p) ≠ 0) :
    (shearToPolynomial i a p).leadingCoeff =
      C (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)) := by
  rw [Polynomial.leadingCoeff, p.natDegree_shearToPolynomial_eq_of_eval_ne_zero i a ha,
    coeff_shearToPolynomial_totalDegree]

end Shear

end MvPolynomial
