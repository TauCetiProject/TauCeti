/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Detecting ambient order along affine lines

For a polynomial of finite ambient order at a point over an infinite domain, there is a
direction along which its restriction has exactly that order. The coefficient of degree `m`
on a line is the value of the degree-`m` homogeneous Taylor component at the direction.
Thus the good directions are detected by a nonzero polynomial, rather than assumed to exist.

These coefficient formulas supply the algebraic input for choosing uniform directions in
families of constant ambient order, and hence for analytic preparation of discriminants.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  Sections 2–3.
-/

public section

namespace MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

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

/-- Translating the polynomial first gives the restriction to an affine line. -/
theorem aeval_C_add_C_mul_X_eq (p : MvPolynomial σ R) (a v : σ → R) :
    aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p =
      aeval (fun i ↦ Polynomial.C (v i) * Polynomial.X) (taylor a p) := by
  rw [taylor_apply, ← AlgHom.comp_apply]
  congr 1
  ext i
  simp [add_comm]

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

/-- The coefficients of an affine-line restriction are the homogeneous Taylor components
evaluated at the direction. -/
@[simp]
theorem coeff_aeval_C_add_C_mul_X (p : MvPolynomial σ R) (a v : σ → R) (m : ℕ) :
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff m =
      eval v (homogeneousComponent m (taylor a p)) := by
  rw [aeval_C_add_C_mul_X_eq, coeff_aeval_C_mul_X]

/-- Terms below the ambient order vanish in every affine-line restriction. -/
theorem coeff_aeval_C_add_C_mul_X_eq_zero (p : MvPolynomial σ R) (a v : σ → R)
    {m : ℕ} (hm : (m : ℕ∞) < p.orderAt a) :
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff m = 0 := by
  rw [coeff_aeval_C_add_C_mul_X]
  have hzero : homogeneousComponent m (taylor a p) = 0 := by
    ext d
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · exact le_orderAt_iff.1 le_rfl d (hd ▸ hm)
    · rfl
  simp [hzero]

end CommSemiring

section InfiniteDomain

variable [CommRing R] [IsDomain R] [Infinite R]

/-- A polynomial of ambient order `m` admits a line restriction that is nonzero and has
order exactly `m` at the line parameter zero. -/
theorem exists_natTrailingDegree_aeval_C_add_C_mul_X_eq (p : MvPolynomial σ R)
    (a : σ → R) {m : ℕ} (hm : p.orderAt a = m) :
    ∃ v : σ → R,
      aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p ≠ 0 ∧
      Polynomial.natTrailingDegree
        (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p) = m := by
  obtain ⟨⟨d, hd, hdm⟩, _⟩ := orderAt_eq_coe_iff.1 hm
  have hH : homogeneousComponent m (taylor a p) ≠ 0 := by
    intro hzero
    have := congrArg (fun q : MvPolynomial σ R ↦ q.coeff d) hzero
    simp [coeff_homogeneousComponent, hdm, hd] at this
  obtain ⟨v, hv⟩ : ∃ v, eval v (homogeneousComponent m (taylor a p)) ≠ 0 := by
    by_contra h
    apply hH
    exact MvPolynomial.funext (by simpa using h)
  have hc :
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff m ≠ 0 :=
    (coeff_aeval_C_add_C_mul_X p a v m) ▸ hv
  have hn : aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p ≠ 0 :=
    fun hzero ↦ hc (by simp [hzero])
  refine ⟨v, hn, le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc) ?_⟩
  exact Polynomial.le_natTrailingDegree hn fun k hk ↦
    coeff_aeval_C_add_C_mul_X_eq_zero p a v (by simpa [hm] using hk)

end InfiniteDomain


end MvPolynomial
