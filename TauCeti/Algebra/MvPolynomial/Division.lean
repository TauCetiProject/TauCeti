/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Divisibility and remainder by powers of a variable

A power `Xᵢ ^ k` of one variable of a multivariate polynomial ring divides `Xⱼ ^ l * p`, for a
different variable `Xⱼ`, exactly when it divides `p`: multiplying by `Xⱼ ^ l` shifts every exponent
vector in the support of `p` by `l` in the coordinate `j` only, which does not change the exponents
of `Xᵢ`. No hypothesis on the coefficient semiring is needed.

Dividing out or reducing modulo a monomial can only drop variables from `vars`, and reducing modulo
`Xᵢ` evaluates `Xᵢ` to `0` (`MvPolynomial.aeval_update_X_zero_eq_modMonomial`) and eliminates `i`
from `vars` (`MvPolynomial.notMem_vars_modMonomial_single`).

This is the divisibility input to the computation of the global sections of the twisting sheaves
`𝒪(n)` on projective space, where the two monomials are powers of two homogeneous coordinates, and
to variable elimination by minimal-exponent slicing in multihomogeneous polynomials.

## Main results

* `MvPolynomial.X_pow_dvd_X_pow_mul_iff`: for `i ≠ j`, `Xᵢ ^ k ∣ Xⱼ ^ l * p ↔ Xᵢ ^ k ∣ p`.
* `MvPolynomial.aeval_update_X_zero_eq_modMonomial`: setting `X i` to `0` computes the remainder
  `p.modMonomial (Finsupp.single i 1)`.
* `MvPolynomial.mem_support_modMonomial`, `MvPolynomial.support_modMonomial_subset`,
  `MvPolynomial.coeff_modMonomial_of_mem_support`: support and coefficient characterization of
  `modMonomial`.
* `MvPolynomial.vars_divMonomial_subset`, `MvPolynomial.vars_modMonomial_subset`,
  `MvPolynomial.notMem_vars_modMonomial_single`: variable-set bounds for monomial division and
  remainder.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- **A power of a variable divides a polynomial times a power of another variable iff it divides
the polynomial.** -/
theorem X_pow_dvd_X_pow_mul_iff {i j : σ} (hij : i ≠ j) {k l : ℕ} {p : MvPolynomial σ R} :
    X i ^ k ∣ X j ^ l * p ↔ X i ^ k ∣ p := by
  refine ⟨fun h ↦ ?_, fun h ↦ dvd_mul_of_dvd_right h _⟩
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero] at h ⊢
  ext m
  by_cases hm : Finsupp.single i k ≤ m
  · exact coeff_modMonomial_of_le _ hm
  -- the coefficient of `p` at `m` is that of `Xⱼ ^ l * p` at `m + l eⱼ`, which has the same
  -- exponent of `Xᵢ` as `m`
  have hm' : ¬Finsupp.single i k ≤ m + Finsupp.single j l := by
    simpa [Finsupp.single_le_iff, Finsupp.single_apply, hij.symm] using hm
  have h' := congrArg (fun q ↦ q.coeff (m + Finsupp.single j l)) h
  rw [coeff_modMonomial_of_not_le _ hm', X_pow_eq_monomial, add_comm m, coeff_monomial_mul,
    one_mul] at h'
  rw [coeff_modMonomial_of_not_le _ hm, h']
  simp

/-- An exponent vector lies in the support of `p.modMonomial s` if and only if it lies in the
support of `p` and is not bounded below by `s`. -/
theorem mem_support_modMonomial {p : MvPolynomial σ R} {s m : σ →₀ ℕ} :
    m ∈ (p.modMonomial s).support ↔ m ∈ p.support ∧ ¬ s ≤ m := by
  by_cases h : s ≤ m <;> simp [h]

/-- Taking the remainder modulo a monomial selects a subset of the support. -/
theorem support_modMonomial_subset (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (p.modMonomial s).support ⊆ p.support :=
  fun _ hm ↦ (mem_support_modMonomial.mp hm).1

/-- Every exponent in the support of `p.modMonomial s` has the same coefficient as in `p`. -/
theorem coeff_modMonomial_of_mem_support {p : MvPolynomial σ R} {s m : σ →₀ ℕ}
    (hm : m ∈ (p.modMonomial s).support) :
    (p.modMonomial s).coeff m = p.coeff m :=
  coeff_modMonomial_of_not_le p (mem_support_modMonomial.mp hm).2

/-- Dividing by a monomial does not introduce new variables. -/
theorem vars_divMonomial_subset (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (p.divMonomial s).vars ⊆ p.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨m, hm, hmj⟩ := hj
  rw [mem_support_iff, coeff_divMonomial, ← mem_support_iff] at hm
  exact ⟨s + m, hm, by simp [Finsupp.mem_support_iff] at hmj ⊢; omega⟩

/-- Taking the remainder modulo a monomial does not introduce new variables. -/
theorem vars_modMonomial_subset (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (p.modMonomial s).vars ⊆ p.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨m, hm, hmj⟩ := hj
  exact ⟨m, support_modMonomial_subset p s hm, hmj⟩

/-- Taking the remainder modulo `X i` eliminates `i` from the variables of `p`. -/
@[simp]
theorem notMem_vars_modMonomial_single (p : MvPolynomial σ R) (i : σ) :
    i ∉ (p.modMonomial (Finsupp.single i 1)).vars := by
  classical
  rw [mem_vars_iff_mem_support]
  rintro ⟨m, hm, hmi⟩
  refine (mem_support_modMonomial.mp hm).2 ?_
  rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
  exact Finsupp.mem_support_iff.mp hmi

/-- Evaluating `X i` to `0` and leaving every other variable unchanged computes the remainder
modulo `X i`. -/
theorem aeval_update_X_zero_eq_modMonomial [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    aeval (Function.update X i (0 : MvPolynomial σ R)) p = p.modMonomial (Finsupp.single i 1) := by
  conv_lhs => rw [← p.modMonomial_add_divMonomial_single i]
  rw [map_add, map_mul, aeval_X, Function.update_self, zero_mul, add_zero]
  -- Variable `i` does not occur in `p.modMonomial (Finsupp.single i 1)`, so `Function.update X i 0`
  -- agrees with `X` on its `vars`.
  conv_rhs => rw [← aeval_X_left_apply (p.modMonomial (Finsupp.single i 1))]
  rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  exact eval₂Hom_congr' rfl
    (fun j _ hj ↦ Function.update_of_ne (ne_of_mem_of_not_mem hj (by simp)) _ _) rfl

end MvPolynomial
