/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Degrees
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Degrees of polynomial matrix expressions

Entrywise degree bounds add under matrix multiplication and bound the degrees of the entries
of the adjugate. For a linear substitution with polynomial matrix entries, these bounds control
the coefficients of the substituted monomials in the matrix parameters, rather than their
degree in the variables of the monomials.
-/

public section

open MvPolynomial

namespace Matrix

variable {R σ ι κ ν : Type*}

/-- Entrywise total-degree bounds add under matrix multiplication. -/
theorem totalDegree_mul_apply_le [CommSemiring R] [Fintype κ]
    {A : Matrix ι κ (MvPolynomial σ R)} {B : Matrix κ ν (MvPolynomial σ R)} {a b : ℕ}
    (hA : ∀ i j, (A i j).totalDegree ≤ a) (hB : ∀ i j, (B i j).totalDegree ≤ b) (i : ι) (j : ν) :
    ((A * B) i j).totalDegree ≤ a + b := by
  rw [Matrix.mul_apply]
  exact totalDegree_finsetSum_le fun k _ ↦
    (totalDegree_mul _ _).trans (Nat.add_le_add (hA i k) (hB k j))

/-- The entries of an ordered product of square polynomial matrices have degree at most the sum
of the individual entry bounds. -/
theorem totalDegree_list_prod_apply_le [CommSemiring R] [Fintype ι] [DecidableEq ι]
    {A : κ → Matrix ι ι (MvPolynomial σ R)} {d : κ → ℕ} (l : List κ)
    (hA : ∀ s ∈ l, ∀ i j, (A s i j).totalDegree ≤ d s) (i j : ι) :
    ((l.map A).prod i j).totalDegree ≤ (l.map d).sum := by
  induction l generalizing i j with
  | nil => by_cases h : i = j <;> simp [h]
  | cons s l ih =>
    simpa only [List.map_cons, List.prod_cons, List.sum_cons] using
      totalDegree_mul_apply_le (hA s (by simp))
        (ih fun t ht ↦ hA t (List.mem_cons_of_mem _ ht)) i j

/-- Entrywise degree bound for an adjugate of a square polynomial matrix. -/
theorem totalDegree_adjugate_apply_le [CommRing R] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MvPolynomial σ R)} {d : ℕ} (hA : ∀ i j, (A i j).totalDegree ≤ d)
    (i j : ι) : (A.adjugate i j).totalDegree ≤ Fintype.card ι * d := by
  rw [adjugate_apply]
  apply totalDegree_det_le
  intro r s
  by_cases h : r = j
  · subst r
    by_cases h' : i = s <;> simp [h']
  · simpa [Matrix.updateRow_ne h] using hA r s

end Matrix

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- For the linear substitution given by `A`, the coefficients of the image of `X^β` have
parameter degree at most `∑ i, β i * d i`, where row `i` of `A` has degree bounded by `d i`. -/
theorem totalDegree_coeff_linearSubst_monomial_le [Fintype τ]
    {A : Matrix τ τ (MvPolynomial σ R)} {d : τ → ℕ}
    (hA : ∀ i j, (A i j).totalDegree ≤ d i) (β γ : τ →₀ ℕ) :
    ((linearSubst A (monomial β 1)).coeff γ).totalDegree ≤ ∑ i, β i * d i := by
  classical
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_prod]
  refine totalDegree_coeff_finsetProd_le Finset.univ (d := fun i ↦ β i * d i) (fun i _ e ↦ ?_) γ
  simp only [map_pow]
  refine totalDegree_coeff_pow_le (fun t ↦ ?_) _ e
  rw [linearSubst_X, coeff_sum]
  refine totalDegree_finsetSum_le fun j _ ↦ ?_
  rw [C_mul_X_eq_monomial, coeff_monomial]
  split_ifs <;> simp [hA i j]

end MvPolynomial
