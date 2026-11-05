/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Product densities on word spaces

Given weights `p : ι → R` on an alphabet, the product density `TauCeti.productDensity p` is the
diagonal operator on the word space `(Fin n → ι) →₀ R` multiplying the basis word `w` by the
product `∏ i, p (w i)` of the weights of its letters. These are the tensor powers of the diagonal
operator with eigenvalues `p`, written in the canonical word basis, so no tensor products or
choice of basis are needed. They serve as the enhancements and densities of weighted traces of
braid and Hecke algebra representations on word spaces.

## Main definitions

* `TauCeti.productDensity`: the product density of a weight function on the word space.
-/

public section

open Finsupp

namespace TauCeti

variable {R : Type*} [CommSemiring R] {ι : Type*} {n : ℕ}

/-- The product density of the weights `p` on the word space: the basis word `w` is multiplied by
`∏ i, p (w i)`. -/
noncomputable def productDensity (p : ι → R) : Module.End R ((Fin n → ι) →₀ R) :=
  linearCombination R fun w ↦ (∏ i, p (w i)) • single w 1

/-- The product density acts diagonally in the word basis. -/
@[simp]
theorem productDensity_single_one (p : ι → R) (w : Fin n → ι) :
    productDensity p (single w 1) = (∏ i, p (w i)) • single w 1 := by
  simp [productDensity]

/-- The coefficient of a word after applying the product density is its original coefficient
multiplied by the product of the weights of its letters. -/
@[simp]
theorem productDensity_apply (p : ι → R) (v : (Fin n → ι) →₀ R) (w : Fin n → ι) :
    productDensity p v w = (∏ i, p (w i)) * v w := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ h₁ h₂ => simp [h₁, h₂, mul_add]
  | single u r =>
    rw [← smul_single_one, map_smul, productDensity_single_one]
    by_cases h : u = w
    · subst w
      simp [mul_comm]
    · simp [h]

/-- The product density of the constant weight one is the identity. -/
@[simp]
theorem productDensity_one : productDensity (n := n) (1 : ι → R) = 1 := by
  refine LinearMap.ext fun v ↦ Finsupp.ext fun w ↦ ?_
  simp

/-- Composing product densities multiplies their weights. -/
theorem productDensity_mul (p p' : ι → R) :
    productDensity (n := n) p * productDensity p' = productDensity (p * p') := by
  refine LinearMap.ext fun v ↦ Finsupp.ext fun w ↦ ?_
  simp [mul_apply_eq_comp, ← mul_assoc, Finset.prod_mul_distrib]

end TauCeti
