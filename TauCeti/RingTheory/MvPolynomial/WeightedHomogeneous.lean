/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Weighted homogeneity under substitution of homogeneous polynomials

Give the variable `i` the weight `w i`, and substitute for it a polynomial that is homogeneous of
degree `w i`. A weighted homogeneous polynomial of weight `m` then becomes a homogeneous
polynomial of degree `m`. When the substitution is injective the converse holds: a polynomial
whose substitution is homogeneous of degree `m` is itself weighted homogeneous of weight `m`.

The motivating substitution sends the variable `i` of `MvPolynomial (Fin n) R` to the elementary
symmetric polynomial `eᵢ₊₁`, which is homogeneous of degree `i + 1`
(`MvPolynomial.isHomogeneous_esymm`). By the fundamental theorem of symmetric polynomials it is
injective, so the expression of a homogeneous symmetric polynomial in the elementary symmetric
polynomials is weighted homogeneous for the weights `i + 1`. The coefficients of a product
`∏ (X - C Ψ)` of linear factors with homogeneous constant terms of a common degree `m` supply
such symmetric polynomials (`MvPolynomial.isHomogeneous_coeff_prod_X_sub_C`).

## Main results

* `MvPolynomial.IsWeightedHomogeneous.isHomogeneous_aeval`: substituting homogeneous polynomials
  of the weights turns weighted homogeneity into homogeneity.
* `MvPolynomial.isWeightedHomogeneous_of_isHomogeneous_aeval`: the converse, for an injective
  substitution.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Substituting, for each variable `i`, a polynomial homogeneous of degree `w i` into a
polynomial that is weighted homogeneous of weight `m` for the weights `w` gives a homogeneous
polynomial of degree `m`. -/
theorem IsWeightedHomogeneous.isHomogeneous_aeval {w : σ → ℕ} {φ : MvPolynomial σ R} {m : ℕ}
    (hφ : φ.IsWeightedHomogeneous w m) {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsHomogeneous (w i)) : (aeval g φ).IsHomogeneous m := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isHomogeneous_zero τ R m
  | add p q _ _ ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, Finsupp.prod, algebraMap_eq]
    have hprod := IsHomogeneous.prod d.support (fun i => g i ^ d i) (fun i => w i * d i)
      fun i _ => (hg i).pow (d i)
    convert (isHomogeneous_C τ r).mul hprod using 1
    rw [← hr, Finsupp.weight_apply, Finsupp.sum, zero_add]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

/-- **Weighted homogeneity from homogeneity of a substitution.** If `g i` is homogeneous of
degree `w i` for every variable `i` and substitution of the `g i` is injective, then a polynomial
whose substitution is homogeneous of degree `m` is weighted homogeneous of weight `m`. -/
theorem isWeightedHomogeneous_of_isHomogeneous_aeval {w : σ → ℕ} {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsHomogeneous (w i)) (hinj : Function.Injective (aeval (R := R) g))
    {φ : MvPolynomial σ R} {m : ℕ} (h : (aeval g φ).IsHomogeneous m) :
    φ.IsWeightedHomogeneous w m := by
  classical
  -- The substitution of the weight-`n` component of `φ` is homogeneous of degree `n`, so the
  -- degree-`m` part of the substitution of `φ` is the substitution of its weight-`m` component.
  set s := (weightedHomogeneousComponent_finsupp (w := w) φ).toFinset
  have hsum : ∑ n ∈ s, weightedHomogeneousComponent w n φ = φ := by
    rw [← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ),
      sum_weightedHomogeneousComponent]
  have hcomp (n : ℕ) : (aeval g (weightedHomogeneousComponent w n φ)).IsHomogeneous n :=
    (weightedHomogeneousComponent_isWeightedHomogeneous n φ).isHomogeneous_aeval hg
  have key : aeval g φ = aeval g (weightedHomogeneousComponent w m φ) := by
    calc aeval g φ = homogeneousComponent m (aeval g φ) := (homogeneousComponent_eq_self h).symm
      _ = ∑ n ∈ s, homogeneousComponent m (aeval g (weightedHomogeneousComponent w n φ)) := by
        conv_lhs => rw [← hsum]
        rw [map_sum, map_sum]
      _ = homogeneousComponent m (aeval g (weightedHomogeneousComponent w m φ)) := by
        refine Finset.sum_eq_single m (fun n _ hn => ?_) fun hm => ?_
        · simp [homogeneousComponent_of_mem (hcomp n), hn.symm]
        · have hzero : weightedHomogeneousComponent w m φ = 0 := by
            by_contra hne
            exact hm ((Set.Finite.mem_toFinset _).mpr hne)
          rw [hzero, map_zero, map_zero]
      _ = aeval g (weightedHomogeneousComponent w m φ) := homogeneousComponent_eq_self (hcomp m)
  rw [hinj key]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

end CommSemiring

end MvPolynomial
