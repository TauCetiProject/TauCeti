/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Weighted homogeneity under substitution

Give the variable `i` the weight `w i`, and substitute for it a polynomial that is weighted
homogeneous of weight `w i` for weights `v` on the target variables. A weighted homogeneous
polynomial of weight `m` then becomes weighted homogeneous of weight `m` for the weights `v`. The
homogeneous case is `v = 1`: substituting polynomials homogeneous of degree `w i` turns a weighted
homogeneous polynomial of weight `m` into a homogeneous polynomial of degree `m`. In this case,
when the substitution is injective, the converse holds: a polynomial whose substitution is
homogeneous of degree `m` is itself weighted homogeneous of weight `m`.

The motivating substitution sends the variable `i` of `MvPolynomial (Fin n) R` to the elementary
symmetric polynomial `eᵢ₊₁`, which is homogeneous of degree `i + 1`
(`MvPolynomial.isHomogeneous_esymm`). By the fundamental theorem of symmetric polynomials it is
injective, so the expression of a homogeneous symmetric polynomial in the elementary symmetric
polynomials is weighted homogeneous for the weights `i + 1`. The coefficients of a product
`∏ (X - C Ψ)` of linear factors with homogeneous constant terms of a common degree `m` supply
such symmetric polynomials (`MvPolynomial.isHomogeneous_coeff_prod_X_sub_C`).

More generally, evaluating a weighted homogeneous polynomial of weight `m` at elements of the
graded pieces of weights `w i` of any graded algebra lands in its graded piece of weight `m`.
Conversely, the weighted homogeneous components of a polynomial over `R` are read off from the
substitution `X i ↦ X i * T ^ w i` into polynomials in an auxiliary variable `T`: the coefficient
of `T ^ n` is the component of weight `n`. This detects homogeneity of an ideal from its stability
under such substitutions, as for the ideal of relations of the Lazard ring.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.aeval_mem`: evaluation at elements of graded pieces of the
  weights of the variables preserves weighted homogeneity.
* `MvPolynomial.IsWeightedHomogeneous.aeval`: substituting polynomials that are weighted
  homogeneous of the weights of the variables preserves weighted homogeneity.
* `MvPolynomial.isWeightedHomogeneous_of_isHomogeneous_aeval`: the converse of the homogeneous
  case, for an injective substitution.
* `MvPolynomial.coeff_aeval_C_X_mul_X_pow`: the coefficient of `T ^ n` in the substitution
  `X i ↦ X i * T ^ w i` is the weighted homogeneous component of weight `n`.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Evaluating a polynomial that is weighted homogeneous of weight `m` at elements `g i` of the
graded pieces `𝒜 (w i)` of a graded algebra gives an element of `𝒜 m`. -/
theorem IsWeightedHomogeneous.aeval_mem {M A S : Type*} [AddCommMonoid M] [CommSemiring A]
    [Algebra R A] [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] {𝒜 : M → S}
    [SetLike.GradedMonoid 𝒜] {w : σ → M} {φ : MvPolynomial σ R} {m : M}
    (hφ : φ.IsWeightedHomogeneous w m) {g : σ → A} (hg : ∀ i, g i ∈ 𝒜 (w i)) :
    MvPolynomial.aeval g φ ∈ 𝒜 m := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => simpa using add_mem ihp ihq
  | monomial d r hr =>
    -- Write the weight of `d` as `0 + ∑ i, d i • w i` and `algebraMap R A r` as `r • 1`, matching
    -- the product of `r • 1 ∈ 𝒜 0` with `∏ i, g i ^ d i ∈ 𝒜 (∑ i, d i • w i)`.
    rw [aeval_monomial, ← hr, Finsupp.weight_apply, Finsupp.sum, ← zero_add (∑ _ ∈ _, _),
      Algebra.algebraMap_eq_smul_one]
    exact SetLike.mul_mem_graded (SMulMemClass.smul_mem r SetLike.GradedOne.one_mem)
      (SetLike.prod_pow_mem_graded 𝒜 w g d fun i _ ↦ hg i)

/-- Substituting, for each variable `i`, a polynomial that is weighted homogeneous of weight
`w i` for the weights `v` into a polynomial that is weighted homogeneous of weight `m` for the
weights `w` gives a polynomial that is weighted homogeneous of weight `m` for the weights `v`. -/
theorem IsWeightedHomogeneous.aeval {M : Type*} [AddCommMonoid M] {w : σ → M} {v : τ → M}
    {φ : MvPolynomial σ R} {m : M} (hφ : φ.IsWeightedHomogeneous w m) {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsWeightedHomogeneous v (w i)) :
    (MvPolynomial.aeval g φ).IsWeightedHomogeneous v m :=
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := R) (w := v)
  hφ.aeval_mem (𝒜 := weightedHomogeneousSubmodule R v) hg

/-- **Weighted homogeneous components as coefficients.** Substituting `X i * T ^ w i` for each
variable `X i` turns a polynomial into a polynomial in `T` whose coefficient of `Tⁿ` is its
weighted homogeneous component of weight `n`. -/
theorem coeff_aeval_C_X_mul_X_pow (w : σ → ℕ) (φ : MvPolynomial σ R) (n : ℕ) :
    (MvPolynomial.aeval (fun i ↦ Polynomial.C (X i) * Polynomial.X ^ w i) φ).coeff n =
      weightedHomogeneousComponent w n φ := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial d r =>
    -- Each factor `(X i * T ^ w i) ^ d i` contributes `T ^ (d i * w i)`.
    have h : MvPolynomial.aeval (fun i ↦ Polynomial.C (X i) * Polynomial.X ^ w i) (monomial d r) =
        Polynomial.C (monomial d r) * Polynomial.X ^ Finsupp.weight w d := by
      rw [aeval_monomial, monomial_eq]
      simp only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
        ← pow_mul', Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow,
        Polynomial.algebraMap_apply, algebraMap_eq, smul_eq_mul]
      ring
    rw [h, Polynomial.coeff_C_mul_X_pow, weightedHomogeneousComponent_of_mem
      (isWeightedHomogeneous_monomial w d r rfl)]
  | add p q hp hq => simp [hp, hq]

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
    (weightedHomogeneousComponent_isWeightedHomogeneous n φ).aeval hg
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
