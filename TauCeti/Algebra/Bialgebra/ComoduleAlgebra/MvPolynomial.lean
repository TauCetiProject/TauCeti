/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# Diagonal actions of diagonalizable groups on affine space

Let `G` be a commutative monoid and `w : σ → G` a family of weights. The polynomial ring
`MvPolynomial σ R` is a comodule algebra over the monoid algebra `R[G]`, with the coaction
sending the variable `X i` to `X i ⊗ [w i]` (`TauCeti.ComoduleAlgebra.mvPolynomialWeight`).
When `G` is a commutative group, this is the action of the diagonalizable group `D(G) = Spec R[G]`
on the affine space `𝔸^σ` in which `D(G)` scales the `i`th coordinate by the character `w i`. For
`G = Multiplicative ℤ`, so that `D(G)` is the multiplicative group `𝔾ₘ`, these are the linear
actions of `𝔾ₘ` on affine space with weights `w`.

A monomial `X^s` is a weight vector of weight `∏ i, w i ^ s i`
(`TauCeti.ComoduleAlgebra.mvPolynomialWeight_coact_monomial`), and a polynomial is invariant
exactly when every monomial in its support has weight `1`
(`TauCeti.ComoduleAlgebra.mem_coinvariants_mvPolynomialWeight_iff`). For `𝔾ₘ` acting on `𝔸²`
with weights `1` and `-1`, the invariants are the polynomials in `x y`
(`TauCeti.QuotientExamples.coinvariants_gm_one_neg_one`).

## Main declarations

* `TauCeti.ComoduleAlgebra.monomialWeight`: the weight of a monomial.
* `TauCeti.ComoduleAlgebra.mvPolynomialWeight`: the comodule algebra structure on
  `MvPolynomial σ R` over `R[G]` given by the weights `w`.
* `TauCeti.ComoduleAlgebra.mvPolynomialWeight_coact_monomial`: monomials are weight vectors.
* `TauCeti.ComoduleAlgebra.mem_coinvariants_mvPolynomialWeight_iff`: the invariants are the
  polynomials supported on monomials of weight `1`.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

open MvPolynomial

variable {R σ G : Type*} [CommSemiring R] [CommMonoid G]

/-- The weight `∏ i, w i ^ s i` of the monomial with exponent `s`. -/
noncomputable def monomialWeight (w : σ → G) (s : σ →₀ ℕ) : G :=
  s.prod fun i n ↦ w i ^ n

theorem monomialWeight_def (w : σ → G) (s : σ →₀ ℕ) :
    monomialWeight w s = s.prod fun i n ↦ w i ^ n := (rfl)

/-- The coaction with weights `w`, as an algebra homomorphism: it sends `X i` to `X i ⊗ [w i]`. -/
noncomputable def mvPolynomialWeightCoact (w : σ → G) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R ⊗[R] MonoidAlgebra R G :=
  aeval fun i ↦ X i ⊗ₜ[R] MonoidAlgebra.single (w i) 1

@[simp]
theorem mvPolynomialWeightCoact_X (w : σ → G) (i : σ) :
    mvPolynomialWeightCoact (R := R) w (X i) = X i ⊗ₜ[R] MonoidAlgebra.single (w i) 1 :=
  aeval_X _ _

/-- The coaction sends a monomial to itself tensored with its weight. -/
theorem mvPolynomialWeightCoact_monomial (w : σ → G) (s : σ →₀ ℕ) (c : R) :
    mvPolynomialWeightCoact w (monomial s c) =
      monomial s c ⊗ₜ[R] MonoidAlgebra.single (monomialWeight w s) 1 := by
  classical
  induction s using Finsupp.induction with
  | zero =>
    simp [mvPolynomialWeightCoact, monomialWeight_def, Algebra.TensorProduct.algebraMap_apply,
      MonoidAlgebra.one_def]
  | single_add i n s _ _ ih =>
    rw [monomial_single_add, map_mul, map_pow, mvPolynomialWeightCoact_X, ih,
      Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
      MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.single_mul_single, one_mul,
      monomialWeight_def, monomialWeight_def, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_single_index (by simp)]

/-- **The diagonal action with weights `w`** of the diagonalizable monoid `D(G) = Spec R[G]` on
the affine space `Spec (MvPolynomial σ R)`, as a comodule algebra structure: the coaction sends
`X i` to `X i ⊗ [w i]`.

This is not an instance, since it depends on the weights. -/
@[implicit_reducible]
noncomputable def mvPolynomialWeight (w : σ → G) :
    ComoduleAlgebra R (MonoidAlgebra R G) (MvPolynomial σ R) where
  coact := (mvPolynomialWeightCoact w).toLinearMap
  coassoc := by
    refine LinearMap.ext fun p ↦ ?_
    induction p using MvPolynomial.induction_on' with
    | monomial s c =>
      simp [mvPolynomialWeightCoact_monomial]
    | add p q hp hq => simp only [map_add, hp, hq]
  lTensor_counit_comp_coact := by
    refine LinearMap.ext fun p ↦ ?_
    induction p using MvPolynomial.induction_on' with
    | monomial s c =>
      simp [mvPolynomialWeightCoact_monomial]
    | add p q hp hq => simp only [map_add, hp, hq]
  coact_one := map_one (mvPolynomialWeightCoact w)
  coact_mul := map_mul (mvPolynomialWeightCoact w)

/-- **Monomials are weight vectors**: the monomial with exponent `s` has weight
`monomialWeight w s = ∏ i, w i ^ s i`. -/
theorem mvPolynomialWeight_coact_monomial (w : σ → G) (s : σ →₀ ℕ) (c : R) :
    letI := mvPolynomialWeight (R := R) w
    Comodule.coact (R := R) (C := MonoidAlgebra R G) (monomial s c) =
      monomial s c ⊗ₜ[R] MonoidAlgebra.single (monomialWeight w s) 1 :=
  mvPolynomialWeightCoact_monomial w s c

/-- **The invariants of a diagonal action** are the polynomials all of whose monomials have
weight `1`. -/
theorem mem_coinvariants_mvPolynomialWeight_iff (w : σ → G) {p : MvPolynomial σ R} :
    letI := mvPolynomialWeight (R := R) w
    p ∈ coinvariants R (MonoidAlgebra R G) (MvPolynomial σ R) ↔
      ∀ s ∈ p.support, monomialWeight w s = 1 := by
  classical
  let := mvPolynomialWeight (R := R) w
  refine ⟨fun hp s hs ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    -- Read off the coefficient of `X^s ⊗ [monomialWeight w s]` in the coaction of `p`.
    let F := (lcoeff R s).comp (LinearMap.tensorComponent (R := R) (M := MvPolynomial σ R)
      (Comodule.monoidCoeff R G (monomialWeight w s)))
    have h₁ : F (Comodule.coact (R := R) (C := MonoidAlgebra R G) p) = 0 := by
      rw [mem_coinvariants.1 hp]
      simp [F, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Ne.symm hne]
    have h₂ : F (Comodule.coact (R := R) (C := MonoidAlgebra R G) p) = p.coeff s := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum, map_sum, Finset.sum_eq_single s]
      · simp [F, mvPolynomialWeight_coact_monomial, MonoidAlgebra.coeff_single]
      · intro t _ hts
        simp [F, mvPolynomialWeight_coact_monomial, coeff_monomial, hts]
      · intro hs'
        exact absurd hs hs'
    exact (mem_support_iff.1 hs) (h₂.symm.trans h₁)
  · rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun s hs ↦ ?_
    rw [mem_coinvariants, mvPolynomialWeight_coact_monomial, h s hs, MonoidAlgebra.one_def]

end TauCeti.ComoduleAlgebra
