/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
public import TauCeti.RingTheory.MvPolynomial.Basic

/-!
# Diagonal actions of diagonalizable groups on affine space

Let `G` be a commutative monoid and `w : σ → G` a family of weights. The polynomial ring
`MvPolynomial σ R` is a comodule algebra over the monoid algebra `R[G]`, with the coaction
sending the variable `X i` to `X i ⊗ [w i]` (`TauCeti.ComoduleAlgebra.mvPolynomialWeight`). Its
underlying comodule is `TauCeti.Comodule.ofWeights` on the monomial basis.
When `G` is a commutative group, this is the action of the diagonalizable group `D(G) = Spec R[G]`
on the affine space `𝔸^σ` in which `D(G)` scales the `i`th coordinate by the character `w i`. For
`G = Multiplicative ℤ`, so that `D(G)` is the multiplicative group `𝔾ₘ`, these are the linear
actions of `𝔾ₘ` on affine space with weights `w`.

A monomial `X^s` is a weight vector of weight `∏ i, w i ^ s i`, which is Mathlib's
`Finsupp.weight` read multiplicatively
(`TauCeti.ComoduleAlgebra.mvPolynomialWeight_coact_monomial`), and a polynomial is invariant
exactly when every monomial in its support has weight `1`, that is, when it is weighted
homogeneous of degree `0`
(`TauCeti.ComoduleAlgebra.mem_coinvariants_mvPolynomialWeight_iff`). For `𝔾ₘ` acting on `𝔸²`
with weights `1` and `-1`, the invariants are the polynomials in `x y`
(`TauCeti.QuotientExamples.coinvariants_mvPolynomialWeight_one_neg_one_eq_adjoin`).

## Main declarations

* `TauCeti.ComoduleAlgebra.monomialWeight`: the weight of a monomial.
* `TauCeti.ComoduleAlgebra.mvPolynomialWeight`: the comodule algebra structure on
  `MvPolynomial σ R` over `R[G]` given by the weights `w`.
* `TauCeti.ComoduleAlgebra.mvPolynomialWeight_coact_monomial`: monomials are weight vectors.
* `TauCeti.ComoduleAlgebra.mem_coinvariants_mvPolynomialWeight_iff`: the invariants are the
  weighted homogeneous polynomials of degree `0`.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

open _root_.MvPolynomial

variable {R σ G : Type*} [CommSemiring R] [CommMonoid G]

/-- The weight `∏ i, w i ^ s i` of the monomial with exponent `s`: Mathlib's `Finsupp.weight`
with weights `w`, read multiplicatively through `Additive G`. -/
noncomputable def monomialWeight (w : σ → G) (s : σ →₀ ℕ) : G :=
  (Finsupp.weight (Additive.ofMul ∘ w) s).toMul

theorem monomialWeight_def (w : σ → G) (s : σ →₀ ℕ) :
    monomialWeight w s = (Finsupp.weight (Additive.ofMul ∘ w) s).toMul := (rfl)

/-- The weight of a monomial is the product `∏ i, w i ^ s i` over the support of `s`. -/
theorem monomialWeight_eq_prod (w : σ → G) (s : σ →₀ ℕ) :
    monomialWeight w s = s.prod fun i n ↦ w i ^ n := by
  simp [monomialWeight_def, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod, toMul_sum]

/-- The constant monomial has weight `1`: `map_zero` for `Finsupp.weight`, read
multiplicatively. -/
@[simp]
theorem monomialWeight_zero (w : σ → G) : monomialWeight w 0 = 1 := by
  rw [monomialWeight_def, map_zero, toMul_zero]

/-- The weight of a product of monomials is the product of their weights: `map_add` for
`Finsupp.weight`, read multiplicatively. -/
@[simp]
theorem monomialWeight_add (w : σ → G) (s t : σ →₀ ℕ) :
    monomialWeight w (s + t) = monomialWeight w s * monomialWeight w t := by
  rw [monomialWeight_def, map_add, toMul_add, monomialWeight_def, monomialWeight_def]

/-- The monomial `X i ^ n` has weight `w i ^ n`: `Finsupp.weight_single`, read
multiplicatively. -/
@[simp]
theorem monomialWeight_single (w : σ → G) (i : σ) (n : ℕ) :
    monomialWeight w (Finsupp.single i n) = w i ^ n := by
  rw [monomialWeight_def, Finsupp.weight_single, toMul_nsmul, Function.comp_apply, toMul_ofMul]

/-- The coaction with weights `w`, as an algebra homomorphism: it sends `X i` to `X i ⊗ [w i]`. -/
noncomputable def mvPolynomialWeightCoact (w : σ → G) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R ⊗[R] MonoidAlgebra R G :=
  aeval fun i ↦ X i ⊗ₜ[R] MonoidAlgebra.single (w i) 1

@[simp]
theorem mvPolynomialWeightCoact_X (w : σ → G) (i : σ) :
    mvPolynomialWeightCoact (R := R) w (X i) = X i ⊗ₜ[R] MonoidAlgebra.single (w i) 1 :=
  aeval_X _ _

/-- The coaction sends a monomial to itself tensored with its weight. -/
@[simp]
theorem mvPolynomialWeightCoact_monomial (w : σ → G) (s : σ →₀ ℕ) (c : R) :
    mvPolynomialWeightCoact w (monomial s c) =
      monomial s c ⊗ₜ[R] MonoidAlgebra.single (monomialWeight w s) 1 := by
  classical
  induction s using Finsupp.induction with
  | zero =>
    simp [mvPolynomialWeightCoact, Algebra.TensorProduct.algebraMap_apply, MonoidAlgebra.one_def]
  | single_add i n s _ _ ih =>
    rw [monomial_single_add, map_mul, map_pow, mvPolynomialWeightCoact_X, ih,
      Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
    simp [MonoidAlgebra.single_pow]

/-- The diagonal comodule on the monomial basis has coaction `mvPolynomialWeightCoact w`. -/
theorem ofWeights_basisMonomials_coact (w : σ → G) :
    (Comodule.ofWeights (basisMonomials σ R) (monomialWeight w)).coact =
      (mvPolynomialWeightCoact (R := R) w).toLinearMap :=
  (basisMonomials σ R).ext fun s ↦ by
    rw [Comodule.ofWeights_coact_basis, AlgHom.toLinearMap_apply, coe_basisMonomials,
      mvPolynomialWeightCoact_monomial]

/-- **The diagonal action with weights `w`** of the diagonalizable monoid `D(G) = Spec R[G]` on
the affine space `Spec (MvPolynomial σ R)`, as a comodule algebra structure: the coaction sends
`X i` to `X i ⊗ [w i]`. The underlying comodule is `Comodule.ofWeights` on the monomial basis.

This is not an instance, since it depends on the weights. -/
@[implicit_reducible]
noncomputable def mvPolynomialWeight (w : σ → G) :
    ComoduleAlgebra R (MonoidAlgebra R G) (MvPolynomial σ R) :=
  { Comodule.ofWeights (basisMonomials σ R) (monomialWeight w) with
    coact_one := by rw [ofWeights_basisMonomials_coact, AlgHom.toLinearMap_apply, map_one]
    coact_mul a b := by
      simp only [ofWeights_basisMonomials_coact, AlgHom.toLinearMap_apply, map_mul] }

/-- The coaction of `mvPolynomialWeight w` is the algebra homomorphism
`mvPolynomialWeightCoact w`. -/
theorem mvPolynomialWeight_coact (w : σ → G) (p : MvPolynomial σ R) :
    letI := mvPolynomialWeight (R := R) w
    Comodule.coact (R := R) (C := MonoidAlgebra R G) p = mvPolynomialWeightCoact w p :=
  LinearMap.congr_fun (ofWeights_basisMonomials_coact w) p

/-- The variable `X i` has weight `w i`. -/
@[simp]
theorem mvPolynomialWeight_coact_X (w : σ → G) (i : σ) :
    letI := mvPolynomialWeight (R := R) w
    Comodule.coact (R := R) (C := MonoidAlgebra R G) (X i : MvPolynomial σ R) =
      X i ⊗ₜ[R] MonoidAlgebra.single (w i) 1 := by
  rw [mvPolynomialWeight_coact, mvPolynomialWeightCoact_X]

/-- **Monomials are weight vectors**: the monomial with exponent `s` has weight
`monomialWeight w s = ∏ i, w i ^ s i`. -/
@[simp]
theorem mvPolynomialWeight_coact_monomial (w : σ → G) (s : σ →₀ ℕ) (c : R) :
    letI := mvPolynomialWeight (R := R) w
    Comodule.coact (R := R) (C := MonoidAlgebra R G) (monomial s c) =
      monomial s c ⊗ₜ[R] MonoidAlgebra.single (monomialWeight w s) 1 := by
  rw [mvPolynomialWeight_coact, mvPolynomialWeightCoact_monomial]

/-- **The invariants of a diagonal action** are the polynomials all of whose monomials have
weight `1`: the weighted homogeneous polynomials of degree `0` for the weights `w`, read
additively. -/
theorem mem_coinvariants_mvPolynomialWeight_iff (w : σ → G) {p : MvPolynomial σ R} :
    letI := mvPolynomialWeight (R := R) w
    p ∈ coinvariants R (MonoidAlgebra R G) (MvPolynomial σ R) ↔
      p.IsWeightedHomogeneous (Additive.ofMul ∘ w) 0 := by
  let := mvPolynomialWeight (R := R) w
  -- An invariant is a vector of weight `1`.
  rw [mem_coinvariants, MonoidAlgebra.one_def, ← Comodule.mem_weightSpace,
    Comodule.mem_weightSpace_ofWeights_iff (basisMonomials σ R)]
  simp only [Finsupp.mem_support_iff, basisMonomials_repr_apply, monomialWeight_def,
    toMul_eq_one, IsWeightedHomogeneous]

end TauCeti.ComoduleAlgebra
