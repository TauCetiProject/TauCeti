/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.Geometry.Neuromanifold.MLP.Polynomial
public import TauCeti.Geometry.Neuromanifold.Polynomial.Homogeneous

/-!
# Input homogeneity of bias-free monomial MLPs

The input polynomials of a bias-free MLP with hidden monomial activations are homogeneous
of degree the product of the hidden exponents. The output head is linear and contributes
exponent one. For a common hidden exponent `r`, this degree is `r ^ (L - 1)` at
depth `L`. These are homogeneity statements, not assertions of exact total degree: zero
weights or empty layers may give zero output polynomials.

The statements apply to the jointly polynomial tuple `MLPSpec.polynomialRealizeWeights`,
so `polynomialHomogeneousCoefficientMap` and its faithful evaluation and bounded-degree
inclusion API give homogeneous coefficient presentations of these actual networks.
No positivity of the hidden exponents is needed, and the empty network has degree one.

The monomial-network convention follows Finkel–Rodriguez–Wu–Yahl,
*Activation degree thresholds and expressiveness of polynomial neural networks*,
[arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1 and §1.1.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold.MLPSpec

open MvPolynomial

variable {K : Type*} {L : ℕ}

/-- The exponent used by each layer of a monomial MLP: the specified hidden exponent,
and one at the linear output head. -/
def layerExponent (r : Fin (L - 1) → ℕ) (i : Fin L) : ℕ :=
  if h : i.val + 1 < L then r ⟨i.val, by omega⟩ else 1

/-- Hidden layers retain their specified exponent. -/
@[simp] theorem layerExponent_castSucc (r : Fin L → ℕ) (i : Fin L) :
    layerExponent (L := L + 1) r i.castSucc = r i := by
  simp [layerExponent]

/-- The output head has exponent one. -/
@[simp] theorem layerExponent_last (r : Fin L → ℕ) :
    layerExponent (L := L + 1) r (Fin.last L) = 1 := by
  simp [layerExponent]

/-- The product of all layer exponents is the product of the hidden ones. -/
theorem prod_layerExponent (r : Fin (L - 1) → ℕ) :
    ∏ i, layerExponent r i = ∏ j, r j := by
  cases L with
  | zero => simp
  | succ n =>
    simpa only [Nat.add_sub_cancel] using
      (Fin.prod_univ_castSucc (layerExponent (L := n + 1) r)).trans
        (by simp [layerExponent])

variable [CommSemiring K]

/-- Monomial hidden activation polynomials extend to all layers using exponent one at the head. -/
theorem layerPolynomial_X_pow (r : Fin (L - 1) → ℕ) (i : Fin L) :
    layerPolynomial (fun j => (Polynomial.X : Polynomial K) ^ r j) i =
      Polynomial.X ^ layerExponent r i := by
  by_cases h : i.val + 1 < L
  · rw [layerPolynomial_of_lt _ i h]
    simp [layerExponent, h]
  · rw [layerPolynomial_of_val_add_one_eq _ i (by omega)]
    simp [layerExponent, h]

/-- Collecting inputs in a zero-bias monomial prefix gives the weighted sum of the preceding
input polynomials, raised to the layer exponent. -/
private theorem inputPolynomial_prefix_succ (A : MLPSpec K L) (r : Fin (L - 1) → ℕ)
    (i : Fin L) (o : Fin (A.width i.succ)) :
    inputPolynomial
        (polynomialReparametrize A.zeroBiasSubstitution
          (A.polynomialPrefix (fun j => Polynomial.X ^ r j) i.succ)) o =
      (∑ j, C (X ⟨i, (o, j)⟩) *
        inputPolynomial
          (polynomialReparametrize A.zeroBiasSubstitution
            (A.polynomialPrefix (fun j => Polynomial.X ^ r j) i.castSucc)) j) ^
        layerExponent r i := by
  simp only [inputPolynomial_polynomialReparametrize, polynomialPrefix_succ]
  simp [layerPolynomial_X_pow, inputPolynomial_def]

/-- Every zero-bias monomial prefix is homogeneous in the inputs; its degree is the partial
product of the exponents of the layers already evaluated. -/
theorem isHomogeneous_inputPolynomial_polynomialPrefix_weights (A : MLPSpec K L)
    (r : Fin (L - 1) → ℕ) (i : Fin (L + 1)) (o : Fin (A.width i)) :
    (inputPolynomial
      (polynomialReparametrize A.zeroBiasSubstitution
        (A.polynomialPrefix (fun j => Polynomial.X ^ r j) i)) o).IsHomogeneous
      (Fin.partialProd (layerExponent r) i) := by
  induction i using Fin.induction with
  | zero =>
    simpa [inputPolynomial_def, polynomialReparametrize_apply] using
      (isHomogeneous_X (R := MvPolynomial A.WeightIndex K) o)
  | succ i ih =>
    rw [inputPolynomial_prefix_succ, Fin.partialProd_succ]
    exact (IsHomogeneous.sum _ _ _ fun j _ => (ih j).C_mul _).pow _

/-- The jointly polynomial tuple of a bias-free monomial MLP is homogeneous in its inputs of
degree the product of the hidden exponents, with a linear output head. -/
theorem isHomogeneous_inputPolynomial_polynomialRealizeWeights (A : MLPSpec K L)
    (r : Fin (L - 1) → ℕ) (o : Fin (A.width (Fin.last L))) :
    (inputPolynomial (A.polynomialRealizeWeights fun j => Polynomial.X ^ r j) o).IsHomogeneous
      (∏ j, r j) := by
  have h := A.isHomogeneous_inputPolynomial_polynomialPrefix_weights r (Fin.last L) o
  have hd : Fin.partialProd (layerExponent r) (Fin.last L) = ∏ j, r j :=
    (Fin.partialProd_last (layerExponent r)).trans (prod_layerExponent r)
  simpa only [polynomialRealizeWeights_def, polynomialRealize_def, hd] using h

/-- With a common hidden exponent `r`, the input polynomials are homogeneous of degree
`r ^ (L - 1)`. -/
theorem isHomogeneous_inputPolynomial_polynomialRealizeWeights_const (A : MLPSpec K L)
    (r : ℕ) (o : Fin (A.width (Fin.last L))) :
    (inputPolynomial (A.polynomialRealizeWeights fun _ => Polynomial.X ^ r) o).IsHomogeneous
      (r ^ (L - 1)) := by
  simpa using A.isHomogeneous_inputPolynomial_polynomialRealizeWeights (fun _ => r) o

/-- The homogeneous coefficient presentation of a bias-free monomial MLP, on its actual
weight-only parameter space. Coordinates are collected after the zero-bias substitution. -/
def monomialHomogeneousCoefficientMap (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ)
    (w : (monomial (K := K) d r).Weights) :
    Fin ((monomial (K := K) d r).width (Fin.last L)) →
      homogeneousSubmodule (Fin ((monomial (K := K) d r).width 0)) K (∏ j, r j) :=
  polynomialHomogeneousCoefficientMap
    ((monomial d r).polynomialRealizeWeights fun j => Polynomial.X ^ r j)
    ((monomial d r).isHomogeneous_inputPolynomial_polynomialRealizeWeights r)
    ((monomial d r).weightEquiv.symm w)

/-- Forgetting homogeneity gives the input polynomial with the weights specialized to `w`. -/
@[simp] theorem monomialHomogeneousCoefficientMap_coe (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ) (w : (monomial (K := K) d r).Weights)
    (o : Fin ((monomial (K := K) d r).width (Fin.last L))) :
    (monomialHomogeneousCoefficientMap d r w o :
      MvPolynomial (Fin ((monomial (K := K) d r).width 0)) K) =
      map (eval ((monomial d r).weightEquiv.symm w))
        (inputPolynomial
          ((monomial d r).polynomialRealizeWeights fun j => Polynomial.X ^ r j) o) := by
  simp [monomialHomogeneousCoefficientMap]

/-- Evaluating the homogeneous coefficients recovers the bias-free monomial network on its
original weight space, without adding bias coordinates. -/
theorem tupleEvaluation_comp_monomialHomogeneousCoefficientMap (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ) :
    tupleEvaluation (Fin ((monomial (K := K) d r).width (Fin.last L)))
        (homogeneousSubmodule (Fin ((monomial (K := K) d r).width 0)) K (∏ j, r j)) ∘
      monomialHomogeneousCoefficientMap d r =
      (monomial (K := K) d r).realizeWeights := by
  funext w
  simpa [monomialHomogeneousCoefficientMap,
    polynomialRealization_polynomialRealizeWeights_monomial] using
    congrFun (tupleEvaluation_comp_polynomialHomogeneousCoefficientMap
      ((monomial (K := K) d r).polynomialRealizeWeights fun j => Polynomial.X ^ r j)
      ((monomial d r).isHomogeneous_inputPolynomial_polynomialRealizeWeights r))
      ((monomial d r).weightEquiv.symm w)

section Faithful

variable {K : Type*} [CommRing K] [IsDomain K] [Infinite K]

/-- Over an infinite integral domain, two weight tuples realize the same monomial network
function exactly when their homogeneous coefficients agree. -/
theorem monomialHomogeneousCoefficientMap_eq_iff (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ) {w v : (monomial (K := K) d r).Weights} :
    monomialHomogeneousCoefficientMap d r w = monomialHomogeneousCoefficientMap d r v ↔
      (monomial d r).realizeWeights w = (monomial d r).realizeWeights v :=
  apply_eq_apply_iff_of_injective (tupleEvaluation_injective _)
    (congrFun (tupleEvaluation_comp_monomialHomogeneousCoefficientMap d r))

end Faithful

end TauCeti.Neuromanifold.MLPSpec
