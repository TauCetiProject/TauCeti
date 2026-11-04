/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Polynomial

/-!
# Homogeneity of bias-free monomial MLPs

A bias-free MLP whose hidden layer `j + 1` applies `t ↦ t ^ r j` is homogeneous in its input:
scaling the input by `c` scales every hidden prefix by a power of `c`, because each linear layer
commutes with scaling and each monomial activation raises the scale to its exponent. The output
layer is linear, so it contributes the exponent one.

* `MLPSpec.monomial_evalPrefix_zeroBias_smul`: the prefix `hᵢ` scales by `c` to the product of
  the hidden exponents of the layers below it.
* `MLPSpec.monomial_realizeWeights_smul`: the realization scales by `c ^ ∏ j, r j`.
* `MLPSpec.monomial_const_realizeWeights_smul`: with a common hidden exponent `r` and depth `L`,
  the realization scales by `c ^ r ^ (L - 1)`.

Over an infinite domain these scaling laws make every jointly polynomial presentation of the
network homogeneous in the input. If a tuple `P` realizes the bias-free monomial MLP on the
weights assembled from its parameters by any map `e`, then every collected input polynomial
`inputPolynomial P j` is homogeneous of degree `∏ k, r k`
(`MLPSpec.isHomogeneous_inputPolynomial_of_polynomialRealization_eq`). In particular this holds
for the bias-free polynomial tuple `MLPSpec.polynomialRealizeWeights` with hidden activation
polynomials `X ^ r j`
(`MLPSpec.isHomogeneous_inputPolynomial_polynomialRealizeWeights_monomial`), with degree
`r ^ (L - 1)` for a common hidden exponent `r`
(`MLPSpec.isHomogeneous_inputPolynomial_polynomialRealizeWeights_monomial_const`). These are
statements about the coordinate polynomials themselves, not only about their values: a zero
coordinate polynomial is homogeneous of every degree, and no total degree is asserted.

Zero exponents are allowed: a hidden layer with exponent zero outputs the constant vector `1`,
and the realization is then constant in the input, of degree zero. Depth zero gives the identity,
of degree one.

## References

* Bella Finkel, Jose Israel Rodriguez, Chenxi Wu, and Thomas Yahl, *Activation degree
  thresholds and expressiveness of polynomial neural networks*,
  [arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1.
-/

public section

open Matrix

namespace TauCeti.Neuromanifold.MLPSpec

variable {K : Type*} [CommSemiring K] {L : ℕ}

/-- Scaling the input of a bias-free monomial MLP by `c` scales its prefix `hᵢ` by `c` raised to
the product of the hidden exponents `r j` of the layers below it, that is, with `j < i`. -/
theorem monomial_evalPrefix_zeroBias_smul (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ)
    (w : (monomial d r : MLPSpec K L).Weights) (c : K)
    (x : Fin ((monomial d r : MLPSpec K L).width 0) → K) (i : Fin (L + 1)) :
    (monomial d r).evalPrefix ((monomial d r).zeroBias w) (c • x) i =
      c ^ (∏ j : Fin (L - 1) with j.val < i.val, r j) •
        (monomial d r).evalPrefix ((monomial d r).zeroBias w) x i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    ext k
    simp only [evalPrefix_succ, zeroBias_apply, ih, mulVec_smul, Pi.zero_apply, add_zero,
      Pi.smul_apply, smul_eq_mul, Fin.val_succ, Fin.val_castSucc]
    by_cases h : i.val + 1 < L
    · -- A hidden layer raises the scale to its exponent `r i`.
      have hfilter : (Finset.univ.filter fun j : Fin (L - 1) => j.val < i.val + 1) =
          insert ⟨i.val, by omega⟩ (Finset.univ.filter fun j : Fin (L - 1) => j.val < i.val) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [layerActivation_of_lt _ i h, monomial_activation, monomial_activation, hfilter,
        Finset.prod_insert (by simp), mul_pow, ← pow_mul, mul_comm (r _)]
    · -- The output layer is linear, and no hidden exponent is added.
      have hfilter : (Finset.univ.filter fun j : Fin (L - 1) => j.val < i.val + 1) =
          Finset.univ.filter fun j : Fin (L - 1) => j.val < i.val := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [layerActivation_of_val_add_one_eq _ i (by omega), hfilter, id_eq, id_eq]

/-- Scaling the input of a bias-free monomial MLP by `c` scales its realization by
`c ^ ∏ j, r j`, the product of all hidden exponents. -/
theorem monomial_realizeWeights_smul (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ)
    (w : (monomial d r : MLPSpec K L).Weights) (c : K)
    (x : Fin ((monomial d r : MLPSpec K L).width 0) → K) :
    (monomial d r).realizeWeights w (c • x) =
      c ^ (∏ j, r j) • (monomial d r).realizeWeights w x := by
  simp only [realizeWeights_def, Function.comp_apply, realize_def,
    monomial_evalPrefix_zeroBias_smul, Fin.val_last]
  rw [Finset.filter_true_of_mem fun j _ => by omega]

/-- With a common hidden exponent `r`, scaling the input of a bias-free monomial MLP of depth `L`
by `c` scales its realization by `c ^ r ^ (L - 1)`. -/
theorem monomial_const_realizeWeights_smul (d : Fin (L + 1) → ℕ) (r : ℕ)
    (w : (monomial d fun _ => r : MLPSpec K L).Weights) (c : K)
    (x : Fin ((monomial d fun _ => r : MLPSpec K L).width 0) → K) :
    (monomial d fun _ => r).realizeWeights w (c • x) =
      c ^ r ^ (L - 1) • (monomial d fun _ => r).realizeWeights w x := by
  simpa using monomial_realizeWeights_smul d (fun _ => r) w c x

section Polynomial

variable {R V : Type*} [CommRing R] [IsDomain R] [Infinite R]

/-- Over an infinite domain, every jointly polynomial presentation of a bias-free monomial MLP is
homogeneous in the input: if `P` realizes the network on the weights `e v` for every parameter
`v`, then each collected input polynomial of `P` is homogeneous of degree `∏ k, r k`. -/
theorem isHomogeneous_inputPolynomial_of_polynomialRealization_eq (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ)
    {P : Fin ((monomial d r : MLPSpec R L).width (Fin.last L)) →
      MvPolynomial (V ⊕ Fin ((monomial d r : MLPSpec R L).width 0)) R}
    {e : (V → R) → (monomial d r : MLPSpec R L).Weights}
    (hP : polynomialRealization P = (monomial d r).realizeWeights ∘ e)
    (j : Fin ((monomial d r : MLPSpec R L).width (Fin.last L))) :
    (inputPolynomial P j).IsHomogeneous (∏ k, r k) :=
  isHomogeneous_inputPolynomial_iff.mpr fun v c x => by
    rw [hP, Function.comp_apply, monomial_realizeWeights_smul, Pi.smul_apply]

/-- Over an infinite domain, the coordinate polynomials of the bias-free polynomial tuple of a
monomial MLP, with hidden activation polynomials `X ^ r j`, are homogeneous in the input of degree
`∏ k, r k`. -/
theorem isHomogeneous_inputPolynomial_polynomialRealizeWeights_monomial (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ) (j : Fin ((monomial d r : MLPSpec R L).width (Fin.last L))) :
    (inputPolynomial ((monomial d r : MLPSpec R L).polynomialRealizeWeights
      fun j => Polynomial.X ^ r j) j).IsHomogeneous (∏ k, r k) :=
  isHomogeneous_inputPolynomial_of_polynomialRealization_eq d r
    (polynomialRealization_polynomialRealizeWeights_monomial d r) j

/-- Over an infinite domain, the coordinate polynomials of the bias-free polynomial tuple of a
monomial MLP of depth `L` with common hidden exponent `r` are homogeneous in the input of degree
`r ^ (L - 1)`. -/
theorem isHomogeneous_inputPolynomial_polynomialRealizeWeights_monomial_const
    (d : Fin (L + 1) → ℕ) (r : ℕ)
    (j : Fin ((monomial d fun _ => r : MLPSpec R L).width (Fin.last L))) :
    (inputPolynomial ((monomial d fun _ => r : MLPSpec R L).polynomialRealizeWeights
      fun _ => Polynomial.X ^ r) j).IsHomogeneous (r ^ (L - 1)) := by
  simpa using isHomogeneous_inputPolynomial_polynomialRealizeWeights_monomial d (fun _ => r) j

end Polynomial

end TauCeti.Neuromanifold.MLPSpec
