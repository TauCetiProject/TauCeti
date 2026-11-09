/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Polynomial
public import TauCeti.Geometry.Neuromanifold.MLP.Linear

/-!
# Linear convolutional networks

A convolutional specification `A : ConvolutionSpec K L` whose hidden activations are all the
identity is a linear convolutional network. Its layers are single-channel valid convolutions with
nothing between them, so its bias-free realization is a single matrix: the product of the
structured convolution matrices of its filters. This file records that identification and its
consequence for the jointly polynomial presentation.

The product of the first `i` convolution matrices is `MLPSpec.weightProduct` of the structured
dense weights `A.denseWeights w`, with the identity matrix at layer `0`; by
`MLPSpec.weightProduct_succ` and `ConvolutionSpec.denseWeights_apply`, layer `i + 1` multiplies by
`convolutionMatrix (A.length_eq i) (w i)` on the left. The prefix formulas below are
`MLPSpec.evalPrefix_zeroBias_eq_mulVec_of_activation_eq_id` and
`MLPSpec.evalPrefix_eq_mulVec_add_of_activation_eq_id` at the structured dense parameters. When
every hidden activation of `A` is `id`:

* every bias-free prefix evaluates the product of the convolution matrices below it, so the
  bias-free realization is `Matrix.mulVec` of the full product, and the bias-free neuromanifold is
  the image under matrix evaluation of these products;
* with shared biases, every prefix is affine: its linear part is the same product for the filters
  of the parameters, and its translation is the prefix at the zero input;
* over an infinite domain, every jointly polynomial presentation of the bias-free network, in
  particular the bias-free tuple with activation polynomials `X`, has coordinate polynomials that
  are homogeneous of degree one in the input.

The parameters are always the complete filter product: different filters may realize the same
function, and no description of the neuromanifold by rank, dimension, or polynomial
factorization is asserted. The homogeneity statement concerns the coordinate polynomials
themselves; a zero coordinate polynomial is homogeneous of every degree.

## References

* Vahid Shahverdi, *Algebraic Complexity and Neurovariety of Linear Convolutional Networks*,
  [arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1, equations (2.1)–(2.2).
* Giovanni Luca Marchetti, Vahid Shahverdi, Stefano Mereta, Matthew Trager, and Kathlén Kohn,
  *Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
  [arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
-/

public section

open Matrix

namespace TauCeti.Neuromanifold.ConvolutionSpec

variable {K : Type*} {L : ℕ}

section Evaluation

variable [Semiring K]

/-- With identity hidden activations, each bias-free prefix evaluates the product of the
convolution matrices of the filters below it. -/
theorem evalPrefix_zeroBias_eq_mulVec_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (w : A.Weights) (x : Fin (A.width 0) → K)
    (i : Fin (L + 1)) :
    A.evalPrefix (A.zeroBias w) x i = A.toMLPSpec.weightProduct (A.denseWeights w) i *ᵥ x := by
  rw [evalPrefix_eq_mlp, denseParameters_zeroBias,
    A.toMLPSpec.evalPrefix_zeroBias_eq_mulVec_of_activation_eq_id h]

/-- With identity hidden activations, each prefix with shared biases is affine: its linear part
is the product of the convolution matrices of the filters below it, and its translation is the
prefix at the zero input. -/
theorem evalPrefix_eq_mulVec_add_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (p : A.Parameters) (x : Fin (A.width 0) → K)
    (i : Fin (L + 1)) :
    A.evalPrefix p x i =
      A.toMLPSpec.weightProduct (A.denseWeights fun j => (p j).1) i *ᵥ x + A.evalPrefix p 0 i := by
  rw [evalPrefix_eq_mlp, evalPrefix_eq_mlp,
    A.toMLPSpec.evalPrefix_eq_mulVec_add_of_activation_eq_id h]
  congr 3
  funext j
  simp only [denseParameters_apply, denseWeights_apply]

/-- With identity hidden activations, the bias-free realization is evaluation at the product of
the convolution matrices of all filters. -/
theorem realizeWeights_eq_mulVec_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (w : A.Weights) :
    A.realizeWeights w = (A.toMLPSpec.weightProduct (A.denseWeights w) (Fin.last L)).mulVec := by
  funext x
  rw [realizeWeights_def, Function.comp_apply, realize_def]
  exact A.evalPrefix_zeroBias_eq_mulVec_of_activation_eq_id h w x (Fin.last L)

/-- With identity hidden activations, the realization with shared biases is affine: its linear
part is the product of the convolution matrices of all filters, and its translation is its value
at the zero input. -/
theorem realize_eq_mulVec_add_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (p : A.Parameters) (x : Fin (A.width 0) → K) :
    A.realize p x =
      A.toMLPSpec.weightProduct (A.denseWeights fun j => (p j).1) (Fin.last L) *ᵥ x +
        A.realize p 0 := by
  rw [realize_def, realize_def]
  exact A.evalPrefix_eq_mulVec_add_of_activation_eq_id h p x (Fin.last L)

/-- With identity hidden activations, the bias-free neuromanifold is the image under matrix
evaluation of the products of the convolution matrices of all filters. -/
theorem realizedFunctions_realizeWeights_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) :
    realizedFunctions A.realizeWeights =
      Matrix.mulVec '' Set.range fun w => A.toMLPSpec.weightProduct (A.denseWeights w)
        (Fin.last L) := by
  rw [realizedFunctions_def, ← Set.range_comp]
  exact congrArg Set.range (funext (A.realizeWeights_eq_mulVec_of_activation_eq_id h))

end Evaluation

section Polynomial

variable {R V : Type*} [CommRing R] [IsDomain R] [Infinite R]

/-- Over an infinite domain, every jointly polynomial presentation of a bias-free linear
convolutional network is homogeneous of degree one in the input: if `P` realizes the network on
the filters `e v` for every parameter `v`, then each collected input polynomial of `P` is
homogeneous of degree one. -/
theorem isHomogeneous_inputPolynomial_of_polynomialRealization_eq_of_activation_eq_id
    (A : ConvolutionSpec R L) (h : ∀ j, A.activation j = id)
    {P : Fin (A.width (Fin.last L)) → MvPolynomial (V ⊕ Fin (A.width 0)) R}
    {e : (V → R) → A.Weights} (hP : polynomialRealization P = A.realizeWeights ∘ e)
    (j : Fin (A.width (Fin.last L))) :
    (inputPolynomial P j).IsHomogeneous 1 :=
  isHomogeneous_inputPolynomial_iff.mpr fun v c x => by
    rw [hP, Function.comp_apply, A.realizeWeights_eq_mulVec_of_activation_eq_id h, mulVec_smul,
      pow_one, Pi.smul_apply]

/-- Over an infinite domain, the coordinate polynomials of the bias-free tuple of a convolutional
network with identity hidden activations, built from the activation polynomials `X`, are
homogeneous of degree one in the input. -/
theorem isHomogeneous_inputPolynomial_polynomialRealizeWeights_of_activation_eq_id
    (A : ConvolutionSpec R L) (h : ∀ j, A.activation j = id) (j : Fin (A.width (Fin.last L))) :
    (inputPolynomial (A.polynomialRealizeWeights fun _ => Polynomial.X) j).IsHomogeneous 1 :=
  A.isHomogeneous_inputPolynomial_of_polynomialRealization_eq_of_activation_eq_id h
    (A.polynomialRealization_polynomialRealizeWeights_of_activation_eq_id h) j

end Polynomial

end TauCeti.Neuromanifold.ConvolutionSpec
