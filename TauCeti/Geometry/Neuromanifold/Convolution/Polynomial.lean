/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Chain
public import TauCeti.Geometry.Neuromanifold.MLP.Polynomial
import TauCeti.Geometry.Neuromanifold.Convolution.Composition

/-!
# Jointly polynomial convolutional networks

A fixed `ConvolutionSpec` with polynomial hidden activations has a jointly polynomial
realization in its filters, shared biases, and inputs. `ConvolutionSpec.parameterEquiv`
flattens precisely these parameters, not the entries of the associated dense matrices.
`ConvolutionSpec.polynomialPrefix` instantiates `polynomialChainPrefix` on the affine convolution
layers `a ↦ aeval (polynomialAffineConvolution (A.length_eq i) a) (MLPSpec.layerPolynomial q i)`
(`ConvolutionSpec.polynomialPrefix_eq_polynomialChainPrefix`), so its final prefix
`ConvolutionSpec.polynomialRealize` is the corresponding `polynomialChain`
(`ConvolutionSpec.polynomialRealize_eq_polynomialChain`) and its evaluation agrees with
convolutional realization.
The bias-free tuple substitutes zero for every bias and retains only filter coordinates,
agreeing by `ConvolutionSpec.polynomialRealizeWeights_eq_polynomialChain` with `polynomialChain`
of the bias-free convolution layers
`a ↦ aeval (polynomialConvolution (A.length_eq i) a) (MLPSpec.layerPolynomial q i)`.
Thus both tuples feed the coefficient extraction and faithful bounded-degree presentation for
jointly polynomial models.

With identity hidden activations, the activation polynomials `X` give the tuples of linear
convolutional networks (`polynomialChain` of `polynomialAffineConvolution` and of
`polynomialConvolution`).

All index types are finite, so `Fintype.equivFin` can number the coordinates by `Fin p`.
Depth zero and empty filters are included. The output head remains affine, with no activation.

The jointly polynomial viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. The convolution convention is
that of Shahverdi, *Algebraic Complexity and Neurovariety of Linear Convolutional Networks*,
[arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1: shared scalar biases,
no padding, and no filter reversal.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold.ConvolutionSpec

open MvPolynomial

variable {K : Type*} {L : ℕ}

variable [CommSemiring K]

/-- Joint polynomials for each prefix: `polynomialChainPrefix` applied to the affine convolution
layers followed coordinatewise by `MLPSpec.layerPolynomial q i`, so hidden layers substitute their
activation polynomial and the output layer uses its affine convolution without an activation. -/
def polynomialPrefix (A : ConvolutionSpec K L) (q : Fin (L - 1) → Polynomial K) :
    (i : Fin (L + 1)) → Fin (A.width i) →
      MvPolynomial (A.ParameterIndex ⊕ Fin (A.width 0)) K :=
  polynomialChainPrefix (I := fun j => Fin (A.width j))
    (fun i a => Polynomial.aeval (polynomialAffineConvolution (A.length_eq i) a)
      (MLPSpec.layerPolynomial q i))

/-- Every convolutional polynomial prefix is the corresponding prefix of `polynomialChainPrefix`
applied to the affine convolution layers followed coordinatewise by
`MLPSpec.layerPolynomial q i`. -/
theorem polynomialPrefix_eq_polynomialChainPrefix (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (k : Fin (L + 1)) :
    A.polynomialPrefix q k =
      polynomialChainPrefix (I := fun j => Fin (A.width j))
        (fun i a => Polynomial.aeval (polynomialAffineConvolution (A.length_eq i) a)
          (MLPSpec.layerPolynomial q i)) k := (rfl)

/-- The empty polynomial prefix is the tuple of input variables. -/
@[simp] theorem polynomialPrefix_zero (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    A.polynomialPrefix q 0 = fun a => X (Sum.inr a) :=
  polynomialChainPrefix_zero _

/-- A polynomial prefix applies its filter sum and shared bias, and substitutes the hidden
activation polynomial except at the affine output head. -/
@[simp] theorem polynomialPrefix_succ (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (i : Fin L) (a : Fin (A.width i.succ)) :
    A.polynomialPrefix q i.succ a =
      let z := (∑ j, X (Sum.inl ⟨i, Sum.inl j⟩) *
        A.polynomialPrefix q i.castSucc (convolutionIndex (A.length_eq i) a j)) +
          X (Sum.inl ⟨i, Sum.inr ()⟩)
      if h : i.val + 1 < L then Polynomial.aeval z (q ⟨i.val, by omega⟩) else z := by
  rw [polynomialPrefix_eq_polynomialChainPrefix, polynomialChainPrefix_succ,
    ← Polynomial.aeval_algHom_apply (bind₁ _), ← polynomialPrefix_eq_polynomialChainPrefix]
  dsimp only
  split_ifs with h
  · rw [MLPSpec.layerPolynomial_of_lt q i h]
    simp [polynomialAffineConvolution_apply]
  · rw [MLPSpec.layerPolynomial_of_val_add_one_eq q i (by omega)]
    simp [polynomialAffineConvolution_apply]

/-- Evaluating the joint polynomials recovers every convolutional prefix. -/
theorem eval_polynomialPrefix (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K)
    (hq : ∀ j t, A.activation j t = (q j).eval t)
    (p : A.ParameterIndex → K) (x : Fin (A.width 0) → K) (i : Fin (L + 1))
    (a : Fin (A.width i)) :
    eval (Sum.elim p x) (A.polynomialPrefix q i a) =
      A.evalPrefix (A.parameterEquiv p) x i a := by
  have hstep (k : Fin L) :
      polynomialRealization
          (fun b => Polynomial.aeval (polynomialAffineConvolution (K := K) (A.length_eq k) b)
            (MLPSpec.layerPolynomial q k))
          (fun w => p ⟨k, w⟩) =
        Neuromanifold.activation (A.toMLPSpec.layerActivation k) () ∘
          affineConvolution (A.length_eq k) (A.parameterEquiv p k) := by
    have hparam :
        affineConvolutionParameterEquiv K (A.filterLength k) (fun w => p ⟨k, w⟩) =
          A.parameterEquiv p k := by
      ext <;> simp
    rw [polynomialRealization_aeval, polynomialRealization_polynomialAffineConvolution]
    funext y b
    simp [A.toMLPSpec.layerActivation_eq_eval_layerPolynomial hq, hparam]
  rw [← polynomialRealization_apply, polynomialPrefix_eq_polynomialChainPrefix,
    polynomialRealization_polynomialChainPrefix_eq_dfoldl, A.evalPrefix_eq_dfoldl]
  simp only [hstep]

/-- Joint polynomials for the full affine convolutional realization. -/
def polynomialRealize (A : ConvolutionSpec K L) (q : Fin (L - 1) → Polynomial K) :
    Fin (A.width (Fin.last L)) → MvPolynomial (A.ParameterIndex ⊕ Fin (A.width 0)) K :=
  A.polynomialPrefix q (Fin.last L)

/-- The polynomial tuple is the final prefix. -/
theorem polynomialRealize_def (A : ConvolutionSpec K L) (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealize q = A.polynomialPrefix q (Fin.last L) := (rfl)

/-- The affine convolutional polynomial tuple is `polynomialChain` of its affine convolution
layers followed coordinatewise by `MLPSpec.layerPolynomial q i`. -/
theorem polynomialRealize_eq_polynomialChain (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealize q =
      polynomialChain (I := fun j => Fin (A.width j))
        (fun i a => Polynomial.aeval (polynomialAffineConvolution (A.length_eq i) a)
          (MLPSpec.layerPolynomial q i)) := by
  rw [polynomialRealize_def, polynomialChain_def]
  exact A.polynomialPrefix_eq_polynomialChainPrefix q (Fin.last L)

/-- Polynomial hidden activations make the convolutional network jointly polynomial in its
actual parameters and inputs. -/
theorem polynomialRealization_polynomialRealize (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K)
    (hq : ∀ j t, A.activation j t = (q j).eval t) :
    polynomialRealization (A.polynomialRealize q) = A.realize ∘ A.parameterEquiv := by
  funext p x a
  rw [polynomialRealization_apply, polynomialRealize_def, Function.comp_apply, realize_def]
  exact A.eval_polynomialPrefix q hq p x (Fin.last L) a

/-- Polynomial coordinates do not alter the set of realized functions. -/
theorem realizedFunctions_polynomialRealize (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K)
    (hq : ∀ j t, A.activation j t = (q j).eval t) :
    realizedFunctions (polynomialRealization (A.polynomialRealize q)) =
      realizedFunctions A.realize := by
  rw [A.polynomialRealization_polynomialRealize q hq, realizedFunctions_def,
    realizedFunctions_def, A.parameterEquiv.surjective.range_comp]

/-- Substituting zero for the shared biases in prefix `k` of `A.polynomialPrefix q` gives prefix
`k` of `polynomialChainPrefix` applied to the bias-free convolution layers followed coordinatewise
by `MLPSpec.layerPolynomial q i`. -/
theorem polynomialPrefix_zeroBias_eq_polynomialChainPrefix (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (k : Fin (L + 1)) :
    polynomialReparametrize (fun ⟨i, j⟩ => Sum.elim (fun a => X ⟨i, a⟩) (fun _ => 0) j)
        (A.polynomialPrefix q k) =
      polynomialChainPrefix (I := fun j => Fin (A.width j))
        (fun i a => Polynomial.aeval (polynomialConvolution (A.length_eq i) a)
          (MLPSpec.layerPolynomial q i)) k := by
  rw [A.polynomialPrefix_eq_polynomialChainPrefix, sumElim_X_zero_eq_rename,
    polynomialChainPrefix_polynomialReparametrize
      (fun i => Sum.elim X (0 : Unit → MvPolynomial (Fin (A.filterLength i)) K))]
  simp

/-- Joint polynomials for bias-free realization, substituting filter variables for filters
and zero for biases. There are no artificial bias coordinates in the domain. -/
def polynomialRealizeWeights (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    Fin (A.width (Fin.last L)) → MvPolynomial (A.WeightIndex ⊕ Fin (A.width 0)) K :=
  polynomialReparametrize (fun ⟨i, j⟩ => Sum.elim (fun a => X ⟨i, a⟩) (fun _ => 0) j)
    (A.polynomialRealize q)

/-- The bias-free tuple substitutes filter variables for filters and zero for shared biases. -/
theorem polynomialRealizeWeights_def (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealizeWeights q =
      polynomialReparametrize (fun ⟨i, j⟩ => Sum.elim (fun a => X ⟨i, a⟩) (fun _ => 0) j)
        (A.polynomialRealize q) := (rfl)

/-- The bias-free convolutional polynomial tuple is `polynomialChain` of its bias-free convolution
layers followed coordinatewise by `MLPSpec.layerPolynomial q i`. -/
theorem polynomialRealizeWeights_eq_polynomialChain (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealizeWeights q =
      polynomialChain (I := fun j => Fin (A.width j))
        (fun i a => Polynomial.aeval (polynomialConvolution (A.length_eq i) a)
          (MLPSpec.layerPolynomial q i)) := by
  rw [polynomialRealizeWeights_def, polynomialRealize_def, polynomialChain_def]
  exact A.polynomialPrefix_zeroBias_eq_polynomialChainPrefix q (Fin.last L)

/-- The bias-free polynomial tuple realizes the network on precisely its filter product. -/
theorem polynomialRealization_polynomialRealizeWeights (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K)
    (hq : ∀ j t, A.activation j t = (q j).eval t) :
    polynomialRealization (A.polynomialRealizeWeights q) =
      A.realizeWeights ∘ A.weightEquiv := by
  rw [polynomialRealizeWeights_def, polynomialRealization_polynomialReparametrize,
    A.polynomialRealization_polynomialRealize q hq]
  funext w
  simp only [Function.comp_apply, realizeWeights_def]
  congr 1
  funext i
  ext j <;> simp

/-- Bias-free polynomial coordinates preserve the entire realized-function set. -/
theorem realizedFunctions_polynomialRealizeWeights (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K)
    (hq : ∀ j t, A.activation j t = (q j).eval t) :
    realizedFunctions (polynomialRealization (A.polynomialRealizeWeights q)) =
      realizedFunctions A.realizeWeights := by
  rw [A.polynomialRealization_polynomialRealizeWeights q hq, realizedFunctions_def,
    realizedFunctions_def, A.weightEquiv.surjective.range_comp]

/-- With identity hidden activations, the tuple built from the activation polynomials `X`
realizes the linear convolutional network with shared biases. -/
theorem polynomialRealization_polynomialRealize_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) :
    polynomialRealization (A.polynomialRealize fun _ => Polynomial.X) =
      A.realize ∘ A.parameterEquiv :=
  A.polynomialRealization_polynomialRealize _ fun _ _ => by simp [h]

/-- With identity hidden activations, the bias-free tuple built from the activation polynomials
`X` realizes the bias-free linear convolutional network on its filter coordinates. -/
theorem polynomialRealization_polynomialRealizeWeights_of_activation_eq_id
    (A : ConvolutionSpec K L) (h : ∀ j, A.activation j = id) :
    polynomialRealization (A.polynomialRealizeWeights fun _ => Polynomial.X) =
      A.realizeWeights ∘ A.weightEquiv :=
  A.polynomialRealization_polynomialRealizeWeights _ fun _ _ => by simp [h]

end TauCeti.Neuromanifold.ConvolutionSpec
