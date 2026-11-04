/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Basic
public import TauCeti.Geometry.Neuromanifold.MLP.Basic

/-!
# Finite convolutional networks

`ConvolutionSpec` specifies a finite chain of single-channel valid convolutions. It reuses
`MLPSpec` for the lengths and hidden activations, adding filter lengths, strides, and the
valid-convolution length equations. The output head has no activation. Parameters contain
one filter and one shared scalar bias per layer; bias-free parameters contain only filters.

Evaluation reuses the MLP prefix evaluator through the structured convolution matrices.
The prefix recursion is expressed as a filter sum, and the comparison with dense evaluation
retains the complete parameter product without claiming that different filters realize
different functions. These realization maps instantiate the neuromanifold and fibre API
directly. Empty chains realize the identity, and one-layer chains are the existing valid
convolution constructors.

The convention follows Vahid Shahverdi, *Algebraic Complexity and Neurovariety of Linear
Convolutional Networks*, [arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1,
equations (2.1)–(2.2): zero-based indexing, no padding, and no filter reversal. As for the
single-layer API, no positivity assumptions are needed for evaluation; positive filter
lengths, strides, and output lengths give the usual valid convolutional networks.
-/

public section

namespace TauCeti.Neuromanifold

/-- Lengths and hidden activations for a finite valid-convolution network, with no activation
on the output head. The affine parameters use a scalar bias shared across each layer. -/
@[ext]
structure ConvolutionSpec (K : Type*) (L : ℕ) extends MLPSpec K L where
  /-- Number of filter coefficients at each layer. -/
  filterLength : Fin L → ℕ
  /-- Stride at each layer. -/
  stride : Fin L → ℕ
  /-- The input contains exactly the valid convolution windows. -/
  length_eq (i : Fin L) :
    width i.castSucc = stride i * (width i.succ - 1) + filterLength i

namespace ConvolutionSpec

variable {K : Type*} {L : ℕ}

/-- Bias-free parameters: one filter for every layer. -/
abbrev Weights (A : ConvolutionSpec K L) := (i : Fin L) → Fin (A.filterLength i) → K

/-- Affine parameters: one filter and one shared scalar bias for every layer. -/
abbrev Parameters (A : ConvolutionSpec K L) :=
  (i : Fin L) → (Fin (A.filterLength i) → K) × K

/-- One coordinate per filter entry and one shared bias coordinate per layer. -/
abbrev ParameterIndex (A : ConvolutionSpec K L) :=
  (i : Fin L) × (Fin (A.filterLength i) ⊕ Unit)

/-- One coordinate per filter entry, with no bias coordinates. -/
abbrev WeightIndex (A : ConvolutionSpec K L) := (i : Fin L) × Fin (A.filterLength i)

/-- Reconstruct the full affine parameter product from its scalar coordinates. -/
def parameterEquiv (A : ConvolutionSpec K L) : (A.ParameterIndex → K) ≃ A.Parameters :=
  (Equiv.piCurry fun _ _ => K).trans
    (Equiv.piCongrRight fun i => affineConvolutionParameterEquiv K (A.filterLength i))

/-- Scalar filter coordinates reconstruct the filter at the specified layer. -/
@[simp] theorem parameterEquiv_apply_fst (A : ConvolutionSpec K L)
    (p : A.ParameterIndex → K) (i : Fin L) (j : Fin (A.filterLength i)) :
    (A.parameterEquiv p i).1 j = p ⟨i, Sum.inl j⟩ := by
  simp [parameterEquiv, Sigma.curry]

/-- Each layer has a single shared bias coordinate. -/
@[simp] theorem parameterEquiv_apply_snd (A : ConvolutionSpec K L)
    (p : A.ParameterIndex → K) (i : Fin L) :
    (A.parameterEquiv p i).2 = p ⟨i, Sum.inr ()⟩ := by
  simp [parameterEquiv, Sigma.curry]

/-- Flattening affine parameters recovers each filter entry. -/
@[simp] theorem parameterEquiv_symm_apply_inl (A : ConvolutionSpec K L) (p : A.Parameters)
    (i : Fin L) (j : Fin (A.filterLength i)) :
    A.parameterEquiv.symm p ⟨i, Sum.inl j⟩ = (p i).1 j := by
  simp [parameterEquiv, Sigma.uncurry, Equiv.piCongrRight]

/-- Flattening affine parameters recovers the shared bias. -/
@[simp] theorem parameterEquiv_symm_apply_inr (A : ConvolutionSpec K L) (p : A.Parameters)
    (i : Fin L) (u : Unit) :
    A.parameterEquiv.symm p ⟨i, Sum.inr u⟩ = (p i).2 := by
  simp [parameterEquiv, Sigma.uncurry, Equiv.piCongrRight]

/-- Reconstruct the bias-free filter product from its scalar coordinates. -/
def weightEquiv (A : ConvolutionSpec K L) : (A.WeightIndex → K) ≃ A.Weights :=
  Equiv.piCurry fun _ _ => K

/-- Reconstruction selects the filter coordinate at the specified layer and position. -/
@[simp] theorem weightEquiv_apply (A : ConvolutionSpec K L) (w : A.WeightIndex → K)
    (i : Fin L) (j : Fin (A.filterLength i)) :
    A.weightEquiv w i j = w ⟨i, j⟩ := (rfl)

/-- Flattening the bias-free product recovers every filter entry. -/
@[simp] theorem weightEquiv_symm_apply (A : ConvolutionSpec K L) (w : A.Weights)
    (i : Fin L) (j : Fin (A.filterLength i)) :
    A.weightEquiv.symm w ⟨i, j⟩ = w i j := (rfl)

/-- Include bias-free filters in affine parameters by setting all shared biases to zero. -/
def zeroBias [Zero K] (A : ConvolutionSpec K L) (w : A.Weights) : A.Parameters :=
  fun i => (w i, 0)

/-- The zero-bias inclusion retains each filter and sets its bias to zero. -/
@[simp] theorem zeroBias_apply [Zero K] (A : ConvolutionSpec K L) (w : A.Weights)
    (i : Fin L) : A.zeroBias w i = (w i, 0) := (rfl)

/-- The inclusion introduces no redundant bias coordinates into the filter parameter space. -/
theorem zeroBias_injective [Zero K] (A : ConvolutionSpec K L) :
    Function.Injective A.zeroBias :=
  fun _ _ h => funext fun i => congrArg Prod.fst (congrFun h i)

section Parameters

variable [AddCommMonoid K]

/-- Replace every filter by its structured convolution matrix. -/
def denseWeights (A : ConvolutionSpec K L) (w : A.Weights) : A.toMLPSpec.Weights :=
  fun i => convolutionMatrix (A.length_eq i) (w i)

/-- The matrix at each layer is the structured matrix of its filter. -/
@[simp] theorem denseWeights_apply (A : ConvolutionSpec K L) (w : A.Weights) (i : Fin L) :
    A.denseWeights w i = convolutionMatrix (A.length_eq i) (w i) := (rfl)

/-- Replace filters by convolution matrices and scalar biases by constant bias vectors. -/
def denseParameters (A : ConvolutionSpec K L) (p : A.Parameters) : A.toMLPSpec.Parameters :=
  fun i => (convolutionMatrix (A.length_eq i) (p i).1, fun _ => (p i).2)

/-- Structured affine parameters have a convolution matrix and a constant bias vector. -/
@[simp] theorem denseParameters_apply (A : ConvolutionSpec K L) (p : A.Parameters)
    (i : Fin L) : A.denseParameters p i =
      (convolutionMatrix (A.length_eq i) (p i).1, fun _ => (p i).2) := (rfl)

/-- Passing to structured dense parameters commutes with setting all biases to zero. -/
@[simp] theorem denseParameters_zeroBias (A : ConvolutionSpec K L) (w : A.Weights) :
    A.denseParameters (A.zeroBias w) = A.toMLPSpec.zeroBias (A.denseWeights w) := by
  funext i
  simp only [denseParameters_apply, zeroBias_apply, MLPSpec.zeroBias_apply, denseWeights_apply,
    Pi.zero_def]

end Parameters

section Evaluation

variable [NonUnitalNonAssocSemiring K]

/-- Evaluate every prefix through its structured dense parameters. -/
def evalPrefix (A : ConvolutionSpec K L) (p : A.Parameters) (x : Fin (A.width 0) → K) :
    (i : Fin (L + 1)) → Fin (A.width i) → K :=
  A.toMLPSpec.evalPrefix (A.denseParameters p) x

/-- Prefix evaluation agrees with the existing MLP evaluator at structured parameters. -/
theorem evalPrefix_eq_mlp (A : ConvolutionSpec K L) (p : A.Parameters)
    (x : Fin (A.width 0) → K) :
    A.evalPrefix p x = A.toMLPSpec.evalPrefix (A.denseParameters p) x := (rfl)

/-- The empty prefix is the input. -/
@[simp] theorem evalPrefix_zero (A : ConvolutionSpec K L) (p : A.Parameters)
    (x : Fin (A.width 0) → K) : A.evalPrefix p x 0 = x := by
  simp [evalPrefix_eq_mlp]

/-- A convolutional prefix applies its filter sum and shared bias, followed by the hidden
activation; at the output layer the activation is the identity. -/
@[simp] theorem evalPrefix_succ (A : ConvolutionSpec K L) (p : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix p x i.succ = fun a => A.toMLPSpec.layerActivation i
      ((∑ j : Fin (A.filterLength i), (p i).1 j *
        A.evalPrefix p x i.castSucc (convolutionIndex (A.length_eq i) a j)) + (p i).2) := by
  simp [evalPrefix_eq_mlp, convolutionMatrix_mulVec]

/-- The realization of the full affine convolutional network. -/
def realize (A : ConvolutionSpec K L) (p : A.Parameters) (x : Fin (A.width 0) → K) :
    Fin (A.width (Fin.last L)) → K :=
  A.evalPrefix p x (Fin.last L)

/-- Realization is evaluation of the final prefix. -/
theorem realize_def (A : ConvolutionSpec K L) (p : A.Parameters)
    (x : Fin (A.width 0) → K) :
    A.realize p x = A.evalPrefix p x (Fin.last L) := (rfl)

/-- Convolutional realization is dense MLP realization at structured parameters. -/
theorem realize_eq_mlp (A : ConvolutionSpec K L) :
    A.realize = A.toMLPSpec.realize ∘ A.denseParameters := by
  funext p x
  rw [realize_def, evalPrefix_eq_mlp, Function.comp_apply, MLPSpec.realize_def]

/-- An empty convolutional network realizes the identity. -/
@[simp] theorem realize_depth_zero (A : ConvolutionSpec K 0) (p : A.Parameters) :
    A.realize p = id := by
  funext x
  simp [realize_eq_mlp]

/-- The final head is an affine convolution of the preceding hidden prefix. -/
theorem realize_succ (A : ConvolutionSpec K (L + 1)) (p : A.Parameters)
    (x : Fin (A.width 0) → K) :
    A.realize p x = affineConvolution (A.length_eq (Fin.last L)) (p (Fin.last L))
      (A.evalPrefix p x (Fin.last L).castSucc) := by
  funext a
  simp [realize_eq_mlp, MLPSpec.realize_succ, evalPrefix_eq_mlp,
    convolutionMatrix_mulVec]

/-- A one-layer network realizes exactly the affine convolution of its filter and bias. -/
@[simp] theorem realize_depth_one (A : ConvolutionSpec K 1) (p : A.Parameters) :
    A.realize p = affineConvolution (A.length_eq 0) (p 0) := by
  funext x
  simp [realize_succ]

/-- Bias-free realization has precisely the filters as its parameters. -/
def realizeWeights (A : ConvolutionSpec K L) :
    A.Weights → (Fin (A.width 0) → K) → Fin (A.width (Fin.last L)) → K :=
  A.realize ∘ A.zeroBias

/-- Bias-free realization restricts affine realization along the zero-bias inclusion. -/
theorem realizeWeights_def (A : ConvolutionSpec K L) :
    A.realizeWeights = A.realize ∘ A.zeroBias := (rfl)

/-- Bias-free convolutional realization agrees with dense MLP realization at the structured
convolution matrices, with no extra bias parameters. -/
theorem realizeWeights_eq_mlp (A : ConvolutionSpec K L) :
    A.realizeWeights = A.toMLPSpec.realizeWeights ∘ A.denseWeights := by
  funext w x
  simp [realizeWeights_def, realize_eq_mlp, MLPSpec.realizeWeights_def]

/-- An empty bias-free network realizes the identity. -/
@[simp] theorem realizeWeights_depth_zero (A : ConvolutionSpec K 0) (w : A.Weights) :
    A.realizeWeights w = id := by
  simp [realizeWeights_def]

/-- The bias-free output head applies just its convolution filter to the hidden prefix. -/
theorem realizeWeights_succ (A : ConvolutionSpec K (L + 1)) (w : A.Weights)
    (x : Fin (A.width 0) → K) :
    A.realizeWeights w x = convolution (A.length_eq (Fin.last L)) (w (Fin.last L))
      (A.evalPrefix (A.zeroBias w) x (Fin.last L).castSucc) := by
  simp [realizeWeights_def, realize_succ]

/-- A one-layer bias-free network is the valid convolution constructor. -/
@[simp] theorem realizeWeights_depth_one (A : ConvolutionSpec K 1) (w : A.Weights) :
    A.realizeWeights w = convolution (A.length_eq 0) (w 0) := by
  simp [realizeWeights_def]

end Evaluation

end ConvolutionSpec

end TauCeti.Neuromanifold
