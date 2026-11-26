/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# One-hidden-layer networks on real inner product spaces

A fixed-width network computes an affine combination of scalar activations of affine inner
products. The output bias allows constant functions even at width zero. Allowing arbitrary width
gives the linear span of the constants and the individual hidden units. This description lets
approximation arguments work with sums and scalar multiples without tracking widths.

For the finite-dimensional model, see Allan Pinkus, *Approximation theory of the MLP model in
neural networks*, Acta Numerica 8 (1999), §§2–3.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

/-- A scalar-output network with one hidden layer of width `m` and input space `E`. -/
@[ext]
structure ShallowNet (E : Type*) (m : ℕ) where
  /-- The weight vector of each hidden unit. -/
  weight : Fin m → E
  /-- The bias of each hidden unit. -/
  bias : Fin m → ℝ
  /-- The output coefficient of each hidden unit. -/
  coeff : Fin m → ℝ
  /-- The bias of the output. -/
  outBias : ℝ

namespace ShallowNet

variable {E : Type*} {m n : ℕ}

/-- The width-zero network with the given output bias. -/
def const (c : ℝ) : ShallowNet E 0 :=
  ⟨Fin.elim0, Fin.elim0, Fin.elim0, c⟩

/-- The output bias of a constant network is its specified value. -/
@[simp] theorem outBias_const (c : ℝ) : (const c : ShallowNet E 0).outBias = c := (rfl)

/-- The width-one network for a single hidden unit, with output coefficient one and zero output
bias. -/
def single (w : E) (b : ℝ) : ShallowNet E 1 :=
  ⟨fun _ => w, fun _ => b, fun _ => 1, 0⟩

/-- Concatenate the hidden units and add the output biases. -/
def append (N : ShallowNet E m) (M : ShallowNet E n) : ShallowNet E (m + n) where
  weight := Fin.append N.weight M.weight
  bias := Fin.append N.bias M.bias
  coeff := Fin.append N.coeff M.coeff
  outBias := N.outBias + M.outBias

/-- Scale the output coefficients and output bias. -/
def scaleOutput (N : ShallowNet E m) (c : ℝ) : ShallowNet E m :=
  { N with coeff := fun i => c * N.coeff i, outBias := c * N.outBias }

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evaluate the hidden units with activation `σ` and combine them with the output coefficients
and output bias. -/
noncomputable def eval (N : ShallowNet E m) (σ : ℝ → ℝ) (x : E) : ℝ :=
  (∑ i, N.coeff i * σ (⟪N.weight i, x⟫ + N.bias i)) + N.outBias

/-- The evaluation formula for a one-hidden-layer network. -/
theorem eval_apply (N : ShallowNet E m) (σ : ℝ → ℝ) (x : E) :
    N.eval σ x = (∑ i, N.coeff i * σ (⟪N.weight i, x⟫ + N.bias i)) + N.outBias := (rfl)

/-- With no hidden units, evaluation returns the output bias. -/
@[simp] theorem eval_width_zero (N : ShallowNet E 0) (σ : ℝ → ℝ) (x : E) :
    N.eval σ x = N.outBias := by
  simp [eval_apply]

/-- The single-unit network evaluates to the activation of its affine inner product. -/
@[simp] theorem eval_single (w : E) (b : ℝ) (σ : ℝ → ℝ) (x : E) :
    (single w b).eval σ x = σ (⟪w, x⟫ + b) := by
  simp [eval_apply, single]

/-- A concatenation evaluates to the sum of the two outputs. -/
@[simp] theorem eval_append (N : ShallowNet E m) (M : ShallowNet E n) (σ : ℝ → ℝ) (x : E) :
    (N.append M).eval σ x = N.eval σ x + M.eval σ x := by
  simp only [eval_apply, append, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  abel

/-- Scaling the output parameters scales the realized function. -/
@[simp] theorem eval_scaleOutput (N : ShallowNet E m) (c : ℝ) (σ : ℝ → ℝ) (x : E) :
    (N.scaleOutput c).eval σ x = c * N.eval σ x := by
  simp only [eval_apply, scaleOutput, mul_add, Finset.mul_sum, mul_assoc]

/-- Precompose a network with the input map `x ↦ a • x + v`. -/
noncomputable def compAffine (N : ShallowNet E m) (a : ℝ) (v : E) : ShallowNet E m :=
  { N with weight := fun i => a • N.weight i, bias := fun i => ⟪N.weight i, v⟫ + N.bias i }

/-- The transformed parameters evaluate at the dilated and translated input. -/
@[simp] theorem eval_compAffine (N : ShallowNet E m) (a : ℝ) (v : E) (σ : ℝ → ℝ) (x : E) :
    (N.compAffine a v).eval σ x = N.eval σ (a • x + v) := by
  simp only [eval_apply, compAffine, real_inner_smul_left, inner_add_right, real_inner_smul_right,
    add_assoc]

/-- Pull back a univariate network along the inner product with `v`. -/
noncomputable def compInner (N : ShallowNet ℝ m) (v : E) : ShallowNet E m where
  weight i := N.weight i • v
  bias := N.bias
  coeff := N.coeff
  outBias := N.outBias

/-- The pulled-back network evaluates the original network at the inner product with `v`. -/
@[simp] theorem eval_compInner (N : ShallowNet ℝ m) (v : E) (σ : ℝ → ℝ) (x : E) :
    (N.compInner v).eval σ x = N.eval σ ⟪v, x⟫ := by
  simp [eval_apply, compInner, real_inner_smul_left, mul_comm]

/-- The zero activation leaves only the output bias. -/
@[simp] theorem eval_zero (N : ShallowNet E m) (x : E) : N.eval 0 x = N.outBias := by
  simp [eval_apply]

/-- With identity activation, the realized function is affine, with a weight vector given by
the output-weighted sum of the hidden weight vectors. -/
theorem eval_id (N : ShallowNet E m) (x : E) :
    N.eval id x = ⟪∑ i, N.coeff i • N.weight i, x⟫ +
      ((∑ i, N.coeff i * N.bias i) + N.outBias) := by
  simp only [eval_apply, id_eq, mul_add, Finset.sum_add_distrib, sum_inner, real_inner_smul_left,
    add_assoc]

/-- A network with continuous activation realizes a continuous function. -/
@[fun_prop] theorem continuous_eval (N : ShallowNet E m) {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Continuous (N.eval σ) := by
  unfold eval
  fun_prop

end ShallowNet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {σ : ℝ → ℝ}

/-- Functions realized by a one-hidden-layer network of any finite width with activation `σ`. -/
def shallowNetFunctions (σ : ℝ → ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set (E → ℝ) :=
  {f | ∃ (m : ℕ) (N : ShallowNet E m), N.eval σ = f}

/-- Membership is equivalent to realization by a network of some width. -/
theorem mem_shallowNetFunctions {f : E → ℝ} :
    f ∈ shallowNetFunctions σ E ↔ ∃ (m : ℕ) (N : ShallowNet E m), N.eval σ = f := (Iff.rfl)

/-- The realization of any fixed-width network belongs to the family over all widths. -/
@[simp] theorem ShallowNet.eval_mem_shallowNetFunctions {m : ℕ} (N : ShallowNet E m)
    (σ : ℝ → ℝ) : N.eval σ ∈ shallowNetFunctions σ E :=
  mem_shallowNetFunctions.mpr ⟨m, N, rfl⟩

/-- Constant functions belong to the network family for every activation. -/
@[simp] theorem const_mem_shallowNetFunctions (c : ℝ) :
    Function.const E c ∈ shallowNetFunctions σ E := by
  exact mem_shallowNetFunctions.mpr ⟨0, .const c, funext fun _ => by simp⟩

/-- A single activated affine inner product belongs to the network family. -/
theorem single_mem_shallowNetFunctions (w : E) (b : ℝ) :
    (fun x => σ (⟪w, x⟫ + b)) ∈ shallowNetFunctions σ E :=
  mem_shallowNetFunctions.mpr ⟨1, .single w b, funext fun x => ShallowNet.eval_single w b σ x⟩

/-- With zero activation, the realizations are exactly the constant functions. -/
theorem shallowNetFunctions_zero :
    shallowNetFunctions 0 E = Set.range (Function.const E) := by
  ext f
  constructor
  · intro hf
    obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf
    exact ⟨N.outBias, funext fun x => (N.eval_zero x).symm⟩
  · rintro ⟨c, rfl⟩
    exact const_mem_shallowNetFunctions c

/-- With identity activation, the realizations are exactly the affine inner products.
Every such function is realized at width one. -/
theorem shallowNetFunctions_id :
    shallowNetFunctions id E = Set.range (fun wb : E × ℝ => fun x => ⟪wb.1, x⟫ + wb.2) := by
  ext f
  constructor
  · intro hf
    obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf
    exact ⟨(∑ i, N.coeff i • N.weight i, (∑ i, N.coeff i * N.bias i) + N.outBias),
      funext fun x => (N.eval_id x).symm⟩
  · rintro ⟨⟨w, b⟩, rfl⟩
    exact single_mem_shallowNetFunctions (σ := id) w b

/-- The family of one-hidden-layer realizations, bundled as a linear subspace. -/
def shallowNetSubmodule (σ : ℝ → ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Submodule ℝ (E → ℝ) where
  carrier := shallowNetFunctions σ E
  zero_mem' := const_mem_shallowNetFunctions 0
  add_mem' := by
    intro f g hf hg
    obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf
    obtain ⟨n, M, rfl⟩ := mem_shallowNetFunctions.mp hg
    exact mem_shallowNetFunctions.mpr ⟨m + n, N.append M, funext fun x => N.eval_append M σ x⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf
    exact mem_shallowNetFunctions.mpr ⟨m, N.scaleOutput c, funext fun x => N.eval_scaleOutput c σ x⟩

/-- The carrier of the network submodule is the family of all realizations. -/
@[simp] theorem coe_shallowNetSubmodule (σ : ℝ → ℝ) :
    (shallowNetSubmodule σ E : Set (E → ℝ)) = shallowNetFunctions σ E := (rfl)

/-- Network functions are closed under precomposition by a dilation and translation. -/
theorem compAffine_mem_shallowNetFunctions {f : E → ℝ} (hf : f ∈ shallowNetFunctions σ E)
    (a : ℝ) (v : E) : (fun x => f (a • x + v)) ∈ shallowNetFunctions σ E := by
  obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf
  exact mem_shallowNetFunctions.mpr ⟨m, N.compAffine a v, funext fun x => N.eval_compAffine a v σ x⟩

/-- Pulling back a univariate network function along an inner product gives a network function. -/
theorem compInner_mem_shallowNetFunctions {f : ℝ → ℝ} (hf : f ∈ shallowNetFunctions σ ℝ)
    (v : E) : (fun x => f ⟪v, x⟫) ∈ shallowNetFunctions σ E := by
  obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf
  exact mem_shallowNetFunctions.mpr ⟨m, N.compInner v, funext fun x => N.eval_compInner v σ x⟩

/-- The network submodule is the span of the constant functions and the single activated affine
inner products. -/
theorem shallowNetSubmodule_eq_span (σ : ℝ → ℝ) :
    shallowNetSubmodule σ E = Submodule.span ℝ
      (Set.range (Function.const E) ∪
        Set.range (fun wb : E × ℝ => fun x => σ (⟪wb.1, x⟫ + wb.2))) := by
  let S := Submodule.span ℝ
    (Set.range (Function.const E) ∪ Set.range (fun wb : E × ℝ => fun x => σ (⟪wb.1, x⟫ + wb.2)))
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.mpr ?_)
  · have hf' : f ∈ shallowNetFunctions σ E := hf
    obtain ⟨m, N, rfl⟩ := mem_shallowNetFunctions.mp hf'
    have hsum : (∑ i, N.coeff i • fun x => σ (⟪N.weight i, x⟫ + N.bias i)) ∈ S :=
      S.sum_mem fun i _ =>
        S.smul_mem _ (Submodule.subset_span (Or.inr ⟨(N.weight i, N.bias i), rfl⟩))
    have hbias : Function.const E N.outBias ∈ S := Submodule.subset_span (Or.inl ⟨_, rfl⟩)
    have heval : N.eval σ =
        (∑ i, N.coeff i • fun x => σ (⟪N.weight i, x⟫ + N.bias i)) +
          Function.const E N.outBias := by
      funext x
      simp [ShallowNet.eval_apply, Finset.sum_apply]
    rw [heval]
    exact S.add_mem hsum hbias
  · rintro f (⟨c, rfl⟩ | ⟨⟨w, b⟩, rfl⟩)
    · exact const_mem_shallowNetFunctions c
    · exact single_mem_shallowNetFunctions w b

end TauCeti
