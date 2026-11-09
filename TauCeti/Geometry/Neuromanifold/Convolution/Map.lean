/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Polynomial
public import TauCeti.Geometry.Neuromanifold.Polynomial.Map

/-!
# Scalar transport of polynomial convolutional networks

`ConvolutionSpec.polynomial` retains a convolutional specification's lengths, filters and
strides and replaces its hidden activations by polynomial evaluation, possibly over another
scalar semiring. Mapping these polynomials along a scalar homomorphism maps the joint
polynomial tuple coefficientwise. Consequently, evaluating the transported network at mapped
filters, shared biases and inputs gives the mapped original output. Both affine and bias-free
parameter spaces are retained, with no extra coordinates.

The prefix and final polynomial comparisons connect concrete convolutional architectures to
coefficient transport for arbitrary jointly polynomial models. They include empty chains,
empty filters and constant activations. The real-to-complex equations concern mapped real
parameters and inputs; they do not identify the real and complex images or fibres.
Over an infinite integral domain, an injective scalar homomorphism preserves and reflects
all-input function equality at mapped parameters, for both affine and bias-free chains.

The polynomial viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. The convolution convention is
Shahverdi's, *Algebraic Complexity and Neurovariety of Linear Convolutional Networks*,
[arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold.ConvolutionSpec

variable {S K R : Type*} {L : ℕ}

/-- Keep the geometric data of `A` and use `q` as the hidden activation polynomials over `K`.
The original scalar type and activations of `A` are used only as a shape template.
The body is exposed so that parameter and input index types compute to the same types as
those of `A`, independently of the new coefficient semiring. -/
@[expose] def polynomial [Semiring K] (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) : ConvolutionSpec K L where
  width := A.width
  activation j t := (q j).eval t
  filterLength := A.filterLength
  stride := A.stride
  length_eq := A.length_eq

/-- Replacing activations preserves all widths. -/
@[simp] theorem polynomial_width [Semiring K] (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) : (A.polynomial q).width = A.width := (rfl)

/-- Replacing activations preserves the filter lengths. -/
@[simp] theorem polynomial_filterLength [Semiring K] (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) : (A.polynomial q).filterLength = A.filterLength := (rfl)

/-- Replacing activations preserves the strides. -/
@[simp] theorem polynomial_stride [Semiring K] (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) : (A.polynomial q).stride = A.stride := (rfl)

/-- The new hidden activation evaluates its specified polynomial. -/
@[simp] theorem polynomial_activation [Semiring K] (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (j : Fin (L - 1)) (t : K) :
    (A.polynomial q).activation j t = (q j).eval t := (rfl)

/-- Only the last choice of activation polynomials matters. -/
@[simp] theorem polynomial_polynomial [Semiring K] [Semiring R] (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (r : Fin (L - 1) → Polynomial R) :
    (A.polynomial q).polynomial r = A.polynomial r := (rfl)

/-- A specification already using these polynomial activations is unchanged. -/
theorem polynomial_eq_self [Semiring K] (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (hq : ∀ j t, A.activation j t = (q j).eval t) :
    A.polynomial q = A := by
  ext <;> simp [hq]

section Transport

variable [CommSemiring K] [CommSemiring R]

/-- Every joint prefix polynomial transports coefficientwise when its hidden activation
polynomials are mapped along the scalar homomorphism. -/
@[simp] theorem map_polynomialPrefix (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (i : Fin (L + 1))
    (a : Fin (A.width i)) :
    MvPolynomial.map φ (A.polynomialPrefix q i a) =
      (A.polynomial (Polynomial.map φ ∘ q)).polynomialPrefix (Polynomial.map φ ∘ q) i a := by
  -- Compute the common index types even when the scalar types live in different universes.
  dsimp only [polynomial]
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [polynomialPrefix_succ, polynomialPrefix_succ]
    dsimp only
    split_ifs with h
    · rw [Polynomial.map_aeval_eq_aeval_map (MvPolynomial.map_comp_C φ).symm]
      simp [ih]
    · simp [ih]

/-- The full affine joint polynomial tuple transports coefficientwise. -/
@[simp] theorem map_polynomialRealize (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (a : Fin (A.width (Fin.last L))) :
    MvPolynomial.map φ (A.polynomialRealize q a) =
      (A.polynomial (Polynomial.map φ ∘ q)).polynomialRealize (Polynomial.map φ ∘ q) a := by
  dsimp only [polynomial]
  rw [polynomialRealize_def, polynomialRealize_def]
  exact A.map_polynomialPrefix q φ (Fin.last L) a

/-- The bias-free tuple transports coefficientwise, keeping only the filter variables. -/
@[simp] theorem map_polynomialRealizeWeights (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (a : Fin (A.width (Fin.last L))) :
    MvPolynomial.map φ (A.polynomialRealizeWeights q a) =
      (A.polynomial (Polynomial.map φ ∘ q)).polynomialRealizeWeights
        (Polynomial.map φ ∘ q) a := by
  dsimp only [polynomial]
  rw [polynomialRealizeWeights_def, map_polynomialReparametrize,
    polynomialRealizeWeights_def]
  congr 1
  · funext p
    rcases p with ⟨i, j⟩
    cases j <;> simp
  · funext j
    exact A.map_polynomialRealize q φ j

end Transport

section Evaluation

variable [Semiring K] [Semiring R]

/-- Scalar transport commutes with every convolutional prefix, mapping each filter entry
and the shared scalar bias. -/
@[simp] theorem evalPrefix_polynomial_map (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (p : (A.polynomial q).Parameters)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) (a : Fin (A.width i)) :
    (A.polynomial (Polynomial.map φ ∘ q)).evalPrefix
        (fun i => (φ ∘ (p i).1, φ (p i).2)) (φ ∘ x) i a =
      φ ((A.polynomial q).evalPrefix p x i a) := by
  dsimp only [polynomial] at p ⊢
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [evalPrefix_succ, evalPrefix_succ]
    dsimp only [Function.comp_apply] at ih ⊢
    by_cases h : i.val + 1 < L
    · rw [MLPSpec.layerActivation_of_lt _ _ h, MLPSpec.layerActivation_of_lt _ _ h]
      simp only [ih, ← map_mul, ← map_sum, ← map_add]
      simp only [Polynomial.eval_map_apply]
    · have hi : i.val + 1 = L := by omega
      rw [MLPSpec.layerActivation_of_val_add_one_eq _ _ hi,
        MLPSpec.layerActivation_of_val_add_one_eq _ _ hi]
      simp only [id_eq, ih, ← map_mul, ← map_sum, ← map_add]

/-- Scalar transport commutes with convolutional realization on the complete affine
parameter product: filters and the shared bias are both mapped. -/
@[simp] theorem realize_polynomial_map (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (p : (A.polynomial q).Parameters)
    (x : Fin (A.width 0) → K) :
    (A.polynomial (Polynomial.map φ ∘ q)).realize
        (fun i => (φ ∘ (p i).1, φ (p i).2)) (φ ∘ x) =
      φ ∘ (A.polynomial q).realize p x := by
  dsimp only [polynomial] at p ⊢
  funext a
  rw [realize_def, realize_def]
  exact A.evalPrefix_polynomial_map q φ p x (Fin.last L) a

/-- Reconstructing affine parameters from mapped scalar coordinates maps each filter and
shared bias. -/
@[simp] theorem parameterEquiv_polynomial_map (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (p : (A.polynomial q).Parameters) :
    (A.polynomial (Polynomial.map φ ∘ q)).parameterEquiv
        (φ ∘ (A.polynomial q).parameterEquiv.symm p) =
      (fun i => (φ ∘ (p i).1, φ (p i).2)) := by
  -- Explicit projection lemmas keep the dependent index types aligned across scalar universes.
  funext i
  apply Prod.ext
  · funext j
    exact ((A.polynomial (Polynomial.map φ ∘ q)).parameterEquiv_apply_fst _ i j).trans
      (congrArg φ ((A.polynomial q).parameterEquiv_symm_apply_inl p i j))
  · exact ((A.polynomial (Polynomial.map φ ∘ q)).parameterEquiv_apply_snd _ i).trans
      (congrArg φ ((A.polynomial q).parameterEquiv_symm_apply_inr p i ()))

/-- Mapping filters commutes with including them as affine parameters with zero biases. -/
@[simp] theorem zeroBias_polynomial_map (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (w : (A.polynomial q).Weights) :
    (A.polynomial (Polynomial.map φ ∘ q)).zeroBias (fun i => φ ∘ w i) =
      (fun i => (φ ∘ ((A.polynomial q).zeroBias w i).1,
        φ ((A.polynomial q).zeroBias w i).2)) := by
  dsimp only [polynomial] at w ⊢
  funext i
  simp

/-- Scalar transport commutes with bias-free convolutional realization on the filter-only
parameter product. -/
@[simp] theorem realizeWeights_polynomial_map (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (w : (A.polynomial q).Weights)
    (x : Fin (A.width 0) → K) :
    (A.polynomial (Polynomial.map φ ∘ q)).realizeWeights
        (fun i => φ ∘ w i) (φ ∘ x) = φ ∘ (A.polynomial q).realizeWeights w x := by
  rw [realizeWeights_def, realizeWeights_def, Function.comp_apply, Function.comp_apply,
    zeroBias_polynomial_map]
  exact A.realize_polynomial_map q φ ((A.polynomial q).zeroBias w) x

end Evaluation

/-- Complexifying a real polynomial convolutional network recovers its real outputs on
real filters, shared biases and inputs. -/
theorem realize_polynomial_ofReal (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial ℝ) (p : (A.polynomial q).Parameters)
    (x : Fin (A.width 0) → ℝ) (a : Fin (A.width (Fin.last L))) :
    (A.polynomial (Polynomial.map Complex.ofRealHom ∘ q)).realize
        (fun i => ((fun j => ((p i).1 j : ℂ)), ((p i).2 : ℂ)))
        (fun j => (x j : ℂ)) a = ((A.polynomial q).realize p x a : ℂ) :=
  congrFun (A.realize_polynomial_map q Complex.ofRealHom p x) a

/-- The real-to-complex evaluation equation also holds without any bias coordinates. -/
theorem realizeWeights_polynomial_ofReal (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial ℝ) (w : (A.polynomial q).Weights)
    (x : Fin (A.width 0) → ℝ) (a : Fin (A.width (Fin.last L))) :
    (A.polynomial (Polynomial.map Complex.ofRealHom ∘ q)).realizeWeights
        (fun i j => (w i j : ℂ)) (fun j => (x j : ℂ)) a =
      ((A.polynomial q).realizeWeights w x a : ℂ) :=
  congrFun (A.realizeWeights_polynomial_map q Complex.ofRealHom w x) a

section Fibres

variable [CommRing K] [IsDomain K] [Infinite K] [CommSemiring R]

/-- Over an infinite integral domain, an injective scalar homomorphism preserves and reflects
parameter equivalence for the affine convolutional chain. Equality is at every input. -/
theorem realize_polynomial_map_eq_iff (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (hφ : Function.Injective φ)
    (p v : (A.polynomial q).Parameters) :
    (A.polynomial (Polynomial.map φ ∘ q)).realize
        (fun i => (φ ∘ (p i).1, φ (p i).2)) =
      (A.polynomial (Polynomial.map φ ∘ q)).realize
        (fun i => (φ ∘ (v i).1, φ (v i).2)) ↔
      (A.polynomial q).realize p = (A.polynomial q).realize v := by
  have hmap : MvPolynomial.map φ ∘ (A.polynomial q).polynomialRealize q =
      (A.polynomial (Polynomial.map φ ∘ q)).polynomialRealize (Polynomial.map φ ∘ q) := by
    dsimp only [polynomial]
    exact funext ((A.polynomial q).map_polynomialRealize q φ)
  have heval := (A.polynomial q).polynomialRealization_polynomialRealize q
    (polynomial_activation A q)
  have heval' := (A.polynomial (Polynomial.map φ ∘ q)).polynomialRealization_polynomialRealize
    (Polynomial.map φ ∘ q) (polynomial_activation A (Polynomial.map φ ∘ q))
  have hsource (w : (A.polynomial q).Parameters) :
      polynomialRealization ((A.polynomial q).polynomialRealize q)
          ((A.polynomial q).parameterEquiv.symm w) = (A.polynomial q).realize w := by
    simp only [heval, Function.comp_apply, Equiv.apply_symm_apply]
  have htarget (w : (A.polynomial q).Parameters) :
      polynomialRealization (MvPolynomial.map φ ∘ (A.polynomial q).polynomialRealize q)
          (φ ∘ (A.polynomial q).parameterEquiv.symm w) =
        (A.polynomial (Polynomial.map φ ∘ q)).realize
          (fun i => (φ ∘ (w i).1, φ (w i).2)) := by
    have hp := A.parameterEquiv_polynomial_map q φ w
    -- Compute the common index types before rewriting between the two scalar universes.
    dsimp only [polynomial] at hmap heval' hp ⊢
    rw [hmap, heval', Function.comp_apply, hp]
  rw [← htarget p, ← htarget v, ← hsource p, ← hsource v]
  exact polynomialRealization_map_eq_iff hφ _ _ _

/-- The same all-input function comparison holds on the filter-only parameter space, with
no artificial bias coordinates. -/
theorem realizeWeights_polynomial_map_eq_iff (A : ConvolutionSpec S L)
    (q : Fin (L - 1) → Polynomial K) (φ : K →+* R) (hφ : Function.Injective φ)
    (w v : (A.polynomial q).Weights) :
    (A.polynomial (Polynomial.map φ ∘ q)).realizeWeights (fun i => φ ∘ w i) =
      (A.polynomial (Polynomial.map φ ∘ q)).realizeWeights (fun i => φ ∘ v i) ↔
      (A.polynomial q).realizeWeights w = (A.polynomial q).realizeWeights v := by
  simp only [realizeWeights_def, Function.comp_apply, zeroBias_polynomial_map]
  exact A.realize_polynomial_map_eq_iff q φ hφ _ _

end Fibres

end TauCeti.Neuromanifold.ConvolutionSpec
