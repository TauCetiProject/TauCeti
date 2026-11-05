/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Polynomial
public import TauCeti.Geometry.Neuromanifold.Polynomial.Map

/-!
# Scalar transport of polynomial convolutional chains

Mapping the coefficients of the hidden activation polynomials transports a fixed valid
convolutional architecture to a new coefficient semiring. The joint polynomial tuple commutes
with this transport, as does realization at mapped filters, shared biases and inputs. Bias-free
transport uses only the filter product, without adding bias parameters.

Over an infinite integral domain, an injective scalar homomorphism preserves and reflects
equality of realized functions at mapped parameters. In particular, the results apply to
`Complex.ofRealHom` for real-to-complex evaluation and fibre comparison. They do not identify
real and complex images or claim that every complex parameter comes from a real parameter.

The polynomial viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. The convolution convention
follows Shahverdi, *Algebraic Complexity and Neurovariety of Linear Convolutional Networks*,
[arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1. Coefficient transport and
function comparison reuse `MvPolynomial.map` and `polynomialRealization_map_eq_iff`.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold.ConvolutionSpec

open MvPolynomial

variable {K R : Type*} {L : ℕ}

section CommSemiring

variable [CommSemiring K] [CommSemiring R]
variable (φ : K →+* R) (d : Fin (L + 1) → ℕ) (k s : Fin L → ℕ)
variable (h : ∀ i : Fin L, d i.castSucc = s i * (d i.succ - 1) + k i)
variable (q : Fin (L - 1) → Polynomial K)

/-- Mapping coefficients commutes with every polynomial convolutional prefix, retaining the
filter lengths, strides, and shared-bias coordinates. -/
@[simp] theorem map_polynomialPrefix (i : Fin (L + 1)) (a : Fin (d i)) :
    map φ ((polynomial d k s h q).polynomialPrefix q i a) =
      (polynomial d k s h (fun j => (q j).map φ)).polynomialPrefix
        (fun j => (q j).map φ) i a := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    simp only [polynomialPrefix_succ]
    split_ifs
    · rw [Polynomial.map_aeval_eq_aeval_map (map_comp_C φ).symm]
      simp [ih]
    · simp [ih]

/-- Transporting the affine polynomial tuple maps each hidden activation polynomial. -/
@[simp] theorem map_polynomialRealize (a : Fin (d (Fin.last L))) :
    map φ ((polynomial d k s h q).polynomialRealize q a) =
      (polynomial d k s h (fun j => (q j).map φ)).polynomialRealize
        (fun j => (q j).map φ) a := by
  simpa only [polynomialRealize_def] using map_polynomialPrefix φ d k s h q (Fin.last L) a

/-- The joint polynomial tuple commutes with scalar transport as a function. -/
theorem map_comp_polynomialRealize :
    map φ ∘ (polynomial d k s h q).polynomialRealize q =
      (polynomial d k s h (fun j => (q j).map φ)).polynomialRealize
        (fun j => (q j).map φ) :=
  funext (map_polynomialRealize φ d k s h q)

/-- Transporting the bias-free polynomial tuple commutes with zero-bias substitution. -/
@[simp] theorem map_polynomialRealizeWeights (a : Fin (d (Fin.last L))) :
    map φ ((polynomial d k s h q).polynomialRealizeWeights q a) =
      (polynomial d k s h (fun j => (q j).map φ)).polynomialRealizeWeights
        (fun j => (q j).map φ) a := by
  simp only [polynomialRealizeWeights_def, map_polynomialReparametrize]
  congr 1
  · funext ⟨i, j⟩
    cases j <;> simp
  · funext b
    exact map_polynomialRealize φ d k s h q b

/-- Map each filter coefficient and shared bias along the scalar homomorphism. -/
def mapParameters (p : (polynomial d k s h q).Parameters) :
    (polynomial d k s h (fun j => (q j).map φ)).Parameters :=
  fun i => (φ ∘ (p i).1, φ (p i).2)

/-- Scalar transport maps the filter and shared bias at each layer. -/
@[simp] theorem mapParameters_apply (p : (polynomial d k s h q).Parameters) (i : Fin L) :
    mapParameters φ d k s h q p i = (φ ∘ (p i).1, φ (p i).2) := (rfl)

/-- Reconstructing affine parameters commutes with mapping their scalar coordinates. -/
@[simp] theorem parameterEquiv_polynomial_map
    (p : (polynomial d k s h q).ParameterIndex → K) :
    (polynomial d k s h (fun j => (q j).map φ)).parameterEquiv (φ ∘ p) =
      mapParameters φ d k s h q ((polynomial d k s h q).parameterEquiv p) := by
  funext i
  ext j <;> simp [Function.comp_apply]

/-- Mapping affine parameters commutes with the zero-bias inclusion. -/
@[simp] theorem mapParameters_zeroBias (w : (polynomial d k s h q).Weights) :
    mapParameters φ d k s h q ((polynomial d k s h q).zeroBias w) =
      (polynomial d k s h (fun j => (q j).map φ)).zeroBias (fun i => φ ∘ w i) := by
  funext i
  simp

/-- Realization of the transported affine chain at mapped filters, shared biases and inputs
is the scalar image of the original realization. -/
@[simp] theorem realize_polynomial_map
    (p : (polynomial d k s h q).Parameters) (x : Fin (d 0) → K) :
    (polynomial d k s h (fun j => (q j).map φ)).realize
        (mapParameters φ d k s h q p) (φ ∘ x) =
      φ ∘ (polynomial d k s h q).realize p x := by
  have H := polynomialRealization_map φ
    ((polynomial d k s h q).polynomialRealize q)
    ((polynomial d k s h q).parameterEquiv.symm p) x
  rw [map_comp_polynomialRealize, polynomialRealization_polynomial,
    polynomialRealization_polynomial] at H
  simpa only [Function.comp_apply, parameterEquiv_polynomial_map,
    Equiv.apply_symm_apply] using H

/-- The bias-free chain transports on its actual filter product. -/
@[simp] theorem realizeWeights_polynomial_map
    (w : (polynomial d k s h q).Weights) (x : Fin (d 0) → K) :
    (polynomial d k s h (fun j => (q j).map φ)).realizeWeights
        (fun i => φ ∘ w i) (φ ∘ x) =
      φ ∘ (polynomial d k s h q).realizeWeights w x := by
  simpa only [realizeWeights_def, Function.comp_apply, mapParameters_zeroBias] using
    realize_polynomial_map φ d k s h q ((polynomial d k s h q).zeroBias w) x

end CommSemiring

section Fibres

variable [CommRing K] [IsDomain K] [Infinite K] [CommSemiring R]
variable (φ : K →+* R) (d : Fin (L + 1) → ℕ) (k s : Fin L → ℕ)
variable (h : ∀ i : Fin L, d i.castSucc = s i * (d i.succ - 1) + k i)
variable (q : Fin (L - 1) → Polynomial K)

/-- Over an infinite integral domain, an injective scalar homomorphism preserves and reflects
parameter equivalence for the affine convolutional chain. Equality is at every input. -/
theorem realize_polynomial_map_eq_iff (hφ : Function.Injective φ)
    (p v : (polynomial d k s h q).Parameters) :
    (polynomial d k s h (fun j => (q j).map φ)).realize
        (mapParameters φ d k s h q p) =
      (polynomial d k s h (fun j => (q j).map φ)).realize
        (mapParameters φ d k s h q v) ↔
      (polynomial d k s h q).realize p = (polynomial d k s h q).realize v := by
  have H := polynomialRealization_map_eq_iff hφ
    ((polynomial d k s h q).polynomialRealize q)
    ((polynomial d k s h q).parameterEquiv.symm p)
    ((polynomial d k s h q).parameterEquiv.symm v)
  rw [map_comp_polynomialRealize, polynomialRealization_polynomial,
    polynomialRealization_polynomial] at H
  simpa only [Function.comp_apply, parameterEquiv_polynomial_map,
    Equiv.apply_symm_apply] using H

/-- The same all-input function comparison holds on the weight-only parameter space. -/
theorem realizeWeights_polynomial_map_eq_iff (hφ : Function.Injective φ)
    (w v : (polynomial d k s h q).Weights) :
    (polynomial d k s h (fun j => (q j).map φ)).realizeWeights (fun i => φ ∘ w i) =
      (polynomial d k s h (fun j => (q j).map φ)).realizeWeights (fun i => φ ∘ v i) ↔
      (polynomial d k s h q).realizeWeights w =
        (polynomial d k s h q).realizeWeights v := by
  simpa only [realizeWeights_def, Function.comp_apply, mapParameters_zeroBias] using
    realize_polynomial_map_eq_iff φ d k s h q hφ
      ((polynomial d k s h q).zeroBias w) ((polynomial d k s h q).zeroBias v)

end Fibres

end TauCeti.Neuromanifold.ConvolutionSpec
