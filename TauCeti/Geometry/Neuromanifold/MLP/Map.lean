/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Polynomial
public import TauCeti.Geometry.Neuromanifold.Polynomial.Map
-- The coefficient calculations inspect layer polynomials and the zero-bias substitution.
import all TauCeti.Geometry.Neuromanifold.MLP.Polynomial

/-!
# Scalar transport of polynomial MLPs

Mapping the coefficients of each hidden activation polynomial gives an MLP over the new
scalar semiring, with the same widths and an affine output head. Its joint polynomial tuple
is obtained by mapping coefficients of the original tuple. The same statement holds on the
weight-only parameter space, without introducing bias coordinates.

Mapping the actual weights, biases and inputs commutes with realization. Over an infinite
integral domain, an injective scalar homomorphism also preserves and reflects equality of
realized functions at mapped parameters. In particular, `Complex.ofRealHom` gives these
comparisons for real polynomial MLPs and their complexifications. These assertions compare
mapped parameters only: they do not identify the real and complex images or fibres.

The polynomial-model viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. The function comparison uses
`polynomialRealization_map_eq_iff`, based on Mathlib's polynomial extensionality over infinite
domains.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold.MLPSpec

open MvPolynomial

section Transport

variable {K K' : Type*} {L : ℕ} [CommSemiring K] [CommSemiring K']
variable (φ : K →+* K') (d : Fin (L + 1) → ℕ) (q : Fin (L - 1) → Polynomial K)

/-- Mapping hidden activation polynomials also maps the layer polynomials, including the
unchanged polynomial `X` of the output head. -/
@[simp] theorem map_layerPolynomial (i : Fin L) :
    (layerPolynomial q i).map φ = layerPolynomial (fun j => (q j).map φ) i := by
  unfold layerPolynomial
  split <;> simp

/-- Reassembling mapped affine coordinates maps each weight entry and bias coordinate. -/
@[simp] theorem parameterEquiv_map (v : (polynomial d q).ParameterIndex → K) :
    (polynomial d (fun j => (q j).map φ)).parameterEquiv (φ ∘ v) =
      fun i => (((polynomial d q).parameterEquiv v i).1.map φ,
        φ ∘ ((polynomial d q).parameterEquiv v i).2) := by
  -- Normalize the common widths in the dependent coordinate types and their instances.
  revert v
  dsimp +instances only [polynomial, ParameterIndex, Parameters]
  intro v
  funext i
  apply Prod.ext
  · ext o j
    simp [Matrix.map_apply, Function.comp_def]
  · funext o
    simp [Function.comp_def]

/-- Reassembling mapped weight-only coordinates maps each matrix entry. -/
@[simp] theorem weightEquiv_map (v : (polynomial d q).WeightIndex → K) :
    (polynomial d (fun j => (q j).map φ)).weightEquiv (φ ∘ v) =
      fun i => ((polynomial d q).weightEquiv v i).map φ := by
  revert v
  dsimp +instances only [polynomial, WeightIndex, Weights]
  intro v
  funext i o j
  simp [Matrix.map_apply, Function.comp_def]

/-- The joint polynomial of every prefix transports by mapping its scalar coefficients. -/
@[simp] theorem map_polynomialPrefix (i : Fin (L + 1)) (o : Fin (d i)) :
    map φ ((polynomial d q).polynomialPrefix q i o) =
      (polynomial d (fun j => (q j).map φ)).polynomialPrefix
        (fun j => (q j).map φ) i o := by
  -- Both specifications have widths `d`; normalize these also in polynomial instances.
  dsimp +instances only [polynomial, ParameterIndex] at *
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [polynomialPrefix_succ, polynomialPrefix_succ,
      Polynomial.map_aeval_eq_aeval_map (map_comp_C φ).symm, map_layerPolynomial]
    simp [ih]

/-- The joint polynomial tuple of the transported affine MLP is the coefficientwise image
of the original tuple. -/
@[simp] theorem map_polynomialRealize :
    map φ ∘ (polynomial d q).polynomialRealize q =
      (polynomial d (fun j => (q j).map φ)).polynomialRealize (fun j => (q j).map φ) := by
  funext o
  exact map_polynomialPrefix φ d q (Fin.last L) o

/-- Mapping scalar coefficients commutes with the substitution that sets biases to zero. -/
@[simp] theorem map_zeroBiasSubstitution (k : (polynomial d q).ParameterIndex) :
    map φ ((polynomial d q).zeroBiasSubstitution k) =
      (polynomial d (fun j => (q j).map φ)).zeroBiasSubstitution k := by
  revert k
  dsimp +instances only [polynomial, ParameterIndex, WeightIndex]
  rintro ⟨i, k⟩
  cases k <;> simp [zeroBiasSubstitution]

/-- The joint polynomial tuple of the transported bias-free MLP is the coefficientwise image
of the original weight-only tuple. -/
@[simp] theorem map_polynomialRealizeWeights :
    map φ ∘ (polynomial d q).polynomialRealizeWeights q =
      (polynomial d (fun j => (q j).map φ)).polynomialRealizeWeights
        (fun j => (q j).map φ) := by
  funext o
  rw [polynomialRealizeWeights_def, Function.comp_apply, polynomialRealizeWeights_def,
    map_polynomialReparametrize]
  have hq := map_polynomialRealize φ d q
  have hz : map φ ∘ (polynomial d q).zeroBiasSubstitution =
      (polynomial d (fun j => (q j).map φ)).zeroBiasSubstitution :=
    funext (map_zeroBiasSubstitution φ d q)
  dsimp +instances only [polynomial, ParameterIndex, WeightIndex] at *
  rw [hq, hz]

/-- Realization of the transported affine network at mapped weights, biases and inputs is the
mapped realization of the original network. -/
@[simp] theorem realize_polynomial_map (θ : (polynomial d q).Parameters) (x : Fin (d 0) → K) :
    (polynomial d (fun j => (q j).map φ)).realize
        (fun i => ((θ i).1.map φ, φ ∘ (θ i).2)) (φ ∘ x) =
      φ ∘ (polynomial d q).realize θ x := by
  have h := polynomialRealization_map φ ((polynomial d q).polynomialRealize q)
    ((polynomial d q).parameterEquiv.symm θ) x
  rw [map_polynomialRealize] at h
  have hs := (polynomial d q).polynomialRealization_polynomialRealize (fun _ _ => rfl)
  have ht := (polynomial d (fun j => (q j).map φ)).polynomialRealization_polynomialRealize
    (fun _ _ => rfl)
  have hc := parameterEquiv_map φ d q ((polynomial d q).parameterEquiv.symm θ)
  have he := (polynomial d q).parameterEquiv.apply_symm_apply θ
  dsimp +instances only [polynomial, ParameterIndex, Parameters] at *
  simpa only [hs, ht, Function.comp_apply, hc, he] using h

/-- Realization on the weight-only parameter space commutes with scalar transport. -/
@[simp] theorem realizeWeights_polynomial_map (w : (polynomial d q).Weights) (x : Fin (d 0) → K) :
    (polynomial d (fun j => (q j).map φ)).realizeWeights
        (fun i => (w i).map φ) (φ ∘ x) =
      φ ∘ (polynomial d q).realizeWeights w x := by
  have h := polynomialRealization_map φ ((polynomial d q).polynomialRealizeWeights q)
    ((polynomial d q).weightEquiv.symm w) x
  rw [map_polynomialRealizeWeights] at h
  have hs := (polynomial d q).polynomialRealization_polynomialRealizeWeights (fun _ _ => rfl)
  have ht := (polynomial d (fun j => (q j).map φ)).polynomialRealization_polynomialRealizeWeights
    (fun _ _ => rfl)
  have hc := weightEquiv_map φ d q ((polynomial d q).weightEquiv.symm w)
  have he := (polynomial d q).weightEquiv.apply_symm_apply w
  dsimp +instances only [polynomial, WeightIndex, Weights] at *
  simpa only [hs, ht, Function.comp_apply, hc, he] using h

end Transport

section Fibres

variable {K K' : Type*} {L : ℕ}
variable [CommRing K] [IsDomain K] [Infinite K] [CommSemiring K']
variable {φ : K →+* K'} (hφ : Function.Injective φ)
variable (d : Fin (L + 1) → ℕ) (q : Fin (L - 1) → Polynomial K)

include hφ

/-- Over an infinite integral domain, mapped affine parameters realize the same function over
the new scalars exactly when the original parameters realize the same function. -/
theorem realize_polynomial_map_eq_iff (θ η : (polynomial d q).Parameters) :
    (polynomial d (fun j => (q j).map φ)).realize
        (fun i => ((θ i).1.map φ, φ ∘ (θ i).2)) =
      (polynomial d (fun j => (q j).map φ)).realize
        (fun i => ((η i).1.map φ, φ ∘ (η i).2)) ↔
      (polynomial d q).realize θ = (polynomial d q).realize η := by
  have h := polynomialRealization_map_eq_iff hφ ((polynomial d q).polynomialRealize q)
    ((polynomial d q).parameterEquiv.symm θ) ((polynomial d q).parameterEquiv.symm η)
  rw [map_polynomialRealize] at h
  have hs := (polynomial d q).polynomialRealization_polynomialRealize (fun _ _ => rfl)
  have ht := (polynomial d (fun j => (q j).map φ)).polynomialRealization_polynomialRealize
    (fun _ _ => rfl)
  have hcθ := parameterEquiv_map φ d q ((polynomial d q).parameterEquiv.symm θ)
  have hcη := parameterEquiv_map φ d q ((polynomial d q).parameterEquiv.symm η)
  have heθ := (polynomial d q).parameterEquiv.apply_symm_apply θ
  have heη := (polynomial d q).parameterEquiv.apply_symm_apply η
  dsimp +instances only [polynomial, ParameterIndex, Parameters] at *
  simpa only [hs, ht, Function.comp_apply, hcθ, hcη, heθ, heη] using h

/-- Over an infinite integral domain, scalar transport preserves and reflects equality of
bias-free realized functions, on the original weight-only parameter space. -/
theorem realizeWeights_polynomial_map_eq_iff (w v : (polynomial d q).Weights) :
    (polynomial d (fun j => (q j).map φ)).realizeWeights (fun i => (w i).map φ) =
      (polynomial d (fun j => (q j).map φ)).realizeWeights (fun i => (v i).map φ) ↔
      (polynomial d q).realizeWeights w = (polynomial d q).realizeWeights v := by
  have h := polynomialRealization_map_eq_iff hφ ((polynomial d q).polynomialRealizeWeights q)
    ((polynomial d q).weightEquiv.symm w) ((polynomial d q).weightEquiv.symm v)
  rw [map_polynomialRealizeWeights] at h
  have hs := (polynomial d q).polynomialRealization_polynomialRealizeWeights (fun _ _ => rfl)
  have ht := (polynomial d (fun j => (q j).map φ)).polynomialRealization_polynomialRealizeWeights
    (fun _ _ => rfl)
  have hcw := weightEquiv_map φ d q ((polynomial d q).weightEquiv.symm w)
  have hcv := weightEquiv_map φ d q ((polynomial d q).weightEquiv.symm v)
  have hew := (polynomial d q).weightEquiv.apply_symm_apply w
  have hev := (polynomial d q).weightEquiv.apply_symm_apply v
  dsimp +instances only [polynomial, WeightIndex, Weights] at *
  simpa only [hs, ht, Function.comp_apply, hcw, hcv, hew, hev] using h

end Fibres

end TauCeti.Neuromanifold.MLPSpec
