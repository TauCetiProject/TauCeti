/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Scalar transport of multilayer perceptrons

`mapParameters` and `mapWeights` map the actual parameter products of an MLP to a
specification with the same widths and chosen target activations. If these activations
commute with the scalar homomorphism, `realize_map` and `realizeWeights_map` compare
evaluation. The output head remains affine. The bias-free comparison uses the zero-bias
embedding, not an enlarged parameter space.

For polynomial MLPs, mapping the hidden activation coefficients gives the required
compatibility. The results apply to homomorphisms of semirings, in particular field
embeddings. The real-to-complex comparison is stated explicitly. It only compares mapped
inputs and parameters: it does not identify real and complex realized images or fibres.

The polynomial architecture convention follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1, with the affine output head of
Finkel–Rodriguez–Wu–Yahl, *Activation degree thresholds and expressiveness of polynomial
neural networks*, [arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1.
-/

public section

namespace TauCeti.Neuromanifold.MLPSpec

open Matrix

variable {K K' K'' : Type*} [Semiring K] [Semiring K'] [Semiring K'']
variable {L : ℕ} (A : MLPSpec K L) (σ' : Fin (L - 1) → K' → K')

/-- Map every weight entry and bias to a specification with the same widths and the
chosen target hidden activations. -/
def mapParameters (φ : K →+* K') (θ : A.Parameters) :
    (⟨A.width, σ'⟩ : MLPSpec K' L).Parameters :=
  fun i => ((θ i).1.map φ, φ ∘ (θ i).2)

/-- The parameter transport maps weights and biases coordinatewise. -/
@[simp]
theorem mapParameters_apply (φ : K →+* K') (θ : A.Parameters) (i : Fin L) :
    mapParameters A σ' φ θ i = ((θ i).1.map φ, φ ∘ (θ i).2) := (rfl)

/-- Map the weight-only parameter product to a specification with the same widths and
the chosen target hidden activations. -/
def mapWeights (φ : K →+* K') (w : A.Weights) :
    (⟨A.width, σ'⟩ : MLPSpec K' L).Weights :=
  fun i => (w i).map φ

/-- The weight transport maps each matrix entry. -/
@[simp]
theorem mapWeights_apply (φ : K →+* K') (w : A.Weights) (i : Fin L) :
    mapWeights A σ' φ w i = (w i).map φ := (rfl)

/-- Transport along the identity leaves affine parameters unchanged. -/
@[simp]
theorem mapParameters_id (θ : A.Parameters) :
    mapParameters A A.activation (RingHom.id K) θ = θ := (rfl)

/-- Transport along the identity leaves weight-only parameters unchanged. -/
@[simp]
theorem mapWeights_id (w : A.Weights) :
    mapWeights A A.activation (RingHom.id K) w = w := (rfl)

/-- Successive scalar transports compose on affine parameters. -/
@[simp]
theorem mapParameters_comp (σ'' : Fin (L - 1) → K'' → K'')
    (φ : K →+* K') (ψ : K' →+* K'') (θ : A.Parameters) :
    mapParameters ⟨A.width, σ'⟩ σ'' ψ (mapParameters A σ' φ θ) =
      mapParameters A σ'' (ψ.comp φ) θ := (rfl)

/-- Successive scalar transports compose on weight-only parameters. -/
@[simp]
theorem mapWeights_comp (σ'' : Fin (L - 1) → K'' → K'')
    (φ : K →+* K') (ψ : K' →+* K'') (w : A.Weights) :
    mapWeights ⟨A.width, σ'⟩ σ'' ψ (mapWeights A σ' φ w) =
      mapWeights A σ'' (ψ.comp φ) w := (rfl)

/-- Mapping a zero-bias embedding gives the zero-bias embedding of the mapped weights. -/
@[simp]
theorem mapParameters_zeroBias (φ : K →+* K') (w : A.Weights) :
    mapParameters A σ' φ (A.zeroBias w) =
      (⟨A.width, σ'⟩ : MLPSpec K' L).zeroBias (mapWeights A σ' φ w) := by
  funext i
  simp only [mapParameters_apply, zeroBias_apply]
  apply Prod.ext
  · rfl
  · funext j
    exact φ.map_zero

/-- Scalar transport by an embedding is injective on affine parameters. -/
theorem mapParameters_injective {φ : K →+* K'} (hφ : Function.Injective φ) :
    Function.Injective (mapParameters A σ' φ) :=
  Function.Injective.piMap fun _ => (Matrix.map_injective hφ).prodMap hφ.comp_left

/-- Scalar transport by an embedding is injective on weight-only parameters. -/
theorem mapWeights_injective {φ : K →+* K'} (hφ : Function.Injective φ) :
    Function.Injective (mapWeights A σ' φ) :=
  Function.Injective.piMap fun _ => Matrix.map_injective hφ

/-- Compatibility of hidden activations with scalar transport also gives compatibility
on every layer, including the identity activation on the output layer. -/
@[simp]
theorem layerActivation_map (φ : K →+* K')
    (h : ∀ j t, σ' j (φ t) = φ (A.activation j t)) (i : Fin L) (t : K) :
    (⟨A.width, σ'⟩ : MLPSpec K' L).layerActivation i (φ t) =
      φ (A.layerActivation i t) := by
  by_cases hi : i.val + 1 < L
  · simpa only [layerActivation_of_lt _ _ hi] using h ⟨i.val, by omega⟩ t
  · have hi' : i.val + 1 = L := by omega
    simp only [layerActivation_of_val_add_one_eq _ _ hi', id_eq]

/-- Every prefix of an MLP with compatible target activations is the mapped original
prefix. This includes depth zero and layers of width zero. -/
@[simp]
theorem evalPrefix_map (φ : K →+* K')
    (h : ∀ j t, σ' j (φ t) = φ (A.activation j t)) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    (⟨A.width, σ'⟩ : MLPSpec K' L).evalPrefix (mapParameters A σ' φ θ) (φ ∘ x) i =
      φ ∘ A.evalPrefix θ x i := by
  induction i using Fin.induction with
  | zero => simp only [evalPrefix_zero]
  | succ i ih =>
    simp only [evalPrefix_succ, mapParameters_apply, Function.comp_apply]
    funext j
    rw [ih, ← φ.map_mulVec, ← map_add, layerActivation_map A σ' φ h]
    rfl

/-- MLP realization commutes with scalar transport when the hidden activations commute
with the scalar homomorphism. -/
@[simp]
theorem realize_map (φ : K →+* K')
    (h : ∀ j t, σ' j (φ t) = φ (A.activation j t)) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) :
    (⟨A.width, σ'⟩ : MLPSpec K' L).realize (mapParameters A σ' φ θ) (φ ∘ x) =
      φ ∘ A.realize θ x := by
  simpa only [realize_def] using evalPrefix_map A σ' φ h θ x (Fin.last L)

/-- The weight-only realization has the same scalar transport law, with no bias
parameters introduced. -/
@[simp]
theorem realizeWeights_map (φ : K →+* K')
    (h : ∀ j t, σ' j (φ t) = φ (A.activation j t)) (w : A.Weights)
    (x : Fin (A.width 0) → K) :
    (⟨A.width, σ'⟩ : MLPSpec K' L).realizeWeights (mapWeights A σ' φ w) (φ ∘ x) =
      φ ∘ A.realizeWeights w x := by
  simpa only [realizeWeights_def, Function.comp_apply, mapParameters_zeroBias] using
    realize_map A σ' φ h (A.zeroBias w) x

variable (d : Fin (L + 1) → ℕ) (p : Fin (L - 1) → Polynomial K)

/-- Mapping activation coefficients commutes with each hidden activation, and also with
the identity activation on the output layer. -/
@[simp]
theorem layerActivation_polynomial_map (φ : K →+* K') (i : Fin L) (t : K) :
    (polynomial d (fun j => (p j).map φ)).layerActivation i (φ t) =
      φ ((polynomial d p).layerActivation i t) :=
  layerActivation_map (polynomial d p) _ φ (fun _ t => Polynomial.eval_map_apply φ t) i t

/-- Every prefix of a transported polynomial MLP is the mapped original prefix. -/
@[simp]
theorem evalPrefix_polynomial_map (φ : K →+* K') (θ : (polynomial d p).Parameters)
    (x : Fin (d 0) → K) (i : Fin (L + 1)) :
    (polynomial d (fun j => (p j).map φ)).evalPrefix
        (mapParameters (polynomial d p) (polynomial d (fun j => (p j).map φ)).activation φ θ)
        (φ ∘ x) i =
      φ ∘ (polynomial d p).evalPrefix θ x i :=
  evalPrefix_map (polynomial d p) _ φ (fun _ t => Polynomial.eval_map_apply φ t) θ x i

/-- Polynomial MLP realization commutes with scalar transport of coefficients, affine
parameters, and inputs. -/
@[simp]
theorem realize_polynomial_map (φ : K →+* K') (θ : (polynomial d p).Parameters)
    (x : Fin (d 0) → K) :
    (polynomial d (fun j => (p j).map φ)).realize
        (mapParameters (polynomial d p) (polynomial d (fun j => (p j).map φ)).activation φ θ)
        (φ ∘ x) =
      φ ∘ (polynomial d p).realize θ x :=
  realize_map (polynomial d p) _ φ (fun _ t => Polynomial.eval_map_apply φ t) θ x

/-- The weight-only polynomial realization commutes with scalar transport, with no bias
parameters introduced. -/
@[simp]
theorem realizeWeights_polynomial_map (φ : K →+* K') (w : (polynomial d p).Weights)
    (x : Fin (d 0) → K) :
    (polynomial d (fun j => (p j).map φ)).realizeWeights
        (mapWeights (polynomial d p) (polynomial d (fun j => (p j).map φ)).activation φ w)
        (φ ∘ x) =
      φ ∘ (polynomial d p).realizeWeights w x :=
  realizeWeights_map (polynomial d p) _ φ (fun _ t => Polynomial.eval_map_apply φ t) w x

/-- A real polynomial MLP evaluated at real parameters and inputs has the same outputs
as its complexification, viewed in `ℂ`. -/
theorem realize_polynomial_map_ofReal (d : Fin (L + 1) → ℕ)
    (p : Fin (L - 1) → Polynomial ℝ) (θ : (polynomial d p).Parameters)
    (x : Fin (d 0) → ℝ) :
    (polynomial d (fun j => (p j).map Complex.ofRealHom)).realize
        (mapParameters (polynomial d p)
          (polynomial d (fun j => (p j).map Complex.ofRealHom)).activation Complex.ofRealHom θ)
        (Complex.ofReal ∘ x) =
      Complex.ofReal ∘ (polynomial d p).realize θ x :=
  realize_polynomial_map d p Complex.ofRealHom θ x

/-- Complexification also commutes with the weight-only realization of a real polynomial
MLP. -/
theorem realizeWeights_polynomial_map_ofReal (d : Fin (L + 1) → ℕ)
    (p : Fin (L - 1) → Polynomial ℝ) (w : (polynomial d p).Weights)
    (x : Fin (d 0) → ℝ) :
    (polynomial d (fun j => (p j).map Complex.ofRealHom)).realizeWeights
        (mapWeights (polynomial d p)
          (polynomial d (fun j => (p j).map Complex.ofRealHom)).activation Complex.ofRealHom w)
        (Complex.ofReal ∘ x) =
      Complex.ofReal ∘ (polynomial d p).realizeWeights w x :=
  realizeWeights_polynomial_map d p Complex.ofRealHom w x

end TauCeti.Neuromanifold.MLPSpec
