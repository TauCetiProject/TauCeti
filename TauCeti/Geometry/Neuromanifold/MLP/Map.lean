/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Scalar transport of polynomial multilayer perceptrons

Mapping the hidden activation coefficients, weights, biases, and inputs along a ring
homomorphism commutes with evaluation of a polynomial MLP. The output head remains affine.
`polynomialMapParameters` and `polynomialMapWeights` map the actual parameter products;
`realize_polynomial_map` and `realizeWeights_polynomial_map` give the evaluation comparisons.
The bias-free comparison uses the zero-bias embedding, not an enlarged parameter space.

The results apply to homomorphisms of semirings, in particular field embeddings.
The real-to-complex comparison is stated explicitly. It only compares mapped inputs and
parameters: it does not identify real and complex realized images or fibres.

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
variable {L : ℕ} (d : Fin (L + 1) → ℕ) (p : Fin (L - 1) → Polynomial K)

/-- Map every weight entry and bias of a polynomial MLP, with the hidden activation
coefficients mapped along the same homomorphism. -/
def polynomialMapParameters (φ : K →+* K') (θ : (polynomial d p).Parameters) :
    (polynomial d (fun i => (p i).map φ)).Parameters :=
  fun i => ((θ i).1.map φ, φ ∘ (θ i).2)

/-- The parameter transport maps weights and biases coordinatewise. -/
@[simp]
theorem polynomialMapParameters_apply (φ : K →+* K') (θ : (polynomial d p).Parameters)
    (i : Fin L) :
    polynomialMapParameters d p φ θ i = ((θ i).1.map φ, φ ∘ (θ i).2) := (rfl)

/-- Map the weight-only parameter product of a polynomial MLP. -/
def polynomialMapWeights (φ : K →+* K') (w : (polynomial d p).Weights) :
    (polynomial d (fun i => (p i).map φ)).Weights :=
  fun i => (w i).map φ

/-- The weight transport maps each matrix entry. -/
@[simp]
theorem polynomialMapWeights_apply (φ : K →+* K') (w : (polynomial d p).Weights)
    (i : Fin L) : polynomialMapWeights d p φ w i = (w i).map φ := (rfl)

/-- Transport along the identity leaves affine parameters unchanged. -/
@[simp]
theorem polynomialMapParameters_id (θ : (polynomial d p).Parameters) :
    polynomialMapParameters d p (RingHom.id K) θ = θ := (rfl)

/-- Transport along the identity leaves weight-only parameters unchanged. -/
@[simp]
theorem polynomialMapWeights_id (w : (polynomial d p).Weights) :
    polynomialMapWeights d p (RingHom.id K) w = w := (rfl)

/-- Successive scalar transports compose on affine parameters. -/
@[simp]
theorem polynomialMapParameters_comp (φ : K →+* K') (ψ : K' →+* K'')
    (θ : (polynomial d p).Parameters) :
    polynomialMapParameters d (fun i => (p i).map φ) ψ
        (polynomialMapParameters d p φ θ) =
      polynomialMapParameters d p (ψ.comp φ) θ := (rfl)

/-- Successive scalar transports compose on weight-only parameters. -/
@[simp]
theorem polynomialMapWeights_comp (φ : K →+* K') (ψ : K' →+* K'')
    (w : (polynomial d p).Weights) :
    polynomialMapWeights d (fun i => (p i).map φ) ψ
        (polynomialMapWeights d p φ w) =
      polynomialMapWeights d p (ψ.comp φ) w := (rfl)

/-- Mapping a zero-bias embedding gives the zero-bias embedding of the mapped weights. -/
@[simp]
theorem polynomialMapParameters_zeroBias (φ : K →+* K') (w : (polynomial d p).Weights) :
    polynomialMapParameters d p φ ((polynomial d p).zeroBias w) =
      (polynomial d (fun i => (p i).map φ)).zeroBias (polynomialMapWeights d p φ w) := by
  funext i
  simp only [polynomialMapParameters_apply, zeroBias_apply]
  apply Prod.ext
  · rfl
  · funext j
    exact φ.map_zero

/-- Scalar transport by an embedding is injective on affine parameters. -/
theorem polynomialMapParameters_injective {φ : K →+* K'} (hφ : Function.Injective φ) :
    Function.Injective (polynomialMapParameters d p φ) := by
  intro θ θ' h
  funext i
  apply Prod.ext
  · ext j k
    apply hφ
    exact congrFun (congrFun (congrArg Prod.fst (congrFun h i)) j) k
  · ext j
    apply hφ
    exact congrFun (congrArg Prod.snd (congrFun h i)) j

/-- Scalar transport by an embedding is injective on weight-only parameters. -/
theorem polynomialMapWeights_injective {φ : K →+* K'} (hφ : Function.Injective φ) :
    Function.Injective (polynomialMapWeights d p φ) := by
  intro w w' h
  funext i j k
  apply hφ
  exact congrFun (congrFun (congrFun h i) j) k

/-- Mapping activation coefficients commutes with each hidden activation, and also with
the identity activation on the output layer. -/
@[simp]
theorem layerActivation_polynomial_map (φ : K →+* K') (i : Fin L) (t : K) :
    (polynomial d (fun j => (p j).map φ)).layerActivation i (φ t) =
      φ ((polynomial d p).layerActivation i t) := by
  by_cases h : i.val + 1 < L
  · simp only [layerActivation_of_lt _ _ h, polynomial_activation, Polynomial.eval_map_apply]
  · have hi : i.val + 1 = L := by omega
    simp only [layerActivation_of_val_add_one_eq _ _ hi, id_eq]

/-- Every prefix of a transported polynomial MLP is the mapped original prefix. This
includes depth zero and layers of width zero. -/
@[simp]
theorem evalPrefix_polynomial_map (φ : K →+* K') (θ : (polynomial d p).Parameters)
    (x : Fin (d 0) → K) (i : Fin (L + 1)) :
    (polynomial d (fun j => (p j).map φ)).evalPrefix
        (polynomialMapParameters d p φ θ) (φ ∘ x) i =
      φ ∘ (polynomial d p).evalPrefix θ x i := by
  -- The width families coincide, but rewriting below a scalar-composition wrapper cannot
  -- infer that equality at reducible transparency. Use the recursion equations explicitly.
  induction i using Fin.induction with
  | zero =>
    exact (evalPrefix_zero _ _ _).trans
      (congrArg (fun y => φ ∘ y) ((polynomial d p).evalPrefix_zero θ x).symm)
  | succ i ih =>
    refine (evalPrefix_succ _ _ _ i).trans ?_
    refine Eq.trans ?_ (congrArg (fun y => φ ∘ y) (evalPrefix_succ _ θ x i).symm)
    funext j
    dsimp only [polynomialMapParameters, Function.comp_def]
    rw [ih]
    exact (congrArg ((polynomial d (fun j => (p j).map φ)).layerActivation i)
      ((congrArg₂ (· + ·) (φ.map_mulVec (θ i).1 _ j).symm (Eq.refl _)).trans
        (φ.map_add _ _).symm)).trans (layerActivation_polynomial_map d p φ i _)

/-- Polynomial MLP realization commutes with scalar transport of coefficients, affine
parameters, and inputs. -/
@[simp]
theorem realize_polynomial_map (φ : K →+* K') (θ : (polynomial d p).Parameters)
    (x : Fin (d 0) → K) :
    (polynomial d (fun j => (p j).map φ)).realize
        (polynomialMapParameters d p φ θ) (φ ∘ x) =
      φ ∘ (polynomial d p).realize θ x := by
  exact (realize_def _ _ _).trans ((evalPrefix_polynomial_map d p φ θ x _).trans
    (congrArg (fun y => φ ∘ y) (realize_def _ _ _).symm))

/-- The weight-only realization has the same scalar transport law, with no bias parameters
introduced. -/
@[simp]
theorem realizeWeights_polynomial_map (φ : K →+* K') (w : (polynomial d p).Weights)
    (x : Fin (d 0) → K) :
    (polynomial d (fun j => (p j).map φ)).realizeWeights
        (polynomialMapWeights d p φ w) (φ ∘ x) =
      φ ∘ (polynomial d p).realizeWeights w x := by
  funext j
  simp only [Function.comp_apply, realizeWeights_def,
    ← polynomialMapParameters_zeroBias, realize_polynomial_map]

/-- A real polynomial MLP evaluated at real parameters and inputs has the same outputs
as its complexification, viewed in `ℂ`. -/
theorem realize_polynomial_map_ofReal (d : Fin (L + 1) → ℕ)
    (p : Fin (L - 1) → Polynomial ℝ) (θ : (polynomial d p).Parameters)
    (x : Fin (d 0) → ℝ) :
    (polynomial d (fun j => (p j).map Complex.ofRealHom)).realize
        (polynomialMapParameters d p Complex.ofRealHom θ) (Complex.ofReal ∘ x) =
      Complex.ofReal ∘ (polynomial d p).realize θ x :=
  realize_polynomial_map d p Complex.ofRealHom θ x

/-- Complexification also commutes with the weight-only realization of a real polynomial
MLP. -/
theorem realizeWeights_polynomial_map_ofReal (d : Fin (L + 1) → ℕ)
    (p : Fin (L - 1) → Polynomial ℝ) (w : (polynomial d p).Weights)
    (x : Fin (d 0) → ℝ) :
    (polynomial d (fun j => (p j).map Complex.ofRealHom)).realizeWeights
        (polynomialMapWeights d p Complex.ofRealHom w) (Complex.ofReal ∘ x) =
      Complex.ofReal ∘ (polynomial d p).realizeWeights w x :=
  realizeWeights_polynomial_map d p Complex.ofRealHom w x

end TauCeti.Neuromanifold.MLPSpec
