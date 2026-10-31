/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Matrix.Mul

/-!
# Multilayer perceptron specifications

An MLP specification of depth `L` over a scalar type `K` records widths `d₀, …, d_L` and one
scalar activation `σᵢ` for each hidden layer `1 ≤ i ≤ L - 1`. It is one concrete way of
supplying a realization map to the neuromanifold API of
`TauCeti.Geometry.Neuromanifold.Basic`; it is not a universal description of architectures.

For a fixed specification `A`, the affine parameter space `A.Parameters` consists of a weight
matrix `Wᵢ ∈ K^{dᵢ × dᵢ₋₁}` and a bias `bᵢ ∈ K^{dᵢ}` for every layer `1 ≤ i ≤ L`, and the
bias-free parameter space `A.Weights` consists of the weight matrices alone. Layers are indexed
from zero in Lean: the parameters at `i : Fin L` produce layer `i + 1`. The prefix evaluation
`A.evalPrefix θ x` is defined by `h₀ = x` and `hᵢ₊₁ = σᵢ₊₁ (Wᵢ₊₁ hᵢ + bᵢ₊₁)` coordinatewise,
where the output layer has no activation, following Finkel's convention: `σ_L = id`, so the
output layer is affine. The realization `A.realize θ` is the final prefix `h_L`. The bias-free
realization `A.realizeWeights` restricts it along the zero-bias embedding `A.zeroBias`, so its
fibres contain no bias coordinates.

Changing the depth, widths, or activations changes the specification and hence the model; the
parameter space of a fixed specification never grows. The constructors `MLPSpec.linear`,
`MLPSpec.polynomial`, and `MLPSpec.monomial` give identity, layerwise polynomial, and layerwise
monomial hidden activations `t ↦ t ^ rᵢ`. With a constant exponent `r` and depth `L + 1`, the
bias-free monomial realization is the polynomial network
`W_{L+1} ∘ σ_r ∘ W_L ∘ ⋯ ∘ σ_r ∘ W₁` of Finkel–Rodriguez–Wu–Yahl.

## References

* Bella Finkel, Jose Israel Rodriguez, Chenxi Wu, and Thomas Yahl, *Activation degree
  thresholds and expressiveness of polynomial neural networks*,
  [arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1.
* Giovanni Luca Marchetti, Vahid Shahverdi, Stefano Mereta, Matthew Trager, and Kathlén Kohn,
  *Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
  [arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.
-/

public section

open Matrix

namespace TauCeti.Neuromanifold

/-- A multilayer perceptron specification of depth `L`: widths `width i` for the layers
`0 ≤ i ≤ L`, and an activation `activation j` for the hidden layer `j + 1`, for `j < L - 1`.
The output layer carries no activation. -/
@[ext]
structure MLPSpec (K : Type*) (L : ℕ) where
  /-- The width of layer `i`, for `0 ≤ i ≤ L`. -/
  width : Fin (L + 1) → ℕ
  /-- The scalar activation of the hidden layer `j + 1`, for `j < L - 1`. -/
  activation : Fin (L - 1) → K → K

namespace MLPSpec

variable {K : Type*} {L : ℕ}

/-- The bias-free parameter space: a weight matrix `K^{dᵢ₊₁ × dᵢ}` for each `i : Fin L`. -/
abbrev Weights (A : MLPSpec K L) : Type _ :=
  (i : Fin L) → Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K

/-- The affine parameter space: a weight matrix `K^{dᵢ₊₁ × dᵢ}` and a bias `K^{dᵢ₊₁}` for
each `i : Fin L`. -/
abbrev Parameters (A : MLPSpec K L) : Type _ :=
  (i : Fin L) → Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K ×
    (Fin (A.width i.succ) → K)

/-- The embedding of bias-free parameters into affine parameters by zero biases. -/
def zeroBias [Zero K] (A : MLPSpec K L) (w : A.Weights) : A.Parameters :=
  fun i => (w i, 0)

/-- The zero-bias embedding keeps each weight matrix and sets its bias to zero. -/
@[simp]
theorem zeroBias_apply [Zero K] (A : MLPSpec K L) (w : A.Weights) (i : Fin L) :
    A.zeroBias w i = (w i, 0) := (rfl)

/-- Distinct bias-free parameters have distinct zero-bias embeddings. -/
theorem zeroBias_injective [Zero K] (A : MLPSpec K L) : Function.Injective A.zeroBias :=
  fun _ _ h => funext fun i => congrArg Prod.fst (congrFun h i)

/-- The activation applied by the layer with parameters at `i : Fin L`, which produces layer
`i + 1`: the hidden activation when `i + 1 < L`, and the identity on the output layer. -/
def layerActivation (A : MLPSpec K L) (i : Fin L) : K → K :=
  if h : i.val + 1 < L then A.activation ⟨i.val, by omega⟩ else id

/-- A layer below the output applies its hidden activation. -/
theorem layerActivation_of_lt (A : MLPSpec K L) (i : Fin L) (h : i.val + 1 < L) :
    A.layerActivation i = A.activation ⟨i.val, by omega⟩ := by
  simp [layerActivation, h]

/-- The output layer applies the identity activation. -/
theorem layerActivation_of_val_add_one_eq (A : MLPSpec K L) (i : Fin L) (h : i.val + 1 = L) :
    A.layerActivation i = id := by
  simp [layerActivation, h]

/-- In depth `L + 1`, the layer at `i : Fin L` is hidden and applies `activation i`. -/
@[simp]
theorem layerActivation_castSucc (A : MLPSpec K (L + 1)) (i : Fin L) :
    A.layerActivation i.castSucc = A.activation i :=
  A.layerActivation_of_lt _ (by simp)

/-- In depth `L + 1`, the last layer is the output layer and applies the identity. -/
@[simp]
theorem layerActivation_last (A : MLPSpec K (L + 1)) : A.layerActivation (Fin.last L) = id :=
  A.layerActivation_of_val_add_one_eq _ (by simp)

section Evaluation

variable [NonUnitalNonAssocSemiring K]

/-- The prefix evaluation of an MLP: `h₀ = x` and `hᵢ₊₁ = σᵢ₊₁ (Wᵢ₊₁ hᵢ + bᵢ₊₁)`
coordinatewise, where the output layer uses the identity activation. -/
def evalPrefix (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    (i : Fin (L + 1)) → Fin (A.width i) → K :=
  Fin.induction x fun i h j => A.layerActivation i (((θ i).1 *ᵥ h) j + (θ i).2 j)

/-- The zeroth prefix is the input. -/
@[simp]
theorem evalPrefix_zero (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    A.evalPrefix θ x 0 = x :=
  Fin.induction_zero ..

/-- The prefix recursion of an MLP. -/
@[simp]
theorem evalPrefix_succ (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K)
    (i : Fin L) :
    A.evalPrefix θ x i.succ =
      fun j => A.layerActivation i (((θ i).1 *ᵥ A.evalPrefix θ x i.castSucc) j + (θ i).2 j) :=
  Fin.induction_succ ..

/-- The output layer is affine. -/
theorem evalPrefix_succ_of_val_add_one_eq (A : MLPSpec K L) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin L) (h : i.val + 1 = L) :
    A.evalPrefix θ x i.succ = (θ i).1 *ᵥ A.evalPrefix θ x i.castSucc + (θ i).2 := by
  simp [A.layerActivation_of_val_add_one_eq i h, Pi.add_def]

/-- A prefix of an MLP depends only on the parameters of the layers below it. -/
theorem evalPrefix_congr (A : MLPSpec K L) {θ θ' : A.Parameters} (x : Fin (A.width 0) → K)
    (i : Fin (L + 1)) (h : ∀ j : Fin L, j.castSucc < i → θ j = θ' j) :
    A.evalPrefix θ x i = A.evalPrefix θ' x i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [evalPrefix_succ, evalPrefix_succ, h i (Fin.castSucc_lt_succ ..),
      ih fun j hj => h j (hj.trans (Fin.castSucc_lt_succ ..))]

/-- Prefixes from layer `k` on depend only on the prefix at `k` and on the parameters of the
layers above it. -/
theorem evalPrefix_congr_of_le (A : MLPSpec K L) {θ θ' : A.Parameters}
    {x x' : Fin (A.width 0) → K} {k : Fin (L + 1)}
    (hk : A.evalPrefix θ x k = A.evalPrefix θ' x' k)
    (h : ∀ j : Fin L, k ≤ j.castSucc → θ j = θ' j) {i : Fin (L + 1)} (hi : k ≤ i) :
    A.evalPrefix θ x i = A.evalPrefix θ' x' i := by
  induction i using Fin.induction with
  | zero => rwa [Fin.le_zero_iff.mp hi] at hk
  | succ i ih =>
    rcases hi.lt_or_eq with hlt | rfl
    · have hki : k ≤ i.castSucc := Fin.le_castSucc_iff.mpr hlt
      rw [evalPrefix_succ, evalPrefix_succ, h i hki, ih hki]
    · exact hk

/-- The realization map of an MLP specification on affine parameters: the last prefix. -/
def realize (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    Fin (A.width (Fin.last L)) → K :=
  A.evalPrefix θ x (Fin.last L)

/-- The realization is the last prefix evaluation. -/
theorem realize_def (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    A.realize θ x = A.evalPrefix θ x (Fin.last L) := (rfl)

/-- A depth-zero MLP realizes the identity. -/
@[simp]
theorem realize_depth_zero (A : MLPSpec K 0) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    A.realize θ x = x :=
  A.evalPrefix_zero θ x

/-- The realization of an MLP of positive depth applies the affine output layer to the last
hidden prefix. -/
theorem realize_succ (A : MLPSpec K (L + 1)) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    A.realize θ x =
      (θ (Fin.last L)).1 *ᵥ A.evalPrefix θ x (Fin.last L).castSucc + (θ (Fin.last L)).2 :=
  A.evalPrefix_succ_of_val_add_one_eq θ x (Fin.last L) (by simp)

/-- A one-layer MLP realizes a single affine map. -/
@[simp]
theorem realize_depth_one (A : MLPSpec K 1) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    A.realize θ x = (θ 0).1 *ᵥ x + (θ 0).2 := by
  simp [realize_succ]

/-- The realization of an MLP specification on bias-free parameters: the restriction of
`MLPSpec.realize` along the zero-bias embedding. -/
def realizeWeights (A : MLPSpec K L) (w : A.Weights) (x : Fin (A.width 0) → K) :
    Fin (A.width (Fin.last L)) → K :=
  A.realize (A.zeroBias w) x

/-- The bias-free realization is the affine realization composed with the zero-bias
embedding. -/
theorem realizeWeights_def (A : MLPSpec K L) :
    A.realizeWeights = A.realize ∘ A.zeroBias := (rfl)

/-- A depth-zero MLP realizes the identity on bias-free parameters. -/
@[simp]
theorem realizeWeights_depth_zero (A : MLPSpec K 0) (w : A.Weights) (x : Fin (A.width 0) → K) :
    A.realizeWeights w x = x :=
  A.realize_depth_zero _ x

/-- The bias-free realization of an MLP of positive depth applies the linear output layer to
the last hidden prefix. -/
theorem realizeWeights_succ (A : MLPSpec K (L + 1)) (w : A.Weights) (x : Fin (A.width 0) → K) :
    A.realizeWeights w x =
      w (Fin.last L) *ᵥ A.evalPrefix (A.zeroBias w) x (Fin.last L).castSucc := by
  simp [realizeWeights, realize_succ]

/-- A one-layer MLP realizes a single linear map on bias-free parameters. -/
@[simp]
theorem realizeWeights_depth_one (A : MLPSpec K 1) (w : A.Weights) (x : Fin (A.width 0) → K) :
    A.realizeWeights w x = w 0 *ᵥ x := by
  simp [realizeWeights]

end Evaluation

/-! ### Constructors -/

/-- The MLP specification with identity hidden activations. Its bias-free realizations are
linear networks. -/
def linear (d : Fin (L + 1) → ℕ) : MLPSpec K L where
  width := d
  activation _ := id

/-- The identity-activation specification has the given widths. -/
@[simp]
theorem linear_width (d : Fin (L + 1) → ℕ) : (linear d : MLPSpec K L).width = d := (rfl)

/-- Every hidden activation of `MLPSpec.linear` is the identity. -/
@[simp]
theorem linear_activation (d : Fin (L + 1) → ℕ) (j : Fin (L - 1)) :
    (linear d : MLPSpec K L).activation j = id := (rfl)

/-- Every layer of `MLPSpec.linear`, hidden or output, applies the identity. -/
@[simp]
theorem layerActivation_linear (d : Fin (L + 1) → ℕ) (i : Fin L) :
    (linear d : MLPSpec K L).layerActivation i = id := by
  unfold layerActivation
  split <;> rfl

/-- The MLP specification whose hidden layer `j + 1` evaluates the polynomial `p j`. -/
def polynomial [Semiring K] (d : Fin (L + 1) → ℕ) (p : Fin (L - 1) → Polynomial K) :
    MLPSpec K L where
  width := d
  activation j t := (p j).eval t

/-- The polynomial-activation specification has the given widths. -/
@[simp]
theorem polynomial_width [Semiring K] (d : Fin (L + 1) → ℕ) (p : Fin (L - 1) → Polynomial K) :
    (polynomial d p).width = d := (rfl)

/-- The hidden activation `j` of `MLPSpec.polynomial` evaluates `p j`. -/
@[simp]
theorem polynomial_activation [Semiring K] (d : Fin (L + 1) → ℕ) (p : Fin (L - 1) → Polynomial K)
    (j : Fin (L - 1)) (t : K) : (polynomial d p).activation j t = (p j).eval t := (rfl)

/-- The MLP specification whose hidden layer `j + 1` applies the monomial `t ↦ t ^ r j`. -/
def monomial [Monoid K] (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ) : MLPSpec K L where
  width := d
  activation j t := t ^ r j

/-- The monomial-activation specification has the given widths. -/
@[simp]
theorem monomial_width [Monoid K] (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ) :
    (monomial d r : MLPSpec K L).width = d := (rfl)

/-- The hidden activation `j` of `MLPSpec.monomial` is `t ↦ t ^ r j`. -/
@[simp]
theorem monomial_activation [Monoid K] (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ)
    (j : Fin (L - 1)) (t : K) : (monomial d r : MLPSpec K L).activation j t = t ^ r j := (rfl)

/-- Monomial activations are the polynomial activations given by powers of `X`. -/
theorem polynomial_X_pow [Semiring K] (d : Fin (L + 1) → ℕ) (r : Fin (L - 1) → ℕ) :
    polynomial d (fun j => Polynomial.X ^ r j) = (monomial d r : MLPSpec K L) := by
  ext <;> simp [Polynomial.eval_X_pow]

/-- Monomial activations with all exponents one are identity activations. -/
theorem monomial_one [Monoid K] (d : Fin (L + 1) → ℕ) :
    monomial d (fun _ => 1) = (linear d : MLPSpec K L) := by
  ext <;> simp

/-- The bias-free hidden recursion of a monomial MLP: hidden layer `i + 1` raises each
coordinate of `Wᵢ₊₁ hᵢ` to the power `r i`. -/
theorem monomial_evalPrefix_zeroBias_castSucc_succ [Semiring K] (d : Fin (L + 2) → ℕ)
    (r : Fin L → ℕ) (w : (monomial d r : MLPSpec K (L + 1)).Weights)
    (x : Fin ((monomial d r : MLPSpec K (L + 1)).width 0) → K) (i : Fin L) :
    (monomial d r).evalPrefix ((monomial d r).zeroBias w) x i.castSucc.succ =
      fun j => ((w i.castSucc *ᵥ
        (monomial d r).evalPrefix ((monomial d r).zeroBias w) x i.castSucc.castSucc) j) ^ r i := by
  simp

end MLPSpec

end TauCeti.Neuromanifold
