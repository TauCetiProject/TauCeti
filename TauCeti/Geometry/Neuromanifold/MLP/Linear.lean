/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Dense
public import TauCeti.Geometry.Neuromanifold.MLP.Basic

/-!
# Linear networks

An MLP specification with identity activations, `MLPSpec.linear d`, is a finite chain of dense
layers with nothing between them. Its bias-free realizations are linear networks: the weights
`W₁, …, W_L` realize `x ↦ W_L ⋯ W₁ x`. This file records that identification for every depth.

For bias-free parameters `w` of any specification, `MLPSpec.weightProduct A w i` is the product
`Wᵢ ⋯ W₁` of the first `i` weight matrices, with the identity matrix at layer `0`. It depends only
on the widths of `A`. For `MLPSpec.linear d`:

* the bias-free prefix at layer `i` is `x ↦ (Wᵢ ⋯ W₁) x`, so the bias-free realization is
  `Matrix.mulVec` of the full weight product, and the bias-free neuromanifold is the image of
  the weight products under matrix evaluation;
* with biases, every prefix is affine: its linear part is the weight product and its
  translation is the prefix at the zero input;
* in positive depth the output bias is free, so the affine neuromanifold consists of exactly
  the dense layers `x ↦ M x + b` with `M` a weight product and `b` arbitrary.

In depth two the weight product is `W₂ W₁`, so the bias-free neuromanifold is that of the
two-layer linear network obtained by composing two bias-free dense layers in
`TauCeti.Geometry.Neuromanifold.Dense`. The parameter space is always the full product of
the weight spaces: no claim is made that distinct weights realize distinct functions, and no
rank or dimension description of the neuromanifold is asserted.

## References

* Giovanni Luca Marchetti, Vahid Shahverdi, Stefano Mereta, Matthew Trager, and Kathlén Kohn,
  *Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
  [arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3 and Appendix A.
-/

public section

open Matrix

namespace TauCeti.Neuromanifold

namespace MLPSpec

variable {K : Type*} {L : ℕ} [Semiring K]

/-! ### Products of weight matrices -/

/-- The product `Wᵢ ⋯ W₁` of the first `i` weight matrices of bias-free parameters `w`, a
matrix from the input layer to layer `i`. At layer `0` it is the identity matrix. -/
def weightProduct (A : MLPSpec K L) (w : A.Weights) :
    (i : Fin (L + 1)) → Matrix (Fin (A.width i)) (Fin (A.width 0)) K :=
  Fin.induction 1 fun i M => w i * M

/-- The empty product of weight matrices is the identity matrix. -/
@[simp]
theorem weightProduct_zero (A : MLPSpec K L) (w : A.Weights) : A.weightProduct w 0 = 1 :=
  Fin.induction_zero ..

/-- The weight product up to layer `i + 1` multiplies the product up to layer `i` by `Wᵢ₊₁` on
the left. -/
@[simp]
theorem weightProduct_succ (A : MLPSpec K L) (w : A.Weights) (i : Fin L) :
    A.weightProduct w i.succ = w i * A.weightProduct w i.castSucc :=
  Fin.induction_succ ..

/-! ### Identity activations -/

variable (d : Fin (L + 1) → ℕ)

/-- Each bias-free prefix of a linear network evaluates the product of the weight matrices
below it. -/
@[simp]
theorem evalPrefix_zeroBias_linear (w : (linear d : MLPSpec K L).Weights)
    (x : Fin ((linear d : MLPSpec K L).width 0) → K) (i : Fin (L + 1)) :
    (linear d).evalPrefix ((linear d).zeroBias w) x i = (linear d).weightProduct w i *ᵥ x := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    funext j
    simp [ih, mulVec_mulVec]

/-- Each prefix of a linear network with biases is affine: its linear part is the product of
the weight matrices below it, and its translation is the prefix at the zero input. -/
theorem evalPrefix_linear (θ : (linear d : MLPSpec K L).Parameters)
    (x : Fin ((linear d : MLPSpec K L).width 0) → K) (i : Fin (L + 1)) :
    (linear d).evalPrefix θ x i =
      (linear d).weightProduct (fun j => (θ j).1) i *ᵥ x + (linear d).evalPrefix θ 0 i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    funext j
    simp [ih, mulVec_add, mulVec_mulVec, add_assoc]

/-- A linear network realizes evaluation at the product of its weight matrices. -/
@[simp]
theorem realizeWeights_linear (w : (linear d : MLPSpec K L).Weights) :
    (linear d).realizeWeights w = ((linear d).weightProduct w (Fin.last L)).mulVec := by
  funext x
  rw [realizeWeights_def, Function.comp_apply, realize_def]
  exact evalPrefix_zeroBias_linear d w x (Fin.last L)

/-- A linear network with biases realizes an affine map, whose linear part is the product of
its weight matrices and whose translation is its value at the zero input. -/
theorem realize_linear (θ : (linear d : MLPSpec K L).Parameters)
    (x : Fin ((linear d : MLPSpec K L).width 0) → K) :
    (linear d).realize θ x =
      (linear d).weightProduct (fun j => (θ j).1) (Fin.last L) *ᵥ x + (linear d).realize θ 0 := by
  rw [realize_def, realize_def]
  exact evalPrefix_linear d θ x (Fin.last L)

/-- The bias-free neuromanifold of a linear network is the image under matrix evaluation of
the products of its weight matrices. -/
theorem realizedFunctions_realizeWeights_linear :
    realizedFunctions (linear d : MLPSpec K L).realizeWeights =
      Matrix.mulVec '' Set.range fun w => (linear d).weightProduct w (Fin.last L) := by
  rw [realizedFunctions_def, ← Set.range_comp]
  congr 1
  funext w
  exact realizeWeights_linear d w

/-- In positive depth, the neuromanifold of a linear network with biases consists of the
dense layers whose weight matrix is a product of its weight matrices and whose bias is
arbitrary: the output bias moves the translation freely without changing the linear part. -/
theorem realizedFunctions_realize_linear (d : Fin (L + 2) → ℕ) :
    realizedFunctions (linear d : MLPSpec K (L + 1)).realize =
      dense '' ((Set.range fun w => (linear d).weightProduct w (Fin.last (L + 1))) ×ˢ
        Set.univ) := by
  ext f
  rw [realizedFunctions_def]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨((linear d).weightProduct (fun j => (θ j).1) (Fin.last (L + 1)),
      (linear d).realize θ 0), ⟨⟨fun j => (θ j).1, rfl⟩, Set.mem_univ _⟩, ?_⟩
    funext x
    rw [dense_apply, realize_linear d θ x]
  · rintro ⟨⟨_, b⟩, ⟨⟨w, rfl⟩, -⟩, rfl⟩
    -- Keep the weights `w`, and use `b` as the output bias with all other biases zero.
    let θ := Function.update ((linear d).zeroBias w) (Fin.last L) (w (Fin.last L), b)
    have hθ : (fun j => (θ j).1) = w := by
      funext j
      by_cases hj : j = Fin.last L
      · subst hj
        simp [θ]
      · simp [θ, Function.update_of_ne hj]
    have hbelow : (linear d).evalPrefix θ 0 (Fin.last L).castSucc =
        (linear d).evalPrefix ((linear d).zeroBias w) 0 (Fin.last L).castSucc :=
      (linear d).evalPrefix_congr 0 _ fun j hj =>
        Function.update_of_ne (Fin.castSucc_lt_castSucc_iff.mp hj).ne ..
    refine ⟨θ, ?_⟩
    funext x
    rw [realize_linear, hθ, realize_succ, hbelow, evalPrefix_zeroBias_linear]
    simp [θ]

end MLPSpec

end TauCeti.Neuromanifold
