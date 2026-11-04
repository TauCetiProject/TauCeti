/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Batteries.Data.Fin.Fold
public import TauCeti.Geometry.Neuromanifold.Activation
public import TauCeti.Geometry.Neuromanifold.Dense
public import TauCeti.Geometry.Neuromanifold.MLP.Basic

/-!
# MLPs as iterated layer compositions

The prefix evaluation and realization maps of an `MLPSpec` are finite dependent folds (`Fin.dfoldl`)
of the single-layer realization maps `dense`, `Matrix.mulVec`, `Neuromanifold.activation`, and
`powerActivation`:

* at each step `i : Fin L`, the affine prefix applies
  `Neuromanifold.activation (A.layerActivation i) () ∘ dense (θ i)` and the bias-free prefix
  applies `Neuromanifold.activation (A.layerActivation i) () ∘ (w i).mulVec`;
* `A.realize θ` and `A.realizeWeights w` agree with `Fin.dfoldl L` over all `L` layers
  (`realize_eq_dfoldl`, `realizeWeights_eq_dfoldl`);
* in positive depth `L + 1`, the `L` hidden layers fold
  `Neuromanifold.activation (A.activation i) ()` with `dense` or `Matrix.mulVec`, and the output
  layer applies `dense (θ (Fin.last L))` or `(w (Fin.last L)).mulVec` with no activation
  (`realize_succ_eq_dense_comp_dfoldl`, `realizeWeights_succ_eq_mulVec_comp_dfoldl`);
* when all hidden activations are `id`, `A.realize θ` folds `dense` and `A.realizeWeights w` folds
  `Matrix.mulVec` directly (`realize_eq_dfoldl_of_activation_eq_id`,
  `realizeWeights_eq_dfoldl_of_activation_eq_id`).

For the monomial specification `MLPSpec.monomial d r` of positive depth `L + 1`, each hidden layer
uses `powerActivation (r i) ()`, giving `(w (Fin.last L)).mulVec ∘ Fin.dfoldl L … (fun i =>
powerActivation (r i) () ∘ (w i.castSucc).mulVec)`
(`realizeWeights_monomial_eq_mulVec_comp_dfoldl`). Taking a constant hidden exponent `fun _ => r`
recovers the bias-free polynomial network `W_{L+1} ∘ σ_r ∘ ⋯ ∘ σ_r ∘ W₁` of
Finkel–Rodriguez–Wu–Yahl, Definition 1.

Splitting off layer `0` of `A : MLPSpec K (L + 1)` via `A.tail : MLPSpec K L` (from
`TauCeti.Geometry.Neuromanifold.MLP.Basic`) expresses positive-depth realization along
`Fin.consEquiv` as `Neuromanifold.compose`. Unlike `MLPSpec.lowerLayers` and
`MLPSpec.upperLayers` in `TauCeti.Geometry.Neuromanifold.MLP.Append`, which split at an interior
hidden layer and require depth at least `2`, `MLPSpec.tail` applies at every positive depth,
including depth `1` where `A.tail` has depth `0`. Together with the depth-zero and depth-one
neuromanifolds, `MLPSpec.tail` gives a layer-by-layer recursion for `realizedFunctions A.realize`
and `realizedFunctions A.realizeWeights`.

## References

* Giovanni Luca Marchetti, Vahid Shahverdi, Stefano Mereta, Matthew Trager, and Kathlén Kohn,
  *Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
  [arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
* Bella Finkel, Jose Israel Rodriguez, Chenxi Wu, and Thomas Yahl, *Activation degree
  thresholds and expressiveness of polynomial neural networks*,
  [arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1.
-/

public section

open Matrix

namespace TauCeti.Neuromanifold

namespace MLPSpec

variable {K : Type*} {L : ℕ}

/-! ### Single-layer steps via concrete layer constructors -/

section LayerStep

variable [NonUnitalNonAssocSemiring K]

/-- Each prefix step applies the dense affine layer followed by the coordinatewise layer
activation. -/
theorem evalPrefix_succ_eq_activation_dense (A : MLPSpec K L) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix θ x i.succ =
      Neuromanifold.activation (A.layerActivation i) ()
        (dense (θ i) (A.evalPrefix θ x i.castSucc)) := by
  funext j
  simp

/-- Each bias-free prefix step applies the linear layer `Matrix.mulVec` followed by the
coordinatewise layer activation. -/
theorem evalPrefix_zeroBias_succ_eq_activation_mulVec (A : MLPSpec K L) (w : A.Weights)
    (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix (A.zeroBias w) x i.succ =
      Neuromanifold.activation (A.layerActivation i) ()
        ((w i).mulVec (A.evalPrefix (A.zeroBias w) x i.castSucc)) := by
  rw [evalPrefix_succ_eq_activation_dense, zeroBias_apply, dense_mk_zero]

/-- In positive depth, hidden layer `i + 1` applies `dense` followed by the coordinatewise hidden
activation `A.activation i`. -/
theorem evalPrefix_castSucc_succ_eq_activation_dense (A : MLPSpec K (L + 1)) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix θ x i.castSucc.succ =
      Neuromanifold.activation (A.activation i) ()
        (dense (θ i.castSucc) (A.evalPrefix θ x i.castSucc.castSucc)) := by
  rw [evalPrefix_succ_eq_activation_dense, layerActivation_castSucc]

/-- In positive depth, bias-free hidden layer `i + 1` applies `Matrix.mulVec` followed by the
coordinatewise hidden activation `A.activation i`. -/
theorem evalPrefix_zeroBias_castSucc_succ_eq_activation_mulVec (A : MLPSpec K (L + 1))
    (w : A.Weights) (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix (A.zeroBias w) x i.castSucc.succ =
      Neuromanifold.activation (A.activation i) ()
        ((w i.castSucc).mulVec (A.evalPrefix (A.zeroBias w) x i.castSucc.castSucc)) := by
  rw [evalPrefix_zeroBias_succ_eq_activation_mulVec, layerActivation_castSucc]

/-- A one-layer MLP realizes the dense affine layer `dense (θ 0)`. -/
theorem realize_depth_one_eq_dense (A : MLPSpec K 1) (θ : A.Parameters) :
    A.realize θ = dense (θ 0) := by
  funext x
  rw [realize_depth_one, dense_apply]

end LayerStep

/-! ### Factoring the first layer via `MLPSpec.tail` -/

section TailEvaluation

variable [NonUnitalNonAssocSemiring K]

/-- From layer `1` onward, the prefixes of `A` are the prefixes of `A.tail` evaluated at the output
of layer `0`. -/
theorem evalPrefix_succ_eq_tail (A : MLPSpec K (L + 1)) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix θ x i.succ =
      A.tail.evalPrefix (Fin.tail θ)
        (Neuromanifold.activation (A.layerActivation 0) () (dense (θ 0) x)) i := by
  induction i using Fin.induction with
  | zero =>
    rw [evalPrefix_succ_eq_activation_dense]
    simp only [Fin.castSucc_zero, evalPrefix_zero]
    exact (A.tail.evalPrefix_zero (Fin.tail θ) _).symm
  | succ i ih =>
    -- `i.succ.castSucc` and `i.castSucc.succ` both have `.val = i.val + 1`, so `ih` applies at the
    -- recursive call of `A.evalPrefix`.
    have ih' : A.evalPrefix θ x i.succ.castSucc = _ := ih
    have h := A.evalPrefix_succ_eq_activation_dense θ x i.succ
    rw [← A.layerActivation_tail i, ih'] at h
    exact h.trans (A.tail.evalPrefix_succ_eq_activation_dense (Fin.tail θ) _ i).symm

/-- From layer `1` onward, the bias-free prefixes of `A` are the bias-free prefixes of `A.tail`
evaluated at `(w 0).mulVec x` after layer `0`'s activation. -/
theorem evalPrefix_zeroBias_succ_eq_tail (A : MLPSpec K (L + 1)) (w : A.Weights)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix (A.zeroBias w) x i.succ =
      A.tail.evalPrefix (A.tail.zeroBias (Fin.tail w))
        (Neuromanifold.activation (A.layerActivation 0) () ((w 0).mulVec x)) i := by
  have hd : dense (A.zeroBias w 0) = (w 0).mulVec := by rw [zeroBias_apply, dense_mk_zero]
  rw [evalPrefix_succ_eq_tail, tail_zeroBias]
  exact congrArg (fun v => A.tail.evalPrefix _ (Neuromanifold.activation _ () v) i)
    (congrFun hd x)

/-- The realization of `A` factors through its first dense layer, layer `0`'s activation, and the
realization of `A.tail`. -/
theorem realize_eq_tail_comp (A : MLPSpec K (L + 1)) (θ : A.Parameters) :
    A.realize θ =
      A.tail.realize (Fin.tail θ) ∘
        Neuromanifold.activation (A.layerActivation 0) () ∘ dense (θ 0) := by
  funext x
  -- `Fin.last (L + 1)` is definitionally `(Fin.last L).succ`.
  exact ((A.realize_def θ x).trans (A.evalPrefix_succ_eq_tail θ x (Fin.last L))).trans
    (A.tail.realize_def (Fin.tail θ) _).symm

/-- On affine parameters assembled by `Fin.cons`, `A` realizes the composite of `dense θ₀`,
layer `0`'s activation, and `A.tail.realize θ`. -/
theorem realize_cons (A : MLPSpec K (L + 1))
    (θ₀ : Matrix (Fin (A.width 1)) (Fin (A.width 0)) K × (Fin (A.width 1) → K))
    (θ : A.tail.Parameters) :
    A.realize (Fin.cons θ₀ θ) =
      A.tail.realize θ ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ dense θ₀ := by
  rw [realize_eq_tail_comp, Fin.tail_def]
  rfl

/-- Under `Fin.consEquiv`, `A.realize` is `Neuromanifold.compose` of layer `0` (including its
activation) and `A.tail.realize`. -/
theorem realize_comp_consEquiv (A : MLPSpec K (L + 1)) :
    A.realize ∘ Fin.consEquiv _ =
      compose (fun θ₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ dense θ₀)
        A.tail.realize := by
  funext p
  simp only [Function.comp_apply, Fin.consEquiv_apply]
  exact (A.realize_cons p.1 p.2).trans
    (compose_apply (fun θ₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ dense θ₀)
      A.tail.realize p).symm

/-- The bias-free realization of `A` factors through `(w 0).mulVec`, layer `0`'s activation, and
the bias-free realization of `A.tail`. -/
theorem realizeWeights_eq_tail_comp (A : MLPSpec K (L + 1)) (w : A.Weights) :
    A.realizeWeights w =
      A.tail.realizeWeights (Fin.tail w) ∘
        Neuromanifold.activation (A.layerActivation 0) () ∘ (w 0).mulVec := by
  funext x
  simp only [realizeWeights_def]
  dsimp only [Function.comp_def]
  simp only [realize_def]
  exact A.evalPrefix_zeroBias_succ_eq_tail w x (Fin.last L)

/-- On bias-free parameters assembled by `Fin.cons`, `A` realizes the composite of `w₀.mulVec`,
layer `0`'s activation, and `A.tail.realizeWeights w`. -/
theorem realizeWeights_cons (A : MLPSpec K (L + 1))
    (w₀ : Matrix (Fin (A.width 1)) (Fin (A.width 0)) K) (w : A.tail.Weights) :
    A.realizeWeights (Fin.cons w₀ w) =
      A.tail.realizeWeights w ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ w₀.mulVec := by
  rw [realizeWeights_eq_tail_comp, Fin.tail_def]
  rfl

/-- Under `Fin.consEquiv`, `A.realizeWeights` is `Neuromanifold.compose` of bias-free layer `0`
(including its activation) and `A.tail.realizeWeights`. -/
theorem realizeWeights_comp_consEquiv (A : MLPSpec K (L + 1)) :
    A.realizeWeights ∘ Fin.consEquiv _ =
      compose (fun w₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ w₀.mulVec)
        A.tail.realizeWeights := by
  funext p
  simp only [Function.comp_apply, Fin.consEquiv_apply]
  exact (A.realizeWeights_cons p.1 p.2).trans
    (compose_apply (fun w₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ w₀.mulVec)
      A.tail.realizeWeights p).symm

end TailEvaluation

/-! ### Iterated composition via `Fin.dfoldl` -/

section IteratedComposition

variable [NonUnitalNonAssocSemiring K]

/-- Every prefix `A.evalPrefix θ x i` is the `i.val`-step dependent left fold `Fin.dfoldl` of the
layer maps `Neuromanifold.activation (A.layerActivation k) () ∘ dense (θ k)`. -/
theorem evalPrefix_eq_dfoldl (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K)
    (i : Fin (L + 1)) :
    A.evalPrefix θ x i =
      Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K)
        (fun k =>
          Neuromanifold.activation
              (A.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) () ∘
            dense (θ (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))
        x := by
  induction i using Fin.induction with
  | zero =>
    exact (A.evalPrefix_zero θ x).trans (Fin.dfoldl_zero
      (α := fun k => Fin (A.width (Fin.castLE (0 : Fin (L + 1)).isLt k)) → K) _ x).symm
  | succ i ih =>
    rw [evalPrefix_succ_eq_activation_dense, ih]
    -- At `i.succ`, `(Fin.dfoldl_succ_last ...).symm` peels off the final step `Fin.last i.val`,
    -- whose `Fin.castLE` image has `.val = i.val` and is definitionally `i`; on the remaining
    -- steps `k.castSucc`, `Fin.castLE` agrees definitionally with the `i.castSucc` fold in `ih`.
    exact (Fin.dfoldl_succ_last
      (α := fun k => Fin (A.width (Fin.castLE i.succ.isLt k)) → K)
      (fun k =>
        Neuromanifold.activation
            (A.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt) k)) () ∘
          dense (θ (Fin.castLE (Nat.le_of_lt_succ i.succ.isLt) k))) x).symm

/-- Every bias-free prefix `A.evalPrefix (A.zeroBias w) x i` is the `i.val`-step dependent left
fold `Fin.dfoldl` of the layer maps
`Neuromanifold.activation (A.layerActivation k) () ∘ (w k).mulVec`. -/
theorem evalPrefix_zeroBias_eq_dfoldl (A : MLPSpec K L) (w : A.Weights) (x : Fin (A.width 0) → K)
    (i : Fin (L + 1)) :
    A.evalPrefix (A.zeroBias w) x i =
      Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K)
        (fun k =>
          Neuromanifold.activation
              (A.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) () ∘
            (w (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)).mulVec)
        x := by
  have h := A.evalPrefix_eq_dfoldl (A.zeroBias w) x i
  simp_rw [zeroBias_apply, dense_mk_zero] at h
  exact h

/-- The affine realization of an MLP specification is the `L`-step dependent fold `Fin.dfoldl` of
`Neuromanifold.activation (A.layerActivation i) () ∘ dense (θ i)`. -/
theorem realize_eq_dfoldl (A : MLPSpec K L) (θ : A.Parameters) :
    A.realize θ =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => Neuromanifold.activation (A.layerActivation i) () ∘ dense (θ i)) := by
  funext x
  exact (A.realize_def θ x).trans (A.evalPrefix_eq_dfoldl θ x (Fin.last L))

/-- The bias-free realization of an MLP specification is the `L`-step dependent fold `Fin.dfoldl`
of `Neuromanifold.activation (A.layerActivation i) () ∘ (w i).mulVec`. -/
theorem realizeWeights_eq_dfoldl (A : MLPSpec K L) (w : A.Weights) :
    A.realizeWeights w =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => Neuromanifold.activation (A.layerActivation i) () ∘ (w i).mulVec) := by
  rw [realizeWeights_def, Function.comp_apply, realize_eq_dfoldl]
  simp_rw [zeroBias_apply, dense_mk_zero]

/-- In positive depth `L + 1`, the last hidden prefix folds the `L` hidden layers
`Neuromanifold.activation (A.activation i) () ∘ dense (θ i.castSucc)`. -/
theorem evalPrefix_last_castSucc_eq_dfoldl (A : MLPSpec K (L + 1)) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) :
    A.evalPrefix θ x (Fin.last L).castSucc =
      Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
        (fun i => Neuromanifold.activation (A.activation i) () ∘ dense (θ i.castSucc)) x := by
  -- At `i = (Fin.last L).castSucc`, `Fin.castLE` on both the width indices and the layer indices
  -- has `.val = k.val`, agreeing definitionally with `Fin.castSucc`.
  have h : A.evalPrefix θ x (Fin.last L).castSucc =
      Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
        (fun i =>
          Neuromanifold.activation (A.layerActivation i.castSucc) () ∘ dense (θ i.castSucc)) x :=
    A.evalPrefix_eq_dfoldl θ x (Fin.last L).castSucc
  simpa only [layerActivation_castSucc] using h

/-- In positive depth `L + 1`, the last bias-free hidden prefix folds the `L` hidden layers
`Neuromanifold.activation (A.activation i) () ∘ (w i.castSucc).mulVec`. -/
theorem evalPrefix_zeroBias_last_castSucc_eq_dfoldl (A : MLPSpec K (L + 1)) (w : A.Weights)
    (x : Fin (A.width 0) → K) :
    A.evalPrefix (A.zeroBias w) x (Fin.last L).castSucc =
      Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
        (fun i => Neuromanifold.activation (A.activation i) () ∘ (w i.castSucc).mulVec) x := by
  have h := A.evalPrefix_last_castSucc_eq_dfoldl (A.zeroBias w) x
  simp_rw [zeroBias_apply, dense_mk_zero] at h
  exact h

/-- In positive depth `L + 1`, the affine realization composes the output layer
`dense (θ (Fin.last L))` with the `L`-step hidden fold. -/
theorem realize_succ_eq_dense_comp_dfoldl (A : MLPSpec K (L + 1)) (θ : A.Parameters) :
    A.realize θ =
      dense (θ (Fin.last L)) ∘
        Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
          (fun i => Neuromanifold.activation (A.activation i) () ∘ dense (θ i.castSucc)) := by
  funext x
  dsimp only [Function.comp_def]
  rw [realize_succ, dense_apply, evalPrefix_last_castSucc_eq_dfoldl]
  rfl

/-- In positive depth `L + 1`, the bias-free realization composes the linear output head
`(w (Fin.last L)).mulVec` with the `L`-step hidden fold. -/
theorem realizeWeights_succ_eq_mulVec_comp_dfoldl (A : MLPSpec K (L + 1)) (w : A.Weights) :
    A.realizeWeights w =
      (w (Fin.last L)).mulVec ∘
        Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
          (fun i => Neuromanifold.activation (A.activation i) () ∘ (w i.castSucc).mulVec) := by
  have h := A.realize_succ_eq_dense_comp_dfoldl (A.zeroBias w)
  simp_rw [zeroBias_apply, dense_mk_zero] at h
  exact (congrFun A.realizeWeights_def w).trans h

/-- When every hidden activation of `A` is `id`, its affine realization folds `dense` directly
across all `L` layers. -/
theorem realize_eq_dfoldl_of_activation_eq_id (A : MLPSpec K L)
    (h : ∀ j, A.activation j = id) (θ : A.Parameters) :
    A.realize θ =
      Fin.dfoldl L (fun i => Fin (A.width i) → K) (fun i => dense (θ i)) := by
  rw [realize_eq_dfoldl]
  simp_rw [A.layerActivation_eq_id_of_activation_eq_id h, activation_id, Function.id_comp]

/-- When every hidden activation of `A` is `id`, its bias-free realization folds `Matrix.mulVec`
directly across all `L` layers. -/
theorem realizeWeights_eq_dfoldl_of_activation_eq_id (A : MLPSpec K L)
    (h : ∀ j, A.activation j = id) (w : A.Weights) :
    A.realizeWeights w =
      Fin.dfoldl L (fun i => Fin (A.width i) → K) (fun i => (w i).mulVec) := by
  rw [realizeWeights_eq_dfoldl]
  simp_rw [A.layerActivation_eq_id_of_activation_eq_id h, activation_id, Function.id_comp]

/-- An identity-activation MLP with biases is the `L`-step fold of its dense affine layers. -/
theorem realize_linear_eq_dfoldl (d : Fin (L + 1) → ℕ) (θ : (linear d : MLPSpec K L).Parameters) :
    (linear d).realize θ =
      Fin.dfoldl L (fun i => Fin ((linear d : MLPSpec K L).width i) → K)
        (fun i => dense (θ i)) :=
  (linear d).realize_eq_dfoldl_of_activation_eq_id (linear_activation d) θ

/-- A bias-free identity-activation MLP is the `L`-step fold of its linear layers
`Matrix.mulVec`. -/
theorem realizeWeights_linear_eq_dfoldl (d : Fin (L + 1) → ℕ)
    (w : (linear d : MLPSpec K L).Weights) :
    (linear d).realizeWeights w =
      Fin.dfoldl L (fun i => Fin ((linear d : MLPSpec K L).width i) → K)
        (fun i => (w i).mulVec) :=
  (linear d).realizeWeights_eq_dfoldl_of_activation_eq_id (linear_activation d) w

end IteratedComposition

/-! ### Monomial specialization -/

/-- Coordinatewise activation by hidden activation `j` of `MLPSpec.monomial d r` is the power layer
`powerActivation (r j)`. -/
@[simp]
theorem activation_monomial_eq_powerActivation [Monoid K] {ι : Type*} (d : Fin (L + 1) → ℕ)
    (r : Fin (L - 1) → ℕ) (j : Fin (L - 1)) :
    Neuromanifold.activation (ι := ι) ((monomial d r : MLPSpec K L).activation j) =
      powerActivation (r j) := by
  rw [powerActivation_def]
  exact congrArg Neuromanifold.activation (funext (monomial_activation d r j))

section Monomial

variable [Semiring K]

/-- In positive depth `L + 1`, the last bias-free hidden prefix of `MLPSpec.monomial d r` folds
`powerActivation (r i) () ∘ (w i.castSucc).mulVec` across the `L` hidden layers. -/
theorem evalPrefix_zeroBias_monomial_last_castSucc_eq_dfoldl (d : Fin (L + 2) → ℕ) (r : Fin L → ℕ)
    (w : (monomial d r : MLPSpec K (L + 1)).Weights)
    (x : Fin ((monomial d r : MLPSpec K (L + 1)).width 0) → K) :
    (monomial d r).evalPrefix ((monomial d r).zeroBias w) x (Fin.last L).castSucc =
      Fin.dfoldl L (fun i => Fin ((monomial d r : MLPSpec K (L + 1)).width i.castSucc) → K)
        (fun i => powerActivation (r i) () ∘ (w i.castSucc).mulVec) x := by
  simpa only [activation_monomial_eq_powerActivation] using
    (monomial d r).evalPrefix_zeroBias_last_castSucc_eq_dfoldl w x

/-- In positive depth `L + 1`, the affine realization of `MLPSpec.monomial d r` composes the
output layer `dense (θ (Fin.last L))` with the `L`-step fold of `powerActivation (r i) () ∘
dense (θ i.castSucc)`. -/
theorem realize_monomial_eq_dense_comp_dfoldl (d : Fin (L + 2) → ℕ) (r : Fin L → ℕ)
    (θ : (monomial d r : MLPSpec K (L + 1)).Parameters) :
    (monomial d r).realize θ =
      dense (θ (Fin.last L)) ∘
        Fin.dfoldl L (fun i => Fin ((monomial d r : MLPSpec K (L + 1)).width i.castSucc) → K)
          (fun i => powerActivation (r i) () ∘ dense (θ i.castSucc)) := by
  simpa only [activation_monomial_eq_powerActivation] using
    (monomial d r).realize_succ_eq_dense_comp_dfoldl θ

/-- In positive depth `L + 1`, the bias-free realization of `MLPSpec.monomial d r` composes the
linear output head `(w (Fin.last L)).mulVec` with the `L`-step fold of `powerActivation (r i) () ∘
(w i.castSucc).mulVec`. For a constant exponent `fun _ => r₀`, this is the polynomial network
`W_{L+1} ∘ σ_{r₀} ∘ ⋯ ∘ σ_{r₀} ∘ W₁` of Finkel–Rodriguez–Wu–Yahl, Definition 1. -/
theorem realizeWeights_monomial_eq_mulVec_comp_dfoldl (d : Fin (L + 2) → ℕ) (r : Fin L → ℕ)
    (w : (monomial d r : MLPSpec K (L + 1)).Weights) :
    (monomial d r).realizeWeights w =
      (w (Fin.last L)).mulVec ∘
        Fin.dfoldl L (fun i => Fin ((monomial d r : MLPSpec K (L + 1)).width i.castSucc) → K)
          (fun i => powerActivation (r i) () ∘ (w i.castSucc).mulVec) := by
  simpa only [activation_monomial_eq_powerActivation] using
    (monomial d r).realizeWeights_succ_eq_mulVec_comp_dfoldl w

end Monomial

/-! ### Realized-function sets -/

section RealizedFunctions

variable [NonUnitalNonAssocSemiring K]

/-- A depth-zero MLP realizes only the identity function. -/
@[simp]
theorem realizedFunctions_realize_depth_zero (A : MLPSpec K 0) :
    realizedFunctions A.realize = {id} := by
  rw [realizedFunctions_def, Set.range_unique, funext (A.realize_depth_zero default)]
  rfl

/-- A depth-zero bias-free MLP realizes only the identity function. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_zero (A : MLPSpec K 0) :
    realizedFunctions A.realizeWeights = {id} := by
  rw [realizedFunctions_def, Set.range_unique, funext (A.realizeWeights_depth_zero default)]
  rfl

/-- The affine neuromanifold of `A : MLPSpec K (L + 1)` consists of the composites
`g ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ f` with `f` a dense affine layer and `g`
realized by `A.tail`. -/
theorem realizedFunctions_realize_succ (A : MLPSpec K (L + 1)) :
    realizedFunctions A.realize =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ f)
        (realizedFunctions dense) (realizedFunctions A.tail.realize) :=
  realizedFunctions_eq_image2_of_equiv (Fin.consEquiv _).symm _ A.realize_cons

/-- The bias-free neuromanifold of `A : MLPSpec K (L + 1)` consists of the composites
`g ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ f` with `f` a linear layer `Matrix.mulVec`
and `g` realized by `A.tail` on bias-free parameters. -/
theorem realizedFunctions_realizeWeights_succ (A : MLPSpec K (L + 1)) :
    realizedFunctions A.realizeWeights =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ f)
        (realizedFunctions Matrix.mulVec) (realizedFunctions A.tail.realizeWeights) :=
  realizedFunctions_eq_image2_of_equiv (Fin.consEquiv _).symm _ A.realizeWeights_cons

/-- A one-layer MLP has the same neuromanifold as `dense`. -/
@[simp]
theorem realizedFunctions_realize_depth_one (A : MLPSpec K 1) :
    realizedFunctions A.realize = realizedFunctions dense := by
  let e : A.Parameters ≃ Matrix (Fin (A.width 1)) (Fin (A.width 0)) K × (Fin (A.width 1) → K) :=
    Equiv.piUnique _
  have h : A.realize = dense ∘ e := funext A.realize_depth_one_eq_dense
  rw [realizedFunctions_def, h, e.surjective.range_comp, ← realizedFunctions_def]

/-- A one-layer bias-free MLP has the same neuromanifold as `Matrix.mulVec`. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_one (A : MLPSpec K 1) :
    realizedFunctions A.realizeWeights = realizedFunctions Matrix.mulVec := by
  let e : A.Weights ≃ Matrix (Fin (A.width 1)) (Fin (A.width 0)) K := Equiv.piUnique _
  have h : A.realizeWeights = Matrix.mulVec ∘ e :=
    funext fun w => funext (A.realizeWeights_depth_one w)
  rw [realizedFunctions_def, h, e.surjective.range_comp, ← realizedFunctions_def]

/-- In depth at least two, the affine neuromanifold splits off the first hidden layer
`Neuromanifold.activation (A.activation 0) () ∘ dense`. -/
theorem realizedFunctions_realize_succ_succ (A : MLPSpec K (L + 2)) :
    realizedFunctions A.realize =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions dense) (realizedFunctions A.tail.realize) := by
  have h0 : A.layerActivation 0 = A.activation (0 : Fin (L + 1)) :=
    A.layerActivation_castSucc (0 : Fin (L + 1))
  rw [realizedFunctions_realize_succ]
  simp_rw [h0]
  rfl

/-- In depth at least two, the bias-free neuromanifold splits off the first hidden layer
`Neuromanifold.activation (A.activation 0) () ∘ Matrix.mulVec`. -/
theorem realizedFunctions_realizeWeights_succ_succ (A : MLPSpec K (L + 2)) :
    realizedFunctions A.realizeWeights =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions Matrix.mulVec) (realizedFunctions A.tail.realizeWeights) := by
  have h0 : A.layerActivation 0 = A.activation (0 : Fin (L + 1)) :=
    A.layerActivation_castSucc (0 : Fin (L + 1))
  rw [realizedFunctions_realizeWeights_succ]
  simp_rw [h0]
  rfl

end RealizedFunctions

/-- In depth `L + 2`, the affine neuromanifold of `MLPSpec.monomial d r` consists of the
composites `g ∘ powerActivation (r 0) () ∘ f` of a dense affine layer `f` and a function `g`
realized by `(monomial d r).tail`. -/
theorem realizedFunctions_realize_monomial_succ_succ [Semiring K] (d : Fin (L + 3) → ℕ)
    (r : Fin (L + 1) → ℕ) :
    realizedFunctions (monomial d r : MLPSpec K (L + 2)).realize =
      Set.image2 (fun f g => g ∘ powerActivation (r 0) () ∘ f)
        (realizedFunctions dense)
        (realizedFunctions (monomial d r : MLPSpec K (L + 2)).tail.realize) := by
  simpa only [activation_monomial_eq_powerActivation] using
    (monomial d r : MLPSpec K (L + 2)).realizedFunctions_realize_succ_succ

/-- In depth `L + 2`, the bias-free neuromanifold of `MLPSpec.monomial d r` consists of the
composites `g ∘ powerActivation (r 0) () ∘ f` of a linear layer `f` and a function `g` realized by
`(monomial d r).tail` on bias-free parameters. -/
theorem realizedFunctions_realizeWeights_monomial_succ_succ [Semiring K] (d : Fin (L + 3) → ℕ)
    (r : Fin (L + 1) → ℕ) :
    realizedFunctions (monomial d r : MLPSpec K (L + 2)).realizeWeights =
      Set.image2 (fun f g => g ∘ powerActivation (r 0) () ∘ f)
        (realizedFunctions Matrix.mulVec)
        (realizedFunctions (monomial d r : MLPSpec K (L + 2)).tail.realizeWeights) := by
  simpa only [activation_monomial_eq_powerActivation] using
    (monomial d r : MLPSpec K (L + 2)).realizedFunctions_realizeWeights_succ_succ

end MLPSpec

end TauCeti.Neuromanifold
