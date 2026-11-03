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
  (`realize_succ_eq_dense_comp_dfoldl`, `realizeWeights_succ_eq_mulVec_comp_dfoldl`).

For the monomial specification `MLPSpec.monomial d r` of positive depth `L + 1`, each hidden layer
uses `powerActivation (r i) ()`, giving `(w (Fin.last L)).mulVec ∘ Fin.dfoldl L … (fun i =>
powerActivation (r i) () ∘ (w i.castSucc).mulVec)`
(`realizeWeights_monomial_eq_mulVec_comp_dfoldl`). Taking a constant hidden exponent `fun _ => r`
recovers the bias-free polynomial network `W_{L+1} ∘ σ_r ∘ ⋯ ∘ σ_r ∘ W₁` of
Finkel–Rodriguez–Wu–Yahl, Definition 1.

Dropping layer `0` of any specification `A : MLPSpec K (L + 1)` yields `A.tail : MLPSpec K L`.
Unlike `MLPSpec.lowerLayers` and `MLPSpec.upperLayers` in
`TauCeti.Geometry.Neuromanifold.MLP.Append`, which split at an interior hidden layer and require
depth at least `2`, `MLPSpec.tail` applies at every positive depth, including depth `1` where
`A.tail` has depth `0`. Together with the depth-zero and depth-one neuromanifolds, `MLPSpec.tail`
gives a layer-by-layer recursion for `realizedFunctions A.realize` and
`realizedFunctions A.realizeWeights`.

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

/-- In positive depth, the output layer applies `dense` to the last hidden prefix. -/
theorem realize_succ_eq_dense (A : MLPSpec K (L + 1)) (θ : A.Parameters)
    (x : Fin (A.width 0) → K) :
    A.realize θ x = dense (θ (Fin.last L)) (A.evalPrefix θ x (Fin.last L).castSucc) := by
  rw [realize_succ, dense_apply]

/-- A depth-zero MLP realizes the identity map. -/
theorem realize_depth_zero_eq_id (A : MLPSpec K 0) (θ : A.Parameters) :
    A.realize θ = id :=
  funext (A.realize_depth_zero θ)

/-- A depth-zero MLP realizes the identity map on bias-free parameters. -/
theorem realizeWeights_depth_zero_eq_id (A : MLPSpec K 0) (w : A.Weights) :
    A.realizeWeights w = id :=
  funext (A.realizeWeights_depth_zero w)

/-- A one-layer MLP realizes the dense affine layer `dense (θ 0)`. -/
theorem realize_depth_one_eq_dense (A : MLPSpec K 1) (θ : A.Parameters) :
    A.realize θ = dense (θ 0) := by
  funext x
  rw [realize_depth_one, dense_apply]

/-- A one-layer bias-free MLP realizes the linear layer `(w 0).mulVec`. -/
theorem realizeWeights_depth_one_eq_mulVec (A : MLPSpec K 1) (w : A.Weights) :
    A.realizeWeights w = (w 0).mulVec :=
  funext (A.realizeWeights_depth_one w)

end LayerStep

/-! ### Dropping the first layer -/

/-- The specification obtained from `A : MLPSpec K (L + 1)` by dropping layer `0`: its widths are
`A.width 1, …, A.width (L + 1)` and its hidden activations are those of `A` above layer `1`.
Its body is exposed so that `A.tail.Parameters` and `A.tail.Weights` are definitionally the tails
of `A.Parameters` and `A.Weights`. -/
@[expose] def tail (A : MLPSpec K (L + 1)) : MLPSpec K L where
  width i := A.width i.succ
  activation j := A.activation ⟨j.val + 1, by omega⟩

/-- The widths of `A.tail` are the widths of `A` shifted up by one layer. -/
@[simp]
theorem tail_width (A : MLPSpec K (L + 1)) (i : Fin (L + 1)) :
    A.tail.width i = A.width i.succ := (rfl)

/-- The hidden activations of `A.tail` are those of `A` shifted up by one hidden layer. -/
theorem tail_activation (A : MLPSpec K (L + 1)) (j : Fin (L - 1)) :
    A.tail.activation j = A.activation ⟨j.val + 1, by omega⟩ := (rfl)

/-- In depth at least two, hidden activation `j` of `A.tail` is hidden activation `j.succ` of
`A`. -/
@[simp]
theorem tail_activation_succ (A : MLPSpec K (L + 2)) (j : Fin L) :
    A.tail.activation j = A.activation j.succ :=
  congrArg A.activation (Fin.ext rfl)

/-- Each layer of `A.tail` applies the same scalar activation as the corresponding shifted layer of
`A`. -/
@[simp]
theorem layerActivation_tail (A : MLPSpec K (L + 1)) (i : Fin L) :
    A.tail.layerActivation i = A.layerActivation i.succ := by
  by_cases h : i.val + 1 < L
  · rw [A.tail.layerActivation_of_lt i h, A.layerActivation_of_lt i.succ (by simp; omega),
      tail_activation]
    exact congrArg A.activation (Fin.ext rfl)
  · rw [A.tail.layerActivation_of_val_add_one_eq i (by omega),
      A.layerActivation_of_val_add_one_eq i.succ (by simp; omega)]

/-- Dropping the first layer of `MLPSpec.linear` drops the first width. -/
@[simp]
theorem tail_linear (d : Fin (L + 2) → ℕ) :
    (linear d : MLPSpec K (L + 1)).tail = linear (Fin.tail d) := by
  ext <;> simp [Fin.tail, tail_activation]

/-- Dropping the first layer of `MLPSpec.polynomial` in depth `L + 2` drops the first width and the
first hidden polynomial. -/
@[simp]
theorem tail_polynomial [Semiring K] (d : Fin (L + 3) → ℕ) (p : Fin (L + 1) → Polynomial K) :
    (polynomial d p : MLPSpec K (L + 2)).tail = polynomial (Fin.tail d) (Fin.tail p) := by
  ext <;> simp [Fin.tail]

/-- Dropping the first layer of `MLPSpec.monomial` in depth `L + 2` drops the first width and the
first hidden exponent. -/
@[simp]
theorem tail_monomial [Monoid K] (d : Fin (L + 3) → ℕ) (r : Fin (L + 1) → ℕ) :
    (monomial d r : MLPSpec K (L + 2)).tail = monomial (Fin.tail d) (Fin.tail r) := by
  ext <;> simp [Fin.tail]

/-- Taking the tail of parameters commutes with the zero-bias embedding. -/
@[simp]
theorem tail_zeroBias [Zero K] (A : MLPSpec K (L + 1)) (w : A.Weights) :
    Fin.tail (A.zeroBias w) = A.tail.zeroBias (Fin.tail w) :=
  funext fun i => (A.zeroBias_apply w i.succ).trans (A.tail.zeroBias_apply (Fin.tail w) i).symm

/-- Consing a first weight matrix commutes with the zero-bias embedding. -/
@[simp]
theorem zeroBias_cons [Zero K] (A : MLPSpec K (L + 1))
    (w₀ : Matrix (Fin (A.width 1)) (Fin (A.width 0)) K) (w : A.tail.Weights) :
    A.zeroBias (Fin.cons w₀ w) = Fin.cons (w₀, 0) (A.tail.zeroBias w) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    exact (A.zeroBias_apply _ 0).trans
      ((congrArg (·, (0 : Fin (A.width 1) → K))
        (Fin.cons_zero (α := fun i => Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K)
          w₀ w)).trans
        (Fin.cons_zero (α := fun i =>
          Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K × (Fin (A.width i.succ) → K))
          (w₀, 0) (A.tail.zeroBias w)).symm)
  | succ i =>
    exact (A.zeroBias_apply _ i.succ).trans
      (((congrArg (·, (0 : Fin (A.width i.succ.succ) → K))
          (Fin.cons_succ (α := fun k => Matrix (Fin (A.width k.succ)) (Fin (A.width k.castSucc)) K)
            w₀ w i)).trans
        (A.tail.zeroBias_apply w i).symm).trans
        (Fin.cons_succ (α := fun k =>
          Matrix (Fin (A.width k.succ)) (Fin (A.width k.castSucc)) K × (Fin (A.width k.succ) → K))
          (w₀, 0) (A.tail.zeroBias w) i).symm)

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
    exact (A.evalPrefix_succ_eq_activation_dense θ x 0).trans
      ((congrArg (fun v => Neuromanifold.activation (A.layerActivation 0) () (dense (θ 0) v))
        (A.evalPrefix_zero θ x)).trans (A.tail.evalPrefix_zero (Fin.tail θ) _).symm)
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
  have hd : dense (A.zeroBias w 0) x = (w 0).mulVec x :=
    congrFun ((congrArg dense (A.zeroBias_apply w 0)).trans (dense_mk_zero (w 0))) x
  exact (A.evalPrefix_succ_eq_tail (A.zeroBias w) x i).trans
    ((congrArg (fun p => A.tail.evalPrefix p _ i) (A.tail_zeroBias w)).trans
      (congrArg (fun v => A.tail.evalPrefix (A.tail.zeroBias (Fin.tail w))
        (Neuromanifold.activation (A.layerActivation 0) () v) i) hd))

/-- The realization of `A` factors through its first dense layer, layer `0`'s activation, and the
realization of `A.tail`. -/
theorem realize_eq_tail_comp (A : MLPSpec K (L + 1)) (θ : A.Parameters) :
    A.realize θ =
      A.tail.realize (Fin.tail θ) ∘
        Neuromanifold.activation (A.layerActivation 0) () ∘ dense (θ 0) := by
  funext x
  exact ((A.realize_def θ x).trans (A.evalPrefix_succ_eq_tail θ x (Fin.last L))).trans
    (A.tail.realize_def (Fin.tail θ) _).symm

/-- On affine parameters assembled by `Fin.cons`, `A` realizes the composite of `dense θ₀`,
layer `0`'s activation, and `A.tail.realize θ`. -/
theorem realize_cons (A : MLPSpec K (L + 1))
    (θ₀ : Matrix (Fin (A.width 1)) (Fin (A.width 0)) K × (Fin (A.width 1) → K))
    (θ : A.tail.Parameters) :
    A.realize (Fin.cons θ₀ θ) =
      A.tail.realize θ ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ dense θ₀ := by
  let P := fun i : Fin (L + 1) =>
    Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K × (Fin (A.width i.succ) → K)
  exact (A.realize_eq_tail_comp (Fin.cons (α := P) θ₀ θ)).trans
    ((congrArg (fun p => A.tail.realize p ∘
        Neuromanifold.activation (A.layerActivation 0) () ∘ dense (Fin.cons (α := P) θ₀ θ 0))
      (Fin.tail_cons (α := P) θ₀ θ)).trans
      (congrArg (fun p₀ => A.tail.realize θ ∘
          Neuromanifold.activation (A.layerActivation 0) () ∘ dense p₀)
        (Fin.cons_zero (α := P) θ₀ θ)))

/-- Under `Fin.consEquiv`, `A.realize` is `Neuromanifold.compose` of layer `0` (including its
activation) and `A.tail.realize`. -/
theorem realize_comp_consEquiv (A : MLPSpec K (L + 1)) :
    A.realize ∘ Fin.consEquiv _ =
      compose (fun θ₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ dense θ₀)
        A.tail.realize :=
  funext fun p =>
    (Function.comp_apply (f := A.realize) (x := p)).trans
      ((congrArg A.realize (Fin.consEquiv_apply _ p)).trans
        ((A.realize_cons p.1 p.2).trans
          (compose_apply (fun θ₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ dense θ₀)
            A.tail.realize p).symm))

/-- The bias-free realization of `A` factors through `(w 0).mulVec`, layer `0`'s activation, and
the bias-free realization of `A.tail`. -/
theorem realizeWeights_eq_tail_comp (A : MLPSpec K (L + 1)) (w : A.Weights) :
    A.realizeWeights w =
      A.tail.realizeWeights (Fin.tail w) ∘
        Neuromanifold.activation (A.layerActivation 0) () ∘ (w 0).mulVec := by
  funext x
  exact ((congrFun (congrFun A.realizeWeights_def w) x).trans
    ((A.realize_def _ x).trans
      ((A.evalPrefix_zeroBias_succ_eq_tail w x (Fin.last L)).trans
        ((A.tail.realize_def _ _).symm.trans
          (congrFun (congrFun A.tail.realizeWeights_def (Fin.tail w)).symm _)))))

/-- On bias-free parameters assembled by `Fin.cons`, `A` realizes the composite of `w₀.mulVec`,
layer `0`'s activation, and `A.tail.realizeWeights w`. -/
theorem realizeWeights_cons (A : MLPSpec K (L + 1))
    (w₀ : Matrix (Fin (A.width 1)) (Fin (A.width 0)) K) (w : A.tail.Weights) :
    A.realizeWeights (Fin.cons w₀ w) =
      A.tail.realizeWeights w ∘ Neuromanifold.activation (A.layerActivation 0) () ∘ w₀.mulVec := by
  let W := fun i : Fin (L + 1) => Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K
  exact (A.realizeWeights_eq_tail_comp (Fin.cons (α := W) w₀ w)).trans
    ((congrArg (fun p => A.tail.realizeWeights p ∘
        Neuromanifold.activation (A.layerActivation 0) () ∘ (Fin.cons (α := W) w₀ w 0).mulVec)
      (Fin.tail_cons (α := W) w₀ w)).trans
      (congrArg (fun p₀ => A.tail.realizeWeights w ∘
          Neuromanifold.activation (A.layerActivation 0) () ∘ Matrix.mulVec p₀)
        (Fin.cons_zero (α := W) w₀ w)))

/-- Under `Fin.consEquiv`, `A.realizeWeights` is `Neuromanifold.compose` of bias-free layer `0`
(including its activation) and `A.tail.realizeWeights`. -/
theorem realizeWeights_comp_consEquiv (A : MLPSpec K (L + 1)) :
    A.realizeWeights ∘ Fin.consEquiv _ =
      compose (fun w₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ w₀.mulVec)
        A.tail.realizeWeights :=
  funext fun p =>
    (Function.comp_apply (f := A.realizeWeights) (x := p)).trans
      ((congrArg A.realizeWeights (Fin.consEquiv_apply _ p)).trans
        ((A.realizeWeights_cons p.1 p.2).trans
          (compose_apply (fun w₀ => Neuromanifold.activation (A.layerActivation 0) () ∘ w₀.mulVec)
            A.tail.realizeWeights p).symm))

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
  exact (A.realize_succ_eq_dense θ x).trans
    (congrArg (dense (θ (Fin.last L))) (A.evalPrefix_last_castSucc_eq_dfoldl θ x))

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

/-- An identity-activation MLP with biases is the `L`-step fold of its dense affine layers. -/
theorem realize_linear_eq_dfoldl (d : Fin (L + 1) → ℕ) (θ : (linear d : MLPSpec K L).Parameters) :
    (linear d).realize θ =
      Fin.dfoldl L (fun i => Fin ((linear d : MLPSpec K L).width i) → K)
        (fun i => dense (θ i)) := by
  simpa only [layerActivation_linear, activation_id, Function.id_comp] using
    (linear d).realize_eq_dfoldl θ

/-- A bias-free identity-activation MLP is the `L`-step fold of its linear layers
`Matrix.mulVec`. -/
theorem realizeWeights_linear_eq_dfoldl (d : Fin (L + 1) → ℕ)
    (w : (linear d : MLPSpec K L).Weights) :
    (linear d).realizeWeights w =
      Fin.dfoldl L (fun i => Fin ((linear d : MLPSpec K L).width i) → K)
        (fun i => (w i).mulVec) := by
  simpa only [layerActivation_linear, activation_id, Function.id_comp] using
    (linear d).realizeWeights_eq_dfoldl w

end IteratedComposition

/-! ### Monomial specialization -/

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
  have hact : ∀ i : Fin L, (monomial d r : MLPSpec K (L + 1)).activation i = fun t => t ^ r i :=
    fun i => funext (monomial_activation d r i)
  simpa only [hact, ← powerActivation_def] using
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
  have hact : ∀ i : Fin L, (monomial d r : MLPSpec K (L + 1)).activation i = fun t => t ^ r i :=
    fun i => funext (monomial_activation d r i)
  simpa only [hact, ← powerActivation_def] using
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
  have hact : ∀ i : Fin L, (monomial d r : MLPSpec K (L + 1)).activation i = fun t => t ^ r i :=
    fun i => funext (monomial_activation d r i)
  simpa only [hact, ← powerActivation_def] using
    (monomial d r).realizeWeights_succ_eq_mulVec_comp_dfoldl w

end Monomial

/-! ### Realized-function sets -/

section RealizedFunctions

variable [NonUnitalNonAssocSemiring K]

/-- A depth-zero MLP realizes only the identity function. -/
@[simp]
theorem realizedFunctions_realize_depth_zero (A : MLPSpec K 0) :
    realizedFunctions A.realize = {id} := by
  rw [realizedFunctions_def, Set.range_unique, realize_depth_zero_eq_id]

/-- A depth-zero bias-free MLP realizes only the identity function. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_zero (A : MLPSpec K 0) :
    realizedFunctions A.realizeWeights = {id} := by
  rw [realizedFunctions_def, Set.range_unique, realizeWeights_depth_zero_eq_id]

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
  let P := fun i : Fin 1 =>
    Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K × (Fin (A.width i.succ) → K)
  ext f
  simp only [mem_realizedFunctions]
  exact ⟨fun ⟨θ, h⟩ => ⟨θ 0, (A.realize_depth_one_eq_dense θ).symm.trans h⟩,
    fun ⟨θ₀, h⟩ => ⟨Fin.cons (α := P) θ₀ (fun i => i.elim0),
      (A.realize_depth_one_eq_dense _).trans
        ((congrArg dense (Fin.cons_zero (α := P) θ₀ (fun i => i.elim0))).trans h)⟩⟩

/-- A one-layer bias-free MLP has the same neuromanifold as `Matrix.mulVec`. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_one (A : MLPSpec K 1) :
    realizedFunctions A.realizeWeights = realizedFunctions Matrix.mulVec := by
  let W := fun i : Fin 1 => Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K
  ext f
  simp only [mem_realizedFunctions]
  exact ⟨fun ⟨w, h⟩ => ⟨w 0, (A.realizeWeights_depth_one_eq_mulVec w).symm.trans h⟩,
    fun ⟨w₀, h⟩ => ⟨Fin.cons (α := W) w₀ (fun i => i.elim0),
      (A.realizeWeights_depth_one_eq_mulVec _).trans
        ((congrArg Matrix.mulVec (Fin.cons_zero (α := W) w₀ (fun i => i.elim0))).trans h)⟩⟩

/-- In depth at least two, the affine neuromanifold splits off the first hidden layer
`Neuromanifold.activation (A.activation 0) () ∘ dense`. -/
theorem realizedFunctions_realize_succ_succ (A : MLPSpec K (L + 2)) :
    realizedFunctions A.realize =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions dense) (realizedFunctions A.tail.realize) :=
  A.realizedFunctions_realize_succ.trans
    (congrArg (fun σ => Set.image2 (fun f g => g ∘ Neuromanifold.activation σ () ∘ f)
      (realizedFunctions dense) (realizedFunctions A.tail.realize))
      (A.layerActivation_castSucc (0 : Fin (L + 1))))

/-- In depth at least two, the bias-free neuromanifold splits off the first hidden layer
`Neuromanifold.activation (A.activation 0) () ∘ Matrix.mulVec`. -/
theorem realizedFunctions_realizeWeights_succ_succ (A : MLPSpec K (L + 2)) :
    realizedFunctions A.realizeWeights =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions Matrix.mulVec) (realizedFunctions A.tail.realizeWeights) :=
  A.realizedFunctions_realizeWeights_succ.trans
    (congrArg (fun σ => Set.image2 (fun f g => g ∘ Neuromanifold.activation σ () ∘ f)
      (realizedFunctions Matrix.mulVec) (realizedFunctions A.tail.realizeWeights))
      (A.layerActivation_castSucc (0 : Fin (L + 1))))

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
  let A : MLPSpec K (L + 2) := monomial d r
  have hact : Neuromanifold.activation (ι := Fin (A.width 1)) (A.activation (0 : Fin (L + 1))) () =
      powerActivation (ι := Fin (A.width 1)) (r 0) () :=
    congrFun ((congrArg (Neuromanifold.activation (ι := Fin (A.width 1)))
      (funext (monomial_activation d r (0 : Fin (L + 1))))).trans
      (powerActivation_def (ι := Fin (A.width 1)) (r 0)).symm) ()
  exact A.realizedFunctions_realize_succ_succ.trans
    (congrArg (fun a => Set.image2 (fun f g => g ∘ a ∘ f)
      (realizedFunctions dense) (realizedFunctions A.tail.realize)) hact)

/-- In depth `L + 2`, the bias-free neuromanifold of `MLPSpec.monomial d r` consists of the
composites `g ∘ powerActivation (r 0) () ∘ f` of a linear layer `f` and a function `g` realized by
`(monomial d r).tail` on bias-free parameters. -/
theorem realizedFunctions_realizeWeights_monomial_succ_succ [Semiring K] (d : Fin (L + 3) → ℕ)
    (r : Fin (L + 1) → ℕ) :
    realizedFunctions (monomial d r : MLPSpec K (L + 2)).realizeWeights =
      Set.image2 (fun f g => g ∘ powerActivation (r 0) () ∘ f)
        (realizedFunctions Matrix.mulVec)
        (realizedFunctions (monomial d r : MLPSpec K (L + 2)).tail.realizeWeights) := by
  let A : MLPSpec K (L + 2) := monomial d r
  have hact : Neuromanifold.activation (ι := Fin (A.width 1)) (A.activation (0 : Fin (L + 1))) () =
      powerActivation (ι := Fin (A.width 1)) (r 0) () :=
    congrFun ((congrArg (Neuromanifold.activation (ι := Fin (A.width 1)))
      (funext (monomial_activation d r (0 : Fin (L + 1))))).trans
      (powerActivation_def (ι := Fin (A.width 1)) (r 0)).symm) ()
  exact A.realizedFunctions_realizeWeights_succ_succ.trans
    (congrArg (fun a => Set.image2 (fun f g => g ∘ a ∘ f)
      (realizedFunctions Matrix.mulVec) (realizedFunctions A.tail.realizeWeights)) hact)

end MLPSpec

end TauCeti.Neuromanifold
