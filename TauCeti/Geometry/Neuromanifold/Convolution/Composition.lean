/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Chain
public import TauCeti.Geometry.Neuromanifold.MLP.Composition

/-!
# Convolutional networks as iterated layer compositions

Because `ConvolutionSpec` evaluates its prefixes and realizations by passing structured
Toeplitz-like convolution matrices and constant bias vectors to `MLPSpec`, the dependent fold
descriptions of `TauCeti.Geometry.Neuromanifold.MLP.Composition` specialize directly to
single-channel valid convolutional chains:

* at each layer `i : Fin L`, `dense (A.denseParameters p i)` is `affineConvolution (A.length_eq i)
  (p i)` and `(A.denseWeights w i).mulVec` is `convolution (A.length_eq i) (w i)`;
* `A.realize p` and `A.realizeWeights w` are the `L`-step dependent folds (`Fin.dfoldl`) of these
  single-layer convolutional constructors composed with `Neuromanifold.activation`
  (`realize_eq_dfoldl`, `realizeWeights_eq_dfoldl`);
* in positive depth `L + 1`, the `L` hidden layers fold `Neuromanifold.activation (A.activation i)
  ()` with `affineConvolution` or `convolution`, and the output head applies
  `affineConvolution (A.length_eq (Fin.last L))` or `convolution (A.length_eq (Fin.last L))` with
  no activation (`realize_succ_eq_affineConvolution_comp_dfoldl`,
  `realizeWeights_succ_eq_convolution_comp_dfoldl`);
* when all hidden activations are `id`, `A.realize p` folds `affineConvolution` and
  `A.realizeWeights w` folds `convolution` directly (`realize_eq_dfoldl_of_activation_eq_id`,
  `realizeWeights_eq_dfoldl_of_activation_eq_id`), matching Shahverdi, §2.1, equation (2.2).

Dropping layer `0` of `A : ConvolutionSpec K (L + 1)` forms `A.tail : ConvolutionSpec K L`, whose
underlying MLP specification is `A.toMLPSpec.tail`. Since `A.denseParameters` and `A.denseWeights`
restrict to structured matrices rather than ranging over all dense matrices, the neuromanifolds
`realizedFunctions A.realize` and `realizedFunctions A.realizeWeights` are built from
`realizedFunctions (affineConvolution (A.length_eq 0))` and
`realizedFunctions (convolution (A.length_eq 0))` rather than from `realizedFunctions dense` and
`realizedFunctions Matrix.mulVec`.

## References

* Vahid Shahverdi, *Algebraic Complexity and Neurovariety of Linear Convolutional Networks*,
  [arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1, equations (2.1)–(2.2).
* Giovanni Luca Marchetti, Vahid Shahverdi, Stefano Mereta, Matthew Trager, and Kathlén Kohn,
  *Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
  [arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
-/

public section

namespace TauCeti.Neuromanifold

namespace ConvolutionSpec

variable {K : Type*} {L : ℕ}

/-! ### Single-layer steps via concrete convolution constructors -/

section LayerStep

variable [NonUnitalNonAssocSemiring K]

/-- Structured dense parameters at layer `i` realize `affineConvolution` of the layer's filter and
shared scalar bias. -/
theorem dense_denseParameters (A : ConvolutionSpec K L) (p : A.Parameters) (i : Fin L) :
    dense (A.denseParameters p i) = affineConvolution (A.length_eq i) (p i) := by
  funext x
  rw [dense_apply, denseParameters_apply, affineConvolution_eq_mulVec_add]

/-- The structured weight matrix at layer `i` realizes `convolution` of the layer's filter. -/
theorem mulVec_denseWeights (A : ConvolutionSpec K L) (w : A.Weights) (i : Fin L) :
    (A.denseWeights w i).mulVec = convolution (A.length_eq i) (w i) := by
  funext x
  rw [denseWeights_apply, convolutionMatrix_mulVec]

/-- Each convolutional prefix step applies `affineConvolution` followed by the coordinatewise layer
activation. -/
theorem evalPrefix_succ_eq_activation_affineConvolution (A : ConvolutionSpec K L)
    (p : A.Parameters) (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix p x i.succ =
      Neuromanifold.activation (A.toMLPSpec.layerActivation i) ()
        (affineConvolution (A.length_eq i) (p i) (A.evalPrefix p x i.castSucc)) := by
  rw [evalPrefix_eq_mlp, A.toMLPSpec.evalPrefix_succ_eq_activation_dense, dense_denseParameters,
    ← evalPrefix_eq_mlp]

/-- Each bias-free convolutional prefix step applies `convolution` followed by the coordinatewise
layer activation. -/
theorem evalPrefix_zeroBias_succ_eq_activation_convolution (A : ConvolutionSpec K L)
    (w : A.Weights) (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix (A.zeroBias w) x i.succ =
      Neuromanifold.activation (A.toMLPSpec.layerActivation i) ()
        (convolution (A.length_eq i) (w i) (A.evalPrefix (A.zeroBias w) x i.castSucc)) := by
  rw [evalPrefix_succ_eq_activation_affineConvolution, zeroBias_apply, affineConvolution_zero_bias]

/-- In positive depth, hidden layer `i + 1` applies `affineConvolution` followed by the
coordinatewise hidden activation `A.activation i`. -/
theorem evalPrefix_castSucc_succ_eq_activation_affineConvolution (A : ConvolutionSpec K (L + 1))
    (p : A.Parameters) (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix p x i.castSucc.succ =
      Neuromanifold.activation (A.activation i) ()
        (affineConvolution (A.length_eq i.castSucc) (p i.castSucc)
          (A.evalPrefix p x i.castSucc.castSucc)) := by
  rw [evalPrefix_succ_eq_activation_affineConvolution, A.toMLPSpec.layerActivation_castSucc]

/-- In positive depth, bias-free hidden layer `i + 1` applies `convolution` followed by the
coordinatewise hidden activation `A.activation i`. -/
theorem evalPrefix_zeroBias_castSucc_succ_eq_activation_convolution (A : ConvolutionSpec K (L + 1))
    (w : A.Weights) (x : Fin (A.width 0) → K) (i : Fin L) :
    A.evalPrefix (A.zeroBias w) x i.castSucc.succ =
      Neuromanifold.activation (A.activation i) ()
        (convolution (A.length_eq i.castSucc) (w i.castSucc)
          (A.evalPrefix (A.zeroBias w) x i.castSucc.castSucc)) := by
  rw [evalPrefix_zeroBias_succ_eq_activation_convolution, A.toMLPSpec.layerActivation_castSucc]

end LayerStep

/-! ### Dropping the first layer -/

/-- The convolutional specification obtained from `A : ConvolutionSpec K (L + 1)` by dropping
layer `0`: its underlying MLP specification is `A.toMLPSpec.tail`, and its filter lengths and
strides are shifted up by one layer. Its body is exposed so that `A.tail.Parameters` and
`A.tail.Weights` are definitionally the tails of `A.Parameters` and `A.Weights`. -/
@[expose] def tail (A : ConvolutionSpec K (L + 1)) : ConvolutionSpec K L where
  toMLPSpec := A.toMLPSpec.tail
  filterLength i := A.filterLength i.succ
  stride i := A.stride i.succ
  length_eq i := A.length_eq i.succ

/-- The underlying MLP specification of `A.tail` is `A.toMLPSpec.tail`. -/
@[simp]
theorem toMLPSpec_tail (A : ConvolutionSpec K (L + 1)) :
    A.tail.toMLPSpec = A.toMLPSpec.tail := (rfl)

/-- The filter lengths of `A.tail` are those of `A` shifted up by one layer. -/
@[simp]
theorem tail_filterLength (A : ConvolutionSpec K (L + 1)) (i : Fin L) :
    A.tail.filterLength i = A.filterLength i.succ := (rfl)

/-- The strides of `A.tail` are those of `A` shifted up by one layer. -/
@[simp]
theorem tail_stride (A : ConvolutionSpec K (L + 1)) (i : Fin L) :
    A.tail.stride i = A.stride i.succ := (rfl)

/-- Taking the tail of convolutional parameters commutes with the zero-bias inclusion. -/
@[simp]
theorem tail_zeroBias [Zero K] (A : ConvolutionSpec K (L + 1)) (w : A.Weights) :
    Fin.tail (A.zeroBias w) = A.tail.zeroBias (Fin.tail w) :=
  funext fun i => (A.zeroBias_apply w i.succ).trans (A.tail.zeroBias_apply (Fin.tail w) i).symm

/-- Consing a first filter commutes with the zero-bias inclusion. -/
@[simp]
theorem zeroBias_cons [Zero K] (A : ConvolutionSpec K (L + 1))
    (w₀ : Fin (A.filterLength 0) → K) (w : A.tail.Weights) :
    A.zeroBias (Fin.cons w₀ w) = Fin.cons (w₀, 0) (A.tail.zeroBias w) := by
  let W := fun i : Fin (L + 1) => Fin (A.filterLength i) → K
  let P := fun i : Fin (L + 1) => (Fin (A.filterLength i) → K) × K
  funext i
  cases i using Fin.cases with
  | zero =>
    exact (A.zeroBias_apply _ 0).trans
      ((congrArg (·, (0 : K)) (Fin.cons_zero (α := W) w₀ w)).trans
        (Fin.cons_zero (α := P) (w₀, 0) (A.tail.zeroBias w)).symm)
  | succ i =>
    exact (A.zeroBias_apply _ i.succ).trans
      (((congrArg (·, (0 : K)) (Fin.cons_succ (α := W) w₀ w i)).trans
        (A.tail.zeroBias_apply w i).symm).trans
        (Fin.cons_succ (α := P) (w₀, 0) (A.tail.zeroBias w) i).symm)

/-- Taking the tail commutes with forming structured convolution matrices. -/
@[simp]
theorem tail_denseWeights [AddCommMonoid K] (A : ConvolutionSpec K (L + 1)) (w : A.Weights) :
    Fin.tail (A.denseWeights w) = A.tail.denseWeights (Fin.tail w) :=
  funext fun i => (A.denseWeights_apply w i.succ).trans
    (A.tail.denseWeights_apply (Fin.tail w) i).symm

/-- Consing a first filter commutes with forming structured convolution matrices. -/
@[simp]
theorem denseWeights_cons [AddCommMonoid K] (A : ConvolutionSpec K (L + 1))
    (w₀ : Fin (A.filterLength 0) → K) (w : A.tail.Weights) :
    A.denseWeights (Fin.cons w₀ w) =
      Fin.cons (convolutionMatrix (A.length_eq 0) w₀) (A.tail.denseWeights w) := by
  let W := fun i : Fin (L + 1) => Fin (A.filterLength i) → K
  let M := fun i : Fin (L + 1) => Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K
  funext i
  cases i using Fin.cases with
  | zero =>
    exact (A.denseWeights_apply _ 0).trans
      ((congrArg (convolutionMatrix (A.length_eq 0)) (Fin.cons_zero (α := W) w₀ w)).trans
        (Fin.cons_zero (α := M) (convolutionMatrix (A.length_eq 0) w₀)
          (A.tail.denseWeights w)).symm)
  | succ i =>
    exact (A.denseWeights_apply _ i.succ).trans
      (((congrArg (convolutionMatrix (A.length_eq i.succ)) (Fin.cons_succ (α := W) w₀ w i)).trans
        (A.tail.denseWeights_apply w i).symm).trans
        (Fin.cons_succ (α := M) (convolutionMatrix (A.length_eq 0) w₀)
          (A.tail.denseWeights w) i).symm)

/-- Taking the tail commutes with forming structured affine parameters. -/
@[simp]
theorem tail_denseParameters [AddCommMonoid K] (A : ConvolutionSpec K (L + 1)) (p : A.Parameters) :
    Fin.tail (A.denseParameters p) = A.tail.denseParameters (Fin.tail p) :=
  funext fun i => (A.denseParameters_apply p i.succ).trans
    (A.tail.denseParameters_apply (Fin.tail p) i).symm

/-- Consing first-layer affine parameters commutes with forming structured affine parameters. -/
@[simp]
theorem denseParameters_cons [AddCommMonoid K] (A : ConvolutionSpec K (L + 1))
    (p₀ : (Fin (A.filterLength 0) → K) × K) (p : A.tail.Parameters) :
    A.denseParameters (Fin.cons p₀ p) =
      Fin.cons (convolutionMatrix (A.length_eq 0) p₀.1, fun _ => p₀.2)
        (A.tail.denseParameters p) := by
  let P := fun i : Fin (L + 1) => (Fin (A.filterLength i) → K) × K
  let M := fun i : Fin (L + 1) =>
    Matrix (Fin (A.width i.succ)) (Fin (A.width i.castSucc)) K × (Fin (A.width i.succ) → K)
  funext i
  cases i using Fin.cases with
  | zero =>
    exact (A.denseParameters_apply _ 0).trans
      ((congrArg (fun q : P 0 => (convolutionMatrix (A.length_eq 0) q.1, fun _ => q.2))
        (Fin.cons_zero (α := P) p₀ p)).trans
        (Fin.cons_zero (α := M) (convolutionMatrix (A.length_eq 0) p₀.1, fun _ => p₀.2)
          (A.tail.denseParameters p)).symm)
  | succ i =>
    exact (A.denseParameters_apply _ i.succ).trans
      (((congrArg (fun q : P i.succ =>
          (convolutionMatrix (A.length_eq i.succ) q.1, fun _ => q.2))
          (Fin.cons_succ (α := P) p₀ p i)).trans
        (A.tail.denseParameters_apply p i).symm).trans
        (Fin.cons_succ (α := M) (convolutionMatrix (A.length_eq 0) p₀.1, fun _ => p₀.2)
          (A.tail.denseParameters p) i).symm)

section TailEvaluation

variable [NonUnitalNonAssocSemiring K]

/-- From layer `1` onward, the prefixes of `A` are the prefixes of `A.tail` evaluated at the output
of layer `0`. -/
theorem evalPrefix_succ_eq_tail (A : ConvolutionSpec K (L + 1)) (p : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix p x i.succ =
      A.tail.evalPrefix (Fin.tail p)
        (Neuromanifold.activation (A.toMLPSpec.layerActivation 0) ()
          (affineConvolution (A.length_eq 0) (p 0) x)) i := by
  have hd : dense (A.denseParameters p 0) x = affineConvolution (A.length_eq 0) (p 0) x :=
    congrFun (A.dense_denseParameters p 0) x
  exact (congrFun (A.evalPrefix_eq_mlp p x) i.succ).trans
    ((A.toMLPSpec.evalPrefix_succ_eq_tail (A.denseParameters p) x i).trans
      (((congrArg (fun q => A.toMLPSpec.tail.evalPrefix q _ i) (A.tail_denseParameters p)).trans
        (congrArg (fun v => A.toMLPSpec.tail.evalPrefix (A.tail.denseParameters (Fin.tail p))
          (Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () v) i) hd)).trans
        (congrFun (A.tail.evalPrefix_eq_mlp (Fin.tail p) _) i).symm))

/-- From layer `1` onward, the bias-free prefixes of `A` are the bias-free prefixes of `A.tail`
evaluated at `convolution (A.length_eq 0) (w 0) x` after layer `0`'s activation. -/
theorem evalPrefix_zeroBias_succ_eq_tail (A : ConvolutionSpec K (L + 1)) (w : A.Weights)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix (A.zeroBias w) x i.succ =
      A.tail.evalPrefix (A.tail.zeroBias (Fin.tail w))
        (Neuromanifold.activation (A.toMLPSpec.layerActivation 0) ()
          (convolution (A.length_eq 0) (w 0) x)) i := by
  have hc : affineConvolution (A.length_eq 0) (A.zeroBias w 0) x =
      convolution (A.length_eq 0) (w 0) x :=
    congrFun ((congrArg (affineConvolution (A.length_eq 0)) (A.zeroBias_apply w 0)).trans
      (affineConvolution_zero_bias (A.length_eq 0) (w 0))) x
  exact (A.evalPrefix_succ_eq_tail (A.zeroBias w) x i).trans
    ((congrArg (fun q => A.tail.evalPrefix q _ i) (A.tail_zeroBias w)).trans
      (congrArg (fun v => A.tail.evalPrefix (A.tail.zeroBias (Fin.tail w))
        (Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () v) i) hc))

/-- The realization of `A` factors through its first affine convolution layer, layer `0`'s
activation, and the realization of `A.tail`. -/
theorem realize_eq_tail_comp (A : ConvolutionSpec K (L + 1)) (p : A.Parameters) :
    A.realize p =
      A.tail.realize (Fin.tail p) ∘
        Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          affineConvolution (A.length_eq 0) (p 0) := by
  funext x
  exact ((A.realize_def p x).trans (A.evalPrefix_succ_eq_tail p x (Fin.last L))).trans
    (A.tail.realize_def (Fin.tail p) _).symm

/-- On affine parameters assembled by `Fin.cons`, `A` realizes the composite of
`affineConvolution (A.length_eq 0) p₀`, layer `0`'s activation, and `A.tail.realize p`. -/
theorem realize_cons (A : ConvolutionSpec K (L + 1))
    (p₀ : (Fin (A.filterLength 0) → K) × K) (p : A.tail.Parameters) :
    A.realize (Fin.cons p₀ p) =
      A.tail.realize p ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
        affineConvolution (A.length_eq 0) p₀ := by
  let P := fun i : Fin (L + 1) => (Fin (A.filterLength i) → K) × K
  exact (A.realize_eq_tail_comp (Fin.cons (α := P) p₀ p)).trans
    ((congrArg (fun q => A.tail.realize q ∘
        Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          affineConvolution (A.length_eq 0) (Fin.cons (α := P) p₀ p 0))
      (Fin.tail_cons (α := P) p₀ p)).trans
      (congrArg (fun q₀ => A.tail.realize p ∘
          Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
            affineConvolution (A.length_eq 0) q₀)
        (Fin.cons_zero (α := P) p₀ p)))

/-- Under `Fin.consEquiv`, `A.realize` is `Neuromanifold.compose` of affine convolution layer `0`
(including its activation) and `A.tail.realize`. -/
theorem realize_comp_consEquiv (A : ConvolutionSpec K (L + 1)) :
    A.realize ∘ Fin.consEquiv _ =
      compose
        (fun p₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          affineConvolution (A.length_eq 0) p₀)
        A.tail.realize :=
  funext fun q =>
    (Function.comp_apply (f := A.realize) (x := q)).trans
      ((congrArg A.realize (Fin.consEquiv_apply _ q)).trans
        ((A.realize_cons q.1 q.2).trans
          (compose_apply
            (fun p₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
              affineConvolution (A.length_eq 0) p₀)
            A.tail.realize q).symm))

/-- The bias-free realization of `A` factors through `convolution (A.length_eq 0) (w 0)`,
layer `0`'s activation, and the bias-free realization of `A.tail`. -/
theorem realizeWeights_eq_tail_comp (A : ConvolutionSpec K (L + 1)) (w : A.Weights) :
    A.realizeWeights w =
      A.tail.realizeWeights (Fin.tail w) ∘
        Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          convolution (A.length_eq 0) (w 0) := by
  funext x
  exact ((congrFun (congrFun A.realizeWeights_def w) x).trans
    ((A.realize_def _ x).trans
      ((A.evalPrefix_zeroBias_succ_eq_tail w x (Fin.last L)).trans
        ((A.tail.realize_def _ _).symm.trans
          (congrFun (congrFun A.tail.realizeWeights_def (Fin.tail w)).symm _)))))

/-- On bias-free parameters assembled by `Fin.cons`, `A` realizes the composite of
`convolution (A.length_eq 0) w₀`, layer `0`'s activation, and `A.tail.realizeWeights w`. -/
theorem realizeWeights_cons (A : ConvolutionSpec K (L + 1))
    (w₀ : Fin (A.filterLength 0) → K) (w : A.tail.Weights) :
    A.realizeWeights (Fin.cons w₀ w) =
      A.tail.realizeWeights w ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
        convolution (A.length_eq 0) w₀ := by
  let W := fun i : Fin (L + 1) => Fin (A.filterLength i) → K
  exact (A.realizeWeights_eq_tail_comp (Fin.cons (α := W) w₀ w)).trans
    ((congrArg (fun q => A.tail.realizeWeights q ∘
        Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          convolution (A.length_eq 0) (Fin.cons (α := W) w₀ w 0))
      (Fin.tail_cons (α := W) w₀ w)).trans
      (congrArg (fun q₀ => A.tail.realizeWeights w ∘
          Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
            convolution (A.length_eq 0) q₀)
        (Fin.cons_zero (α := W) w₀ w)))

/-- Under `Fin.consEquiv`, `A.realizeWeights` is `Neuromanifold.compose` of bias-free convolution
layer `0` (including its activation) and `A.tail.realizeWeights`. -/
theorem realizeWeights_comp_consEquiv (A : ConvolutionSpec K (L + 1)) :
    A.realizeWeights ∘ Fin.consEquiv _ =
      compose
        (fun w₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          convolution (A.length_eq 0) w₀)
        A.tail.realizeWeights :=
  funext fun q =>
    (Function.comp_apply (f := A.realizeWeights) (x := q)).trans
      ((congrArg A.realizeWeights (Fin.consEquiv_apply _ q)).trans
        ((A.realizeWeights_cons q.1 q.2).trans
          (compose_apply
            (fun w₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
              convolution (A.length_eq 0) w₀)
            A.tail.realizeWeights q).symm))

end TailEvaluation

/-! ### Iterated composition via `Fin.dfoldl` -/

section IteratedComposition

variable [NonUnitalNonAssocSemiring K]

/-- Every convolutional prefix `A.evalPrefix p x i` is the `i.val`-step dependent left fold
`Fin.dfoldl` of `Neuromanifold.activation (A.toMLPSpec.layerActivation k) () ∘
affineConvolution (A.length_eq k) (p k)`. -/
theorem evalPrefix_eq_dfoldl (A : ConvolutionSpec K L) (p : A.Parameters)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix p x i =
      Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K)
        (fun k =>
          Neuromanifold.activation
              (A.toMLPSpec.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) () ∘
            affineConvolution (A.length_eq (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
              (p (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))
        x := by
  refine (congrFun (A.evalPrefix_eq_mlp p x) i).trans
    ((A.toMLPSpec.evalPrefix_eq_dfoldl (A.denseParameters p) x i).trans ?_)
  exact congrArg
    (fun f => Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K) f x)
    (funext fun k =>
      congrArg
        (Neuromanifold.activation
            (A.toMLPSpec.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) () ∘ ·)
        (A.dense_denseParameters p (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))

/-- Every bias-free convolutional prefix `A.evalPrefix (A.zeroBias w) x i` is the `i.val`-step
dependent left fold `Fin.dfoldl` of `Neuromanifold.activation (A.toMLPSpec.layerActivation k) () ∘
convolution (A.length_eq k) (w k)`. -/
theorem evalPrefix_zeroBias_eq_dfoldl (A : ConvolutionSpec K L) (w : A.Weights)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix (A.zeroBias w) x i =
      Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K)
        (fun k =>
          Neuromanifold.activation
              (A.toMLPSpec.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) () ∘
            convolution (A.length_eq (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
              (w (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))
        x := by
  refine (A.evalPrefix_eq_dfoldl (A.zeroBias w) x i).trans ?_
  exact congrArg
    (fun f => Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K) f x)
    (funext fun k =>
      congrArg
        (Neuromanifold.activation
            (A.toMLPSpec.layerActivation (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) () ∘ ·)
        ((congrArg
            (affineConvolution (A.length_eq (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))
            (A.zeroBias_apply w (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))).trans
          (affineConvolution_zero_bias
            (A.length_eq (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
            (w (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))))

/-- The affine realization of a convolutional specification is the `L`-step dependent fold
`Fin.dfoldl` of `Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
affineConvolution (A.length_eq i) (p i)`. -/
theorem realize_eq_dfoldl (A : ConvolutionSpec K L) (p : A.Parameters) :
    A.realize p =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
          affineConvolution (A.length_eq i) (p i)) := by
  refine (congrFun A.realize_eq_mlp p).trans
    ((A.toMLPSpec.realize_eq_dfoldl (A.denseParameters p)).trans ?_)
  exact congrArg (Fin.dfoldl L (fun i => Fin (A.width i) → K))
    (funext fun i =>
      congrArg (Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘ ·)
        (A.dense_denseParameters p i))

/-- The bias-free realization of a convolutional specification is the `L`-step dependent fold
`Fin.dfoldl` of `Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
convolution (A.length_eq i) (w i)`. -/
theorem realizeWeights_eq_dfoldl (A : ConvolutionSpec K L) (w : A.Weights) :
    A.realizeWeights w =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
          convolution (A.length_eq i) (w i)) := by
  refine (congrFun A.realizeWeights_eq_mlp w).trans
    ((A.toMLPSpec.realizeWeights_eq_dfoldl (A.denseWeights w)).trans ?_)
  exact congrArg (Fin.dfoldl L (fun i => Fin (A.width i) → K))
    (funext fun i =>
      congrArg (Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘ ·)
        (A.mulVec_denseWeights w i))

/-- In positive depth `L + 1`, the last hidden prefix folds the `L` hidden convolutional layers
`Neuromanifold.activation (A.activation i) () ∘ affineConvolution (A.length_eq i.castSucc)
(p i.castSucc)`. -/
theorem evalPrefix_last_castSucc_eq_dfoldl (A : ConvolutionSpec K (L + 1)) (p : A.Parameters)
    (x : Fin (A.width 0) → K) :
    A.evalPrefix p x (Fin.last L).castSucc =
      Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
        (fun i => Neuromanifold.activation (A.activation i) () ∘
          affineConvolution (A.length_eq i.castSucc) (p i.castSucc))
        x := by
  refine (congrFun (A.evalPrefix_eq_mlp p x) (Fin.last L).castSucc).trans
    ((A.toMLPSpec.evalPrefix_last_castSucc_eq_dfoldl (A.denseParameters p) x).trans ?_)
  exact congrArg
    (fun f => Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K) f x)
    (funext fun i =>
      congrArg (Neuromanifold.activation (A.activation i) () ∘ ·)
        (A.dense_denseParameters p i.castSucc))

/-- In positive depth `L + 1`, the last bias-free hidden prefix folds the `L` hidden convolutional
layers `Neuromanifold.activation (A.activation i) () ∘ convolution (A.length_eq i.castSucc)
(w i.castSucc)`. -/
theorem evalPrefix_zeroBias_last_castSucc_eq_dfoldl (A : ConvolutionSpec K (L + 1)) (w : A.Weights)
    (x : Fin (A.width 0) → K) :
    A.evalPrefix (A.zeroBias w) x (Fin.last L).castSucc =
      Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
        (fun i => Neuromanifold.activation (A.activation i) () ∘
          convolution (A.length_eq i.castSucc) (w i.castSucc))
        x := by
  refine (A.evalPrefix_last_castSucc_eq_dfoldl (A.zeroBias w) x).trans ?_
  exact congrArg
    (fun f => Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K) f x)
    (funext fun i =>
      congrArg (Neuromanifold.activation (A.activation i) () ∘ ·)
        ((congrArg (affineConvolution (A.length_eq i.castSucc))
            (A.zeroBias_apply w i.castSucc)).trans
          (affineConvolution_zero_bias (A.length_eq i.castSucc) (w i.castSucc))))

/-- In positive depth `L + 1`, the affine realization composes the output layer
`affineConvolution (A.length_eq (Fin.last L)) (p (Fin.last L))` with the `L`-step hidden fold. -/
theorem realize_succ_eq_affineConvolution_comp_dfoldl (A : ConvolutionSpec K (L + 1))
    (p : A.Parameters) :
    A.realize p =
      affineConvolution (A.length_eq (Fin.last L)) (p (Fin.last L)) ∘
        Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
          (fun i => Neuromanifold.activation (A.activation i) () ∘
            affineConvolution (A.length_eq i.castSucc) (p i.castSucc)) := by
  funext x
  exact (A.realize_succ p x).trans
    (congrArg (affineConvolution (A.length_eq (Fin.last L)) (p (Fin.last L)))
      (A.evalPrefix_last_castSucc_eq_dfoldl p x))

/-- In positive depth `L + 1`, the bias-free realization composes the output head
`convolution (A.length_eq (Fin.last L)) (w (Fin.last L))` with the `L`-step hidden fold. -/
theorem realizeWeights_succ_eq_convolution_comp_dfoldl (A : ConvolutionSpec K (L + 1))
    (w : A.Weights) :
    A.realizeWeights w =
      convolution (A.length_eq (Fin.last L)) (w (Fin.last L)) ∘
        Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K)
          (fun i => Neuromanifold.activation (A.activation i) () ∘
            convolution (A.length_eq i.castSucc) (w i.castSucc)) := by
  funext x
  exact (A.realizeWeights_succ w x).trans
    (congrArg (convolution (A.length_eq (Fin.last L)) (w (Fin.last L)))
      (A.evalPrefix_zeroBias_last_castSucc_eq_dfoldl w x))

/-- When every hidden activation of `A` is `id`, its affine realization folds `affineConvolution`
directly across all `L` layers. -/
theorem realize_eq_dfoldl_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (p : A.Parameters) :
    A.realize p =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => affineConvolution (A.length_eq i) (p i)) := by
  have hlay : ∀ i : Fin L, A.toMLPSpec.layerActivation i = id := fun i =>
    if hi : i.val + 1 < L then
      (A.toMLPSpec.layerActivation_of_lt i hi).trans (h ⟨i.val, by omega⟩)
    else
      A.toMLPSpec.layerActivation_of_val_add_one_eq i (by omega)
  refine (A.realize_eq_dfoldl p).trans ?_
  exact congrArg (Fin.dfoldl L (fun i => Fin (A.width i) → K))
    (funext fun i =>
      (congrArg (· ∘ affineConvolution (A.length_eq i) (p i))
        ((congrArg (fun σ => Neuromanifold.activation (ι := Fin (A.width i.succ)) σ ())
          (hlay i)).trans (congrFun activation_id ()))).trans
        (Function.id_comp _))

/-- When every hidden activation of `A` is `id`, its bias-free realization folds `convolution`
directly across all `L` layers, giving the linear convolutional network `C_{w_L} ∘ ⋯ ∘ C_{w_1}` of
Shahverdi, §2.1, equation (2.2). -/
theorem realizeWeights_eq_dfoldl_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (w : A.Weights) :
    A.realizeWeights w =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => convolution (A.length_eq i) (w i)) := by
  have hlay : ∀ i : Fin L, A.toMLPSpec.layerActivation i = id := fun i =>
    if hi : i.val + 1 < L then
      (A.toMLPSpec.layerActivation_of_lt i hi).trans (h ⟨i.val, by omega⟩)
    else
      A.toMLPSpec.layerActivation_of_val_add_one_eq i (by omega)
  refine (A.realizeWeights_eq_dfoldl w).trans ?_
  exact congrArg (Fin.dfoldl L (fun i => Fin (A.width i) → K))
    (funext fun i =>
      (congrArg (· ∘ convolution (A.length_eq i) (w i))
        ((congrArg (fun σ => Neuromanifold.activation (ι := Fin (A.width i.succ)) σ ())
          (hlay i)).trans (congrFun activation_id ()))).trans
        (Function.id_comp _))

end IteratedComposition

/-! ### Realized-function sets -/

section RealizedFunctions

variable [NonUnitalNonAssocSemiring K]

/-- An empty convolutional network realizes only the identity function. -/
@[simp]
theorem realizedFunctions_realize_depth_zero (A : ConvolutionSpec K 0) :
    realizedFunctions A.realize = {id} := by
  rw [realizedFunctions_def, Set.range_unique, realize_depth_zero]

/-- An empty bias-free convolutional network realizes only the identity function. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_zero (A : ConvolutionSpec K 0) :
    realizedFunctions A.realizeWeights = {id} := by
  rw [realizedFunctions_def, Set.range_unique, realizeWeights_depth_zero]

/-- The affine neuromanifold of `A : ConvolutionSpec K (L + 1)` consists of the composites
`g ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘ f` with `f` realized by layer
`0`'s `affineConvolution` and `g` realized by `A.tail`. -/
theorem realizedFunctions_realize_succ (A : ConvolutionSpec K (L + 1)) :
    realizedFunctions A.realize =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘ f)
        (realizedFunctions (affineConvolution (A.length_eq 0)))
        (realizedFunctions A.tail.realize) :=
  realizedFunctions_eq_image2_of_equiv (Fin.consEquiv _).symm _ A.realize_cons

/-- The bias-free neuromanifold of `A : ConvolutionSpec K (L + 1)` consists of the composites
`g ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘ f` with `f` realized by layer
`0`'s `convolution` and `g` realized by `A.tail` on bias-free parameters. -/
theorem realizedFunctions_realizeWeights_succ (A : ConvolutionSpec K (L + 1)) :
    realizedFunctions A.realizeWeights =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘ f)
        (realizedFunctions (convolution (A.length_eq 0)))
        (realizedFunctions A.tail.realizeWeights) :=
  realizedFunctions_eq_image2_of_equiv (Fin.consEquiv _).symm _ A.realizeWeights_cons

/-- A one-layer convolutional network has the same neuromanifold as its `affineConvolution`
layer. -/
@[simp]
theorem realizedFunctions_realize_depth_one (A : ConvolutionSpec K 1) :
    realizedFunctions A.realize = realizedFunctions (affineConvolution (A.length_eq 0)) := by
  let P := fun i : Fin 1 => (Fin (A.filterLength i) → K) × K
  ext f
  simp only [mem_realizedFunctions]
  exact ⟨fun ⟨p, h⟩ => ⟨p 0, (A.realize_depth_one p).symm.trans h⟩,
    fun ⟨p₀, h⟩ => ⟨Fin.cons (α := P) p₀ (fun i => i.elim0),
      (A.realize_depth_one _).trans
        ((congrArg (affineConvolution (A.length_eq 0))
          (Fin.cons_zero (α := P) p₀ (fun i => i.elim0))).trans h)⟩⟩

/-- A one-layer bias-free convolutional network has the same neuromanifold as its `convolution`
layer. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_one (A : ConvolutionSpec K 1) :
    realizedFunctions A.realizeWeights = realizedFunctions (convolution (A.length_eq 0)) := by
  let W := fun i : Fin 1 => Fin (A.filterLength i) → K
  ext f
  simp only [mem_realizedFunctions]
  exact ⟨fun ⟨w, h⟩ => ⟨w 0, (A.realizeWeights_depth_one w).symm.trans h⟩,
    fun ⟨w₀, h⟩ => ⟨Fin.cons (α := W) w₀ (fun i => i.elim0),
      (A.realizeWeights_depth_one _).trans
        ((congrArg (convolution (A.length_eq 0))
          (Fin.cons_zero (α := W) w₀ (fun i => i.elim0))).trans h)⟩⟩

/-- In depth at least two, the affine convolutional neuromanifold splits off the first hidden layer
`Neuromanifold.activation (A.activation 0) () ∘ affineConvolution (A.length_eq 0)`. -/
theorem realizedFunctions_realize_succ_succ (A : ConvolutionSpec K (L + 2)) :
    realizedFunctions A.realize =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions (affineConvolution (A.length_eq 0)))
        (realizedFunctions A.tail.realize) :=
  A.realizedFunctions_realize_succ.trans
    (congrArg (fun σ => Set.image2 (fun f g => g ∘ Neuromanifold.activation σ () ∘ f)
      (realizedFunctions (affineConvolution (A.length_eq 0)))
      (realizedFunctions A.tail.realize))
      (A.toMLPSpec.layerActivation_castSucc (0 : Fin (L + 1))))

/-- In depth at least two, the bias-free convolutional neuromanifold splits off the first hidden
layer `Neuromanifold.activation (A.activation 0) () ∘ convolution (A.length_eq 0)`. -/
theorem realizedFunctions_realizeWeights_succ_succ (A : ConvolutionSpec K (L + 2)) :
    realizedFunctions A.realizeWeights =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions (convolution (A.length_eq 0)))
        (realizedFunctions A.tail.realizeWeights) :=
  A.realizedFunctions_realizeWeights_succ.trans
    (congrArg (fun σ => Set.image2 (fun f g => g ∘ Neuromanifold.activation σ () ∘ f)
      (realizedFunctions (convolution (A.length_eq 0)))
      (realizedFunctions A.tail.realizeWeights))
      (A.toMLPSpec.layerActivation_castSucc (0 : Fin (L + 1))))

end RealizedFunctions

end ConvolutionSpec

end TauCeti.Neuromanifold
