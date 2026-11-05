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

Splitting off layer `0` of `A : ConvolutionSpec K (L + 1)` via `A.tail : ConvolutionSpec K L`
(from `TauCeti.Geometry.Neuromanifold.Convolution.Chain`), whose underlying MLP specification is
`A.toMLPSpec.tail`, expresses positive-depth realization along `Fin.consEquiv` as
`Neuromanifold.compose`. Since `A.denseParameters` and `A.denseWeights` restrict to structured
matrices rather than ranging over all dense matrices, the neuromanifolds
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
  rw [evalPrefix_succ_eq_activation_affineConvolution, affineConvolution_zeroBias]

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

/-! ### Factoring the first layer via `ConvolutionSpec.tail` -/

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
  rw [evalPrefix_eq_mlp, MLPSpec.evalPrefix_succ_eq_tail, tail_denseParameters]
  refine (congrArg (fun v => A.toMLPSpec.tail.evalPrefix _ (Neuromanifold.activation _ () v) i)
    (congrFun (A.dense_denseParameters p 0) x)).trans ?_
  exact (congrFun (A.tail.evalPrefix_eq_mlp (Fin.tail p) _) i).symm

/-- From layer `1` onward, the bias-free prefixes of `A` are the bias-free prefixes of `A.tail`
evaluated at `convolution (A.length_eq 0) (w 0) x` after layer `0`'s activation. -/
theorem evalPrefix_zeroBias_succ_eq_tail (A : ConvolutionSpec K (L + 1)) (w : A.Weights)
    (x : Fin (A.width 0) → K) (i : Fin (L + 1)) :
    A.evalPrefix (A.zeroBias w) x i.succ =
      A.tail.evalPrefix (A.tail.zeroBias (Fin.tail w))
        (Neuromanifold.activation (A.toMLPSpec.layerActivation 0) ()
          (convolution (A.length_eq 0) (w 0) x)) i := by
  rw [evalPrefix_succ_eq_tail, tail_zeroBias]
  exact congrArg (fun v => A.tail.evalPrefix _ (Neuromanifold.activation _ () v) i)
    (congrFun (A.affineConvolution_zeroBias w 0) x)

/-- The realization of `A` factors through its first affine convolution layer, layer `0`'s
activation, and the realization of `A.tail`. -/
theorem realize_eq_tail_comp (A : ConvolutionSpec K (L + 1)) (p : A.Parameters) :
    A.realize p =
      A.tail.realize (Fin.tail p) ∘
        Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          affineConvolution (A.length_eq 0) (p 0) := by
  funext x
  -- `Fin.last (L + 1)` is definitionally `(Fin.last L).succ`.
  exact ((A.realize_def p x).trans (A.evalPrefix_succ_eq_tail p x (Fin.last L))).trans
    (A.tail.realize_def (Fin.tail p) _).symm

/-- On affine parameters assembled by `Fin.cons`, `A` realizes the composite of
`affineConvolution (A.length_eq 0) p₀`, layer `0`'s activation, and `A.tail.realize p`. -/
theorem realize_cons (A : ConvolutionSpec K (L + 1))
    (p₀ : (Fin (A.filterLength 0) → K) × K) (p : A.tail.Parameters) :
    A.realize (Fin.cons p₀ p) =
      A.tail.realize p ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
        affineConvolution (A.length_eq 0) p₀ := by
  rw [realize_eq_tail_comp, Fin.tail_def]
  rfl

/-- Under `Fin.consEquiv`, `A.realize` is `Neuromanifold.compose` of affine convolution layer `0`
(including its activation) and `A.tail.realize`. -/
theorem realize_comp_consEquiv (A : ConvolutionSpec K (L + 1)) :
    A.realize ∘ Fin.consEquiv _ =
      compose
        (fun p₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          affineConvolution (A.length_eq 0) p₀)
        A.tail.realize := by
  funext q
  simp only [Function.comp_apply, Fin.consEquiv_apply]
  exact (A.realize_cons q.1 q.2).trans
    (compose_apply
      (fun p₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
        affineConvolution (A.length_eq 0) p₀)
      A.tail.realize q).symm

/-- The bias-free realization of `A` factors through `convolution (A.length_eq 0) (w 0)`,
layer `0`'s activation, and the bias-free realization of `A.tail`. -/
theorem realizeWeights_eq_tail_comp (A : ConvolutionSpec K (L + 1)) (w : A.Weights) :
    A.realizeWeights w =
      A.tail.realizeWeights (Fin.tail w) ∘
        Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          convolution (A.length_eq 0) (w 0) := by
  funext x
  simp only [realizeWeights_def]
  dsimp only [Function.comp_def]
  simp only [realize_def]
  exact A.evalPrefix_zeroBias_succ_eq_tail w x (Fin.last L)

/-- On bias-free parameters assembled by `Fin.cons`, `A` realizes the composite of
`convolution (A.length_eq 0) w₀`, layer `0`'s activation, and `A.tail.realizeWeights w`. -/
theorem realizeWeights_cons (A : ConvolutionSpec K (L + 1))
    (w₀ : Fin (A.filterLength 0) → K) (w : A.tail.Weights) :
    A.realizeWeights (Fin.cons w₀ w) =
      A.tail.realizeWeights w ∘ Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
        convolution (A.length_eq 0) w₀ := by
  rw [realizeWeights_eq_tail_comp, Fin.tail_def]
  rfl

/-- Under `Fin.consEquiv`, `A.realizeWeights` is `Neuromanifold.compose` of bias-free convolution
layer `0` (including its activation) and `A.tail.realizeWeights`. -/
theorem realizeWeights_comp_consEquiv (A : ConvolutionSpec K (L + 1)) :
    A.realizeWeights ∘ Fin.consEquiv _ =
      compose
        (fun w₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
          convolution (A.length_eq 0) w₀)
        A.tail.realizeWeights := by
  funext q
  simp only [Function.comp_apply, Fin.consEquiv_apply]
  exact (A.realizeWeights_cons q.1 q.2).trans
    (compose_apply
      (fun w₀ => Neuromanifold.activation (A.toMLPSpec.layerActivation 0) () ∘
        convolution (A.length_eq 0) w₀)
      A.tail.realizeWeights q).symm

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
  rw [evalPrefix_eq_mlp, MLPSpec.evalPrefix_eq_dfoldl]
  -- `Fin.castLE i.isLt k.castSucc` and `(Fin.castLE _ k).castSucc` agree at `default` transparency.
  exact congrArg
    (fun g => Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K) g x)
    (funext fun k => by rw [dense_denseParameters])

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
  rw [evalPrefix_eq_dfoldl]
  exact congrArg
    (fun g => Fin.dfoldl i.val (fun k => Fin (A.width (Fin.castLE i.isLt k)) → K) g x)
    (funext fun k => by rw [affineConvolution_zeroBias])

/-- The affine realization of a convolutional specification is the `L`-step dependent fold
`Fin.dfoldl` of `Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
affineConvolution (A.length_eq i) (p i)`. -/
theorem realize_eq_dfoldl (A : ConvolutionSpec K L) (p : A.Parameters) :
    A.realize p =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
          affineConvolution (A.length_eq i) (p i)) := by
  rw [realize_eq_mlp, Function.comp_apply, MLPSpec.realize_eq_dfoldl]
  simp_rw [dense_denseParameters]

/-- The bias-free realization of a convolutional specification is the `L`-step dependent fold
`Fin.dfoldl` of `Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
convolution (A.length_eq i) (w i)`. -/
theorem realizeWeights_eq_dfoldl (A : ConvolutionSpec K L) (w : A.Weights) :
    A.realizeWeights w =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => Neuromanifold.activation (A.toMLPSpec.layerActivation i) () ∘
          convolution (A.length_eq i) (w i)) := by
  rw [realizeWeights_eq_mlp, Function.comp_apply, MLPSpec.realizeWeights_eq_dfoldl]
  simp_rw [mulVec_denseWeights]

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
  rw [evalPrefix_eq_mlp, MLPSpec.evalPrefix_last_castSucc_eq_dfoldl]
  -- `i.succ.castSucc` and `i.castSucc.succ` agree at `default` transparency.
  exact congrArg
    (fun g => Fin.dfoldl L (fun i => Fin (A.width i.castSucc) → K) g x)
    (funext fun i => by rw [dense_denseParameters])

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
  rw [evalPrefix_last_castSucc_eq_dfoldl]
  simp_rw [affineConvolution_zeroBias]

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
  dsimp only [Function.comp_def]
  rw [realize_succ, evalPrefix_last_castSucc_eq_dfoldl]
  rfl

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
  dsimp only [Function.comp_def]
  rw [realizeWeights_succ, evalPrefix_zeroBias_last_castSucc_eq_dfoldl]
  rfl

/-- When every hidden activation of `A` is `id`, its affine realization folds `affineConvolution`
directly across all `L` layers. -/
theorem realize_eq_dfoldl_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (p : A.Parameters) :
    A.realize p =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => affineConvolution (A.length_eq i) (p i)) := by
  rw [realize_eq_mlp, Function.comp_apply, A.toMLPSpec.realize_eq_dfoldl_of_activation_eq_id h]
  simp_rw [dense_denseParameters]

/-- When every hidden activation of `A` is `id`, its bias-free realization folds `convolution`
directly across all `L` layers, giving the linear convolutional network `C_{w_L} ∘ ⋯ ∘ C_{w_1}` of
Shahverdi, §2.1, equation (2.2). -/
theorem realizeWeights_eq_dfoldl_of_activation_eq_id (A : ConvolutionSpec K L)
    (h : ∀ j, A.activation j = id) (w : A.Weights) :
    A.realizeWeights w =
      Fin.dfoldl L (fun i => Fin (A.width i) → K)
        (fun i => convolution (A.length_eq i) (w i)) := by
  rw [realizeWeights_eq_mlp, Function.comp_apply,
    A.toMLPSpec.realizeWeights_eq_dfoldl_of_activation_eq_id h]
  simp_rw [mulVec_denseWeights]

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
  let e : A.Parameters ≃ (Fin (A.filterLength 0) → K) × K := Equiv.piUnique _
  have h : A.realize = affineConvolution (A.length_eq 0) ∘ e := funext A.realize_depth_one
  rw [realizedFunctions_def, h, e.surjective.range_comp, ← realizedFunctions_def]

/-- A one-layer bias-free convolutional network has the same neuromanifold as its `convolution`
layer. -/
@[simp]
theorem realizedFunctions_realizeWeights_depth_one (A : ConvolutionSpec K 1) :
    realizedFunctions A.realizeWeights = realizedFunctions (convolution (A.length_eq 0)) := by
  let e : A.Weights ≃ (Fin (A.filterLength 0) → K) := Equiv.piUnique _
  have h : A.realizeWeights = convolution (A.length_eq 0) ∘ e := funext A.realizeWeights_depth_one
  rw [realizedFunctions_def, h, e.surjective.range_comp, ← realizedFunctions_def]

/-- In depth at least two, the affine convolutional neuromanifold splits off the first hidden layer
`Neuromanifold.activation (A.activation 0) () ∘ affineConvolution (A.length_eq 0)`. -/
theorem realizedFunctions_realize_succ_succ (A : ConvolutionSpec K (L + 2)) :
    realizedFunctions A.realize =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions (affineConvolution (A.length_eq 0)))
        (realizedFunctions A.tail.realize) := by
  have h0 : A.toMLPSpec.layerActivation 0 = A.activation (0 : Fin (L + 1)) :=
    A.toMLPSpec.layerActivation_castSucc (0 : Fin (L + 1))
  rw [realizedFunctions_realize_succ]
  simp_rw [h0]
  rfl

/-- In depth at least two, the bias-free convolutional neuromanifold splits off the first hidden
layer `Neuromanifold.activation (A.activation 0) () ∘ convolution (A.length_eq 0)`. -/
theorem realizedFunctions_realizeWeights_succ_succ (A : ConvolutionSpec K (L + 2)) :
    realizedFunctions A.realizeWeights =
      Set.image2 (fun f g => g ∘ Neuromanifold.activation (A.activation (0 : Fin (L + 1))) () ∘ f)
        (realizedFunctions (convolution (A.length_eq 0)))
        (realizedFunctions A.tail.realizeWeights) := by
  have h0 : A.toMLPSpec.layerActivation 0 = A.activation (0 : Fin (L + 1)) :=
    A.toMLPSpec.layerActivation_castSucc (0 : Fin (L + 1))
  rw [realizedFunctions_realizeWeights_succ]
  simp_rw [h0]
  rfl

end RealizedFunctions

end ConvolutionSpec

end TauCeti.Neuromanifold
