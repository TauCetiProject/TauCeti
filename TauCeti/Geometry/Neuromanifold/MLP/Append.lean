/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic
public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Concatenation of MLP specifications

An MLP specification `C` of depth `(L + 1) + (M + 1)` splits at its hidden layer `L + 1` into
two MLP specifications of positive depth:

* `C.lowerLayers`, of depth `L + 1`, formed by the layers `0, …, L + 1` of `C`;
* `C.upperLayers`, of depth `M + 1`, formed by the layers `L + 1, …, L + M + 2` of `C`;

joined by the activation `C.junctionActivation` of the hidden layer `L + 1`. Since an MLP
specification has no activation on its output layer, the output layer of `C.lowerLayers` is
affine, and `C` applies the junction activation to it before passing it to `C.upperLayers`.

The parameter spaces split accordingly: `C.splitParameters` identifies the affine parameters of
`C` with pairs of affine parameters of the two parts, and `C.splitWeights` does the same for
the bias-free parameters. Both send the parameters of a layer to the parameters of the same layer
in the corresponding part, with no reindexing of matrices. Under these identifications the
realization of `C` at the parameters joined from `θ₁` and `θ₂` is the composite
`C.upperLayers.realize θ₂ ∘ Pi.map (fun _ => σ) ∘ C.lowerLayers.realize θ₁`, where `σ` is the
junction activation (`realize_splitParameters_symm`). The realized functions of `C` are the
corresponding composites of realized functions of the parts (`realizedFunctions_realize`).

Conversely, `MLPSpec.append A B σ` concatenates two specifications of positive depth, joining
them with the activation `σ`. Its upper part is `B` and its junction activation is `σ`; its
lower part is `A` exactly when the output width of `A` is the input width of `B`
(`lowerLayers_append`); otherwise the concatenation uses the input width of `B` at the junction.
Every specification of depth `(L + 1) + (M + 1)` is the concatenation of its two parts
(`append_lowerLayers_upperLayers`).

A part of depth zero would realize the identity, and there is no hidden layer at which to join
it, so both parts are required to have positive depth.

The layer-by-layer reading of a network as a composite of realization maps follows
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
-/

public section

open Matrix

namespace TauCeti.Neuromanifold

namespace MLPSpec

variable {K : Type*} {L M : ℕ}

/-! ### The two parts of a specification -/

/-- The lower part of an MLP specification of depth `(L + 1) + (M + 1)`: the layers
`0, …, L + 1`, with the hidden activations below layer `L + 1`. Its output layer `L + 1` carries
no activation. Its body is exposed so that its parameter spaces are definitionally the families
of parameters of the first layers, as used by `splitParameters`. -/
@[expose] def lowerLayers (C : MLPSpec K (L + 1 + (M + 1))) : MLPSpec K (L + 1) where
  width := Fin.take (L + 2) (by omega) C.width
  activation := Fin.take L (by omega) C.activation

/-- The upper part of an MLP specification of depth `(L + 1) + (M + 1)`: the layers
`L + 1, …, L + M + 2`, with the hidden activations above layer `L + 1`. Its body is exposed so
that its parameter spaces are definitionally the families of parameters of the last layers, as
used by `splitParameters`. -/
@[expose] def upperLayers (C : MLPSpec K (L + 1 + (M + 1))) : MLPSpec K (M + 1) where
  width i := C.width (Fin.natAdd (L + 1) i)
  activation j := C.activation (Fin.natAdd (L + 1) j)

/-- The activation of the hidden layer `L + 1` of an MLP specification of depth
`(L + 1) + (M + 1)`, at which it splits into `lowerLayers` and `upperLayers`. -/
def junctionActivation (C : MLPSpec K (L + 1 + (M + 1))) : K → K :=
  C.activation (Fin.castAdd M (Fin.last L))

/-- The junction activation is the hidden activation at index `L` of the specification. -/
theorem junctionActivation_def (C : MLPSpec K (L + 1 + (M + 1))) :
    C.junctionActivation = C.activation (Fin.castAdd M (Fin.last L)) := (rfl)

/-- The widths of the lower part are the first widths of the specification. -/
@[simp]
theorem lowerLayers_width (C : MLPSpec K (L + 1 + (M + 1))) (i : Fin (L + 2)) :
    C.lowerLayers.width i = C.width (Fin.castLE (by omega) i) := (rfl)

/-- The hidden activations of the lower part are the first hidden activations of the
specification. -/
@[simp]
theorem lowerLayers_activation (C : MLPSpec K (L + 1 + (M + 1))) (j : Fin L) :
    C.lowerLayers.activation j = C.activation (Fin.castLE (by omega) j) := (rfl)

/-- The widths of the upper part are the last widths of the specification. -/
@[simp]
theorem upperLayers_width (C : MLPSpec K (L + 1 + (M + 1))) (i : Fin (M + 2)) :
    C.upperLayers.width i = C.width (Fin.natAdd (L + 1) i) := (rfl)

/-- The hidden activations of the upper part are the last hidden activations of the
specification. -/
@[simp]
theorem upperLayers_activation (C : MLPSpec K (L + 1 + (M + 1))) (j : Fin M) :
    C.upperLayers.activation j = C.activation (Fin.natAdd (L + 1) j) := (rfl)

/-- A layer of the lower part below its output layer applies the activation it has in the
specification. -/
theorem layerActivation_castAdd_castSucc (C : MLPSpec K (L + 1 + (M + 1))) (i : Fin L) :
    C.layerActivation (Fin.castAdd (M + 1) i.castSucc) =
      C.lowerLayers.layerActivation i.castSucc := by
  rw [layerActivation_castSucc, C.layerActivation_of_lt _ (by simp; omega)]
  rfl

/-- The output layer of the lower part applies the junction activation in the specification. -/
theorem layerActivation_castAdd_last (C : MLPSpec K (L + 1 + (M + 1))) :
    C.layerActivation (Fin.castAdd (M + 1) (Fin.last L)) = C.junctionActivation := by
  rw [C.layerActivation_of_lt _ (by simp)]
  rfl

/-- A layer of the upper part applies the activation it has in the specification. -/
theorem layerActivation_natAdd (C : MLPSpec K (L + 1 + (M + 1))) (i : Fin (M + 1)) :
    C.layerActivation (Fin.natAdd (L + 1) i) = C.upperLayers.layerActivation i := by
  by_cases h : i.val + 1 < M + 1
  · rw [C.upperLayers.layerActivation_of_lt i h, C.layerActivation_of_lt _ (by simp; omega)]
    rfl
  · rw [C.upperLayers.layerActivation_of_val_add_one_eq i (by omega),
      C.layerActivation_of_val_add_one_eq _ (by simp; omega)]

/-! ### Splitting the parameters -/

/-- The affine parameters of a specification of depth `(L + 1) + (M + 1)` are the pairs of
affine parameters of its lower and upper parts. -/
def splitParameters (C : MLPSpec K (L + 1 + (M + 1))) :
    C.Parameters ≃ C.lowerLayers.Parameters × C.upperLayers.Parameters :=
  (Equiv.piCongrLeft _ finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)

/-- The lower part of split affine parameters consists of the first layers. -/
@[simp]
theorem splitParameters_apply_fst (C : MLPSpec K (L + 1 + (M + 1))) (θ : C.Parameters)
    (i : Fin (L + 1)) : (C.splitParameters θ).1 i = θ (Fin.castAdd (M + 1) i) := (rfl)

/-- The upper part of split affine parameters consists of the last layers. -/
@[simp]
theorem splitParameters_apply_snd (C : MLPSpec K (L + 1 + (M + 1))) (θ : C.Parameters)
    (i : Fin (M + 1)) : (C.splitParameters θ).2 i = θ (Fin.natAdd (L + 1) i) := (rfl)

/-- Joined affine parameters agree with the lower part on the first layers. -/
@[simp]
theorem splitParameters_symm_apply_castAdd (C : MLPSpec K (L + 1 + (M + 1)))
    (p : C.lowerLayers.Parameters × C.upperLayers.Parameters) (i : Fin (L + 1)) :
    C.splitParameters.symm p (Fin.castAdd (M + 1) i) = p.1 i :=
  congrFun (congrArg Prod.fst (C.splitParameters.apply_symm_apply p)) i

/-- Joined affine parameters agree with the upper part on the last layers. -/
@[simp]
theorem splitParameters_symm_apply_natAdd (C : MLPSpec K (L + 1 + (M + 1)))
    (p : C.lowerLayers.Parameters × C.upperLayers.Parameters) (i : Fin (M + 1)) :
    C.splitParameters.symm p (Fin.natAdd (L + 1) i) = p.2 i :=
  congrFun (congrArg Prod.snd (C.splitParameters.apply_symm_apply p)) i

/-- The bias-free parameters of a specification of depth `(L + 1) + (M + 1)` are the pairs of
bias-free parameters of its lower and upper parts. -/
def splitWeights (C : MLPSpec K (L + 1 + (M + 1))) :
    C.Weights ≃ C.lowerLayers.Weights × C.upperLayers.Weights :=
  (Equiv.piCongrLeft _ finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)

/-- The lower part of split bias-free parameters consists of the first layers. -/
@[simp]
theorem splitWeights_apply_fst (C : MLPSpec K (L + 1 + (M + 1))) (w : C.Weights)
    (i : Fin (L + 1)) : (C.splitWeights w).1 i = w (Fin.castAdd (M + 1) i) := (rfl)

/-- The upper part of split bias-free parameters consists of the last layers. -/
@[simp]
theorem splitWeights_apply_snd (C : MLPSpec K (L + 1 + (M + 1))) (w : C.Weights)
    (i : Fin (M + 1)) : (C.splitWeights w).2 i = w (Fin.natAdd (L + 1) i) := (rfl)

/-- Joined bias-free parameters agree with the lower part on the first layers. -/
@[simp]
theorem splitWeights_symm_apply_castAdd (C : MLPSpec K (L + 1 + (M + 1)))
    (p : C.lowerLayers.Weights × C.upperLayers.Weights) (i : Fin (L + 1)) :
    C.splitWeights.symm p (Fin.castAdd (M + 1) i) = p.1 i :=
  congrFun (congrArg Prod.fst (C.splitWeights.apply_symm_apply p)) i

/-- Joined bias-free parameters agree with the upper part on the last layers. -/
@[simp]
theorem splitWeights_symm_apply_natAdd (C : MLPSpec K (L + 1 + (M + 1)))
    (p : C.lowerLayers.Weights × C.upperLayers.Weights) (i : Fin (M + 1)) :
    C.splitWeights.symm p (Fin.natAdd (L + 1) i) = p.2 i :=
  congrFun (congrArg Prod.snd (C.splitWeights.apply_symm_apply p)) i

/-- Splitting commutes with the zero-bias embedding. -/
@[simp]
theorem splitParameters_zeroBias [Zero K] (C : MLPSpec K (L + 1 + (M + 1))) (w : C.Weights) :
    C.splitParameters (C.zeroBias w) =
      (C.lowerLayers.zeroBias (C.splitWeights w).1, C.upperLayers.zeroBias (C.splitWeights w).2) :=
  Prod.ext
    (funext fun i =>
      (C.zeroBias_apply w _).trans (C.lowerLayers.zeroBias_apply (C.splitWeights w).1 i).symm)
    (funext fun i =>
      (C.zeroBias_apply w _).trans (C.upperLayers.zeroBias_apply (C.splitWeights w).2 i).symm)

/-! ### Realization of a split specification

The prefix types of a specification depend on the layer index, so indices of `C` and of its parts
that agree definitionally cannot be rewritten into each other. The proofs below therefore compose
the prefix recursions of `C` and of its parts with `Eq.trans`, which compares them up to
definitional equality. -/

section Evaluation

variable [NonUnitalNonAssocSemiring K]

/-- Below the junction, the prefixes of a specification are those of its lower part. -/
theorem evalPrefix_castAdd_castSucc (C : MLPSpec K (L + 1 + (M + 1))) (θ : C.Parameters)
    (x : Fin (C.width 0) → K) (i : Fin (L + 1)) :
    C.evalPrefix θ x (Fin.castAdd (M + 1) i).castSucc =
      C.lowerLayers.evalPrefix (C.splitParameters θ).1 x i.castSucc := by
  induction i using Fin.induction with
  | zero => exact (C.evalPrefix_zero θ x).trans (C.lowerLayers.evalPrefix_zero _ x).symm
  | succ i ih =>
    have h := C.evalPrefix_succ θ x (Fin.castAdd (M + 1) i.castSucc)
    rw [layerActivation_castAdd_castSucc, ih] at h
    exact h.trans (C.lowerLayers.evalPrefix_succ (C.splitParameters θ).1 x i.castSucc).symm

/-- At the junction, a specification applies the junction activation to the output of its lower
part. -/
theorem evalPrefix_natAdd_zero (C : MLPSpec K (L + 1 + (M + 1))) (θ : C.Parameters)
    (x : Fin (C.width 0) → K) :
    C.evalPrefix θ x (Fin.natAdd (L + 1) (0 : Fin (M + 2))) =
      fun k => C.junctionActivation (C.lowerLayers.realize (C.splitParameters θ).1 x k) := by
  have h := C.evalPrefix_succ θ x (Fin.castAdd (M + 1) (Fin.last L))
  rw [layerActivation_castAdd_last, evalPrefix_castAdd_castSucc] at h
  exact h.trans (congrArg (fun v k => C.junctionActivation (v k))
    (C.lowerLayers.realize_succ (C.splitParameters θ).1 x)).symm

/-- Above the junction, the prefixes of a specification are those of its upper part, fed with
the junction activation applied to the output of the lower part. -/
theorem evalPrefix_natAdd (C : MLPSpec K (L + 1 + (M + 1))) (θ : C.Parameters)
    (x : Fin (C.width 0) → K) (i : Fin (M + 2)) :
    C.evalPrefix θ x (Fin.natAdd (L + 1) i) =
      C.upperLayers.evalPrefix (C.splitParameters θ).2
        (fun k => C.junctionActivation (C.lowerLayers.realize (C.splitParameters θ).1 x k)) i := by
  induction i using Fin.induction with
  | zero => exact (C.evalPrefix_natAdd_zero θ x).trans (C.upperLayers.evalPrefix_zero _ _).symm
  | succ i ih =>
    -- `Fin.natAdd (L + 1) i.castSucc` and `(Fin.natAdd (L + 1) i).castSucc` agree
    -- definitionally; restate the inductive hypothesis at the index produced by the recursion.
    have ih' : C.evalPrefix θ x (Fin.natAdd (L + 1) i).castSucc = _ := ih
    have h := C.evalPrefix_succ θ x (Fin.natAdd (L + 1) i)
    rw [layerActivation_natAdd, ih'] at h
    exact h.trans (C.upperLayers.evalPrefix_succ (C.splitParameters θ).2 _ i).symm

/-- The realization of a specification of depth `(L + 1) + (M + 1)` is the realization of its
upper part applied, after the junction activation, to the realization of its lower part. -/
theorem realize_eq_upperLayers_realize (C : MLPSpec K (L + 1 + (M + 1))) (θ : C.Parameters)
    (x : Fin (C.width 0) → K) :
    C.realize θ x =
      C.upperLayers.realize (C.splitParameters θ).2
        (fun k => C.junctionActivation (C.lowerLayers.realize (C.splitParameters θ).1 x k)) :=
  ((C.realize_def θ x).trans (C.evalPrefix_natAdd θ x (Fin.last (M + 1)))).trans
    (C.upperLayers.realize_def _ _).symm

/-- On joined affine parameters, a specification realizes the composite of its parts, joined by
the junction activation. -/
theorem realize_splitParameters_symm (C : MLPSpec K (L + 1 + (M + 1)))
    (θ₁ : C.lowerLayers.Parameters) (θ₂ : C.upperLayers.Parameters) :
    C.realize (C.splitParameters.symm (θ₁, θ₂)) =
      C.upperLayers.realize θ₂ ∘ Pi.map (fun _ => C.junctionActivation) ∘
        C.lowerLayers.realize θ₁ := by
  funext x
  rw [realize_eq_upperLayers_realize]
  simp only [Equiv.apply_symm_apply]
  -- The two sides agree after unfolding `Function.comp` and `Pi.map`.
  rfl

/-- The bias-free realization of a specification of depth `(L + 1) + (M + 1)` is the bias-free
realization of its upper part applied, after the junction activation, to the bias-free
realization of its lower part. -/
theorem realizeWeights_eq_upperLayers_realizeWeights (C : MLPSpec K (L + 1 + (M + 1)))
    (w : C.Weights) (x : Fin (C.width 0) → K) :
    C.realizeWeights w x =
      C.upperLayers.realizeWeights (C.splitWeights w).2
        (fun k =>
          C.junctionActivation (C.lowerLayers.realizeWeights (C.splitWeights w).1 x k)) := by
  simpa [realizeWeights_def] using C.realize_eq_upperLayers_realize (C.zeroBias w) x

/-- On joined bias-free parameters, a specification realizes the composite of its parts, joined
by the junction activation. -/
theorem realizeWeights_splitWeights_symm (C : MLPSpec K (L + 1 + (M + 1)))
    (w₁ : C.lowerLayers.Weights) (w₂ : C.upperLayers.Weights) :
    C.realizeWeights (C.splitWeights.symm (w₁, w₂)) =
      C.upperLayers.realizeWeights w₂ ∘ Pi.map (fun _ => C.junctionActivation) ∘
        C.lowerLayers.realizeWeights w₁ := by
  funext x
  rw [realizeWeights_eq_upperLayers_realizeWeights]
  simp only [Equiv.apply_symm_apply]
  -- The two sides agree after unfolding `Function.comp` and `Pi.map`.
  rfl

/-- The functions realized by a specification of depth `(L + 1) + (M + 1)` are the composites of
functions realized by its parts, joined by the junction activation. -/
theorem realizedFunctions_realize (C : MLPSpec K (L + 1 + (M + 1))) :
    realizedFunctions C.realize =
      Set.image2 (fun f g => g ∘ Pi.map (fun _ => C.junctionActivation) ∘ f)
        (realizedFunctions C.lowerLayers.realize) (realizedFunctions C.upperLayers.realize) :=
  (realizedFunctions_def _).trans <| (C.splitParameters.symm.surjective.range_comp _).symm.trans <|
    (congrArg Set.range (funext fun p : _ × _ => C.realize_splitParameters_symm p.1 p.2)).trans <|
      (Set.image2_range (fun f g => g ∘ Pi.map (fun _ => C.junctionActivation) ∘ f)
        C.lowerLayers.realize C.upperLayers.realize).symm.trans <|
        congrArg₂ (Set.image2 _) (realizedFunctions_def _).symm (realizedFunctions_def _).symm

/-- The functions realized by a specification of depth `(L + 1) + (M + 1)` on bias-free
parameters are the composites of functions realized by its parts on bias-free parameters, joined
by the junction activation. -/
theorem realizedFunctions_realizeWeights (C : MLPSpec K (L + 1 + (M + 1))) :
    realizedFunctions C.realizeWeights =
      Set.image2 (fun f g => g ∘ Pi.map (fun _ => C.junctionActivation) ∘ f)
        (realizedFunctions C.lowerLayers.realizeWeights)
        (realizedFunctions C.upperLayers.realizeWeights) :=
  (realizedFunctions_def _).trans <| (C.splitWeights.symm.surjective.range_comp _).symm.trans <|
    (congrArg Set.range
      (funext fun p : _ × _ => C.realizeWeights_splitWeights_symm p.1 p.2)).trans <|
      (Set.image2_range (fun f g => g ∘ Pi.map (fun _ => C.junctionActivation) ∘ f)
        C.lowerLayers.realizeWeights C.upperLayers.realizeWeights).symm.trans <|
        congrArg₂ (Set.image2 _) (realizedFunctions_def _).symm (realizedFunctions_def _).symm

end Evaluation

/-! ### Concatenation -/

/-- The concatenation of MLP specifications `A` and `B` of positive depths, joined by the
activation `σ`: its layers are those of `A` followed by those of `B`, the output layer of `A`
becoming the hidden layer with activation `σ` and the input layer of `B`. The width of that layer
is the input width of `B`; it agrees with `A` when the output width of `A` is the input width of
`B`. -/
def append (A : MLPSpec K (L + 1)) (B : MLPSpec K (M + 1)) (σ : K → K) :
    MLPSpec K (L + 1 + (M + 1)) where
  width := (Fin.append (Fin.init A.width) B.width : Fin (L + 1 + (M + 2)) → ℕ)
  activation := Fin.append (Fin.snoc (α := fun _ => K → K) (A.activation : Fin L → K → K) σ)
    B.activation

/-- The upper part of a concatenation is its second factor. -/
@[simp]
theorem upperLayers_append (A : MLPSpec K (L + 1)) (B : MLPSpec K (M + 1)) (σ : K → K) :
    (A.append B σ).upperLayers = B :=
  MLPSpec.ext (funext fun i => Fin.append_right (Fin.init A.width) B.width i)
    (funext fun j => Fin.append_right (Fin.snoc (α := fun _ => K → K) A.activation σ)
      B.activation j)

/-- The junction activation of a concatenation is the activation joining its factors. -/
@[simp]
theorem junctionActivation_append (A : MLPSpec K (L + 1)) (B : MLPSpec K (M + 1)) (σ : K → K) :
    (A.append B σ).junctionActivation = σ :=
  (Fin.append_left _ _ _).trans (Fin.snoc_last (α := fun _ => K → K) _ _)

/-- The lower part of a concatenation is its first factor, when the output width of the first
factor is the input width of the second. -/
theorem lowerLayers_append (A : MLPSpec K (L + 1)) (B : MLPSpec K (M + 1)) (σ : K → K)
    (h : A.width (Fin.last (L + 1)) = B.width 0) : (A.append B σ).lowerLayers = A := by
  refine MLPSpec.ext (funext fun i => ?_) (funext fun j => ?_)
  · induction i using Fin.lastCases with
    | last => exact (Fin.append_right (Fin.init A.width) B.width (0 : Fin (M + 2))).trans h.symm
    | cast j => exact Fin.append_left (Fin.init A.width) B.width j
  · exact (Fin.append_left (Fin.snoc (α := fun _ => K → K) A.activation σ) B.activation
      j.castSucc).trans (Fin.snoc_castSucc (α := fun _ => K → K) _ _ _)

/-- Every specification of depth `(L + 1) + (M + 1)` is the concatenation of its lower and upper
parts, joined by its junction activation. -/
@[simp]
theorem append_lowerLayers_upperLayers (C : MLPSpec K (L + 1 + (M + 1))) :
    C.lowerLayers.append C.upperLayers C.junctionActivation = C := by
  have h : Fin.snoc (α := fun _ => K → K) C.lowerLayers.activation C.junctionActivation =
      fun j => C.activation (Fin.castAdd M j) :=
    Fin.snoc_init_self (α := fun _ => K → K) (q := fun j => C.activation (Fin.castAdd M j))
  refine MLPSpec.ext (Fin.append_castAdd_natAdd (m := L + 1) (n := M + 2) (f := C.width)) ?_
  exact (congrArg (Fin.append · C.upperLayers.activation) h).trans
    (Fin.append_castAdd_natAdd (m := L + 1) (n := M) (f := C.activation))

end MLPSpec

end TauCeti.Neuromanifold
