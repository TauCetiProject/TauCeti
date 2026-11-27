/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Activation
public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import TauCeti.Topology.PL.PiecewiseAffine
import Mathlib.Data.Fin.VecNotation

/-!
# ReLU multilayer perceptrons and continuous piecewise-linear functions

A ReLU network of depth `L` with widths `d : Fin (L + 1) → ℕ` is the `Neuromanifold.MLPSpec`
`TauCeti.reluSpec d` whose every hidden activation is the scalar rectifier `t ↦ max 0 t` (the
scalar function of `TauCeti.Neuromanifold.reluActivation`), with an affine output layer.
The predicates `TauCeti.ReLUNetRealizes d f` (for `ℝⁿ → ℝᵐ`) and
`TauCeti.ReLUNetComputes d f` (for `ℝⁿ → ℝ`) assert that the input and output widths match
and some parameters realize `f`.

This file builds the structural calculus for ReLU networks of positive depth and connects them to
piecewise-affine maps:

* **Composition** (`ReLUNetRealizes.comp`, `ReLUNetComputes.comp`): merging the affine output
  layer of a depth-`(L₁ + 1)` network with the affine input layer of a depth-`(L₂ + 1)` network
  yields a depth-`(L₁ + L₂ + 1)` network realizing the composite with widths `compWidths`.
* **Parallel stacking and linear combinations** (`ReLUNetRealizes.finAppend`,
  `ReLUNetComputes.linearComb`): placing two networks of the same positive depth side by side adds
  their hidden widths; composing with an affine output layer gives arbitrary affine combinations
  `a * f₁ x + b * f₂ x + c`.
* **Affine layers and depth padding** (`ReLUNetRealizes.of_continuousAffineMap`,
  `ReLUNetRealizes.pad`, `ReLUNetComputes.pad`): continuous affine maps are realized at depth `1`
  and at every positive depth by appending two-unit hidden layers via `t = max 0 t - max 0 (-t)`.
* **Piecewise affineness** (`isPiecewiseAffineOn_of_reluNetRealizes`,
  `isPiecewiseAffineOn_of_reluNetComputes`): every prefix evaluation and hence every function
  computed by a ReLU network is globally piecewise affine in the sense of
  `TauCeti.IsPiecewiseAffineOn`.

## References

* Raman Arora, Amitabh Basu, Poorya Mianjy, and Anirbit Mukherjee, *Understanding deep neural
  networks with rectified linear units*, ICLR 2018;
  [arXiv:1611.01491v6](https://arxiv.org/abs/1611.01491v6), Theorem 2.1 and Appendix D.
* Christoph Hertrich, Amitabh Basu, Marco Di Summa, and Martin Skutella, *Towards lower bounds on
  the depth of ReLU neural networks*, Discrete & Computational Geometry (2024);
  [arXiv:2105.14835v5](https://arxiv.org/abs/2105.14835v5), §2 and Figure 1.
-/

public section

open Matrix Set

namespace TauCeti.Neuromanifold.MLPSpec

/-- If layer `k` of an MLP specification has width zero, every prefix evaluation at layer `k` or
above is constant in the input `x`. -/
theorem evalPrefix_eq_of_width_eq_zero {K : Type*} [NonUnitalNonAssocSemiring K] {L : ℕ}
    (A : MLPSpec K L) (θ : A.Parameters) {k : Fin (L + 1)} (hk : A.width k = 0)
    (x x' : Fin (A.width 0) → K) {i : Fin (L + 1)} (hi : k ≤ i) :
    A.evalPrefix θ x i = A.evalPrefix θ x' i := by
  have hk_eq : A.evalPrefix θ x k = A.evalPrefix θ x' k := by
    funext j
    exact Fin.elim0 (j.cast hk)
  exact A.evalPrefix_congr_of_le hk_eq (fun _ _ => rfl) hi

/-- If any layer of an MLP specification has width zero, its realization is constant in the
input. -/
theorem realize_eq_of_width_eq_zero {K : Type*} [NonUnitalNonAssocSemiring K] {L : ℕ}
    (A : MLPSpec K L) (θ : A.Parameters) {k : Fin (L + 1)} (hk : A.width k = 0)
    (x x' : Fin (A.width 0) → K) :
    A.realize θ x = A.realize θ x' :=
  (A.realize_def θ x).trans
    ((A.evalPrefix_eq_of_width_eq_zero θ hk x x' (Fin.le_last k)).trans
      (A.realize_def θ x').symm)

end TauCeti.Neuromanifold.MLPSpec

namespace TauCeti

open Neuromanifold

private theorem evalPrefix_succ_apply {K : Type*} [NonUnitalNonAssocSemiring K] {L : ℕ}
    (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K) (i : Fin L)
    (j : Fin (A.width i.succ)) :
    A.evalPrefix θ x i.succ j =
      A.layerActivation i (((θ i).1 *ᵥ A.evalPrefix θ x i.castSucc) j + (θ i).2 j) :=
  congrFun (A.evalPrefix_succ θ x i) j

private theorem evalPrefix_cast {K : Type*} [NonUnitalNonAssocSemiring K] {L : ℕ}
    (A : MLPSpec K L) (θ : A.Parameters) (x : Fin (A.width 0) → K) {i j : Fin (L + 1)}
    (hij : i = j) (r : Fin (A.width i)) :
    A.evalPrefix θ x i r = A.evalPrefix θ x j (Fin.cast (congrArg A.width hij) r) := by
  subst hij
  rfl

private theorem evalPrefix_castSucc_zero {K : Type*} [NonUnitalNonAssocSemiring K] {L : ℕ}
    (A : MLPSpec K (L + 1)) (θ : A.Parameters) (x : Fin (A.width 0) → K) :
    A.evalPrefix θ x (0 : Fin (L + 1)).castSucc = x :=
  A.evalPrefix_zero θ x

/-! ### ReLU MLP specification and realization predicates -/

/-- The ReLU multilayer perceptron specification with widths `d 0, …, d L`: every hidden layer
applies `t ↦ max 0 t` coordinatewise, matching `TauCeti.Neuromanifold.reluActivation`, and the
output layer is affine. -/
@[expose] def reluSpec {L : ℕ} (d : Fin (L + 1) → ℕ) : MLPSpec ℝ L where
  width := d
  activation _ t := max 0 t

/-- The widths of `reluSpec d` are `d`. -/
@[simp]
theorem reluSpec_width {L : ℕ} (d : Fin (L + 1) → ℕ) : (reluSpec d).width = d := (rfl)

/-- Every hidden activation of `reluSpec d` is the scalar rectifier `t ↦ max 0 t`. -/
@[simp]
theorem reluSpec_activation {L : ℕ} (d : Fin (L + 1) → ℕ) (j : Fin (L - 1)) (t : ℝ) :
    (reluSpec d).activation j t = max 0 t := (rfl)

/-- In positive depth `L + 1`, hidden layer `i + 1` of `reluSpec d` applies `t ↦ max 0 t`. -/
@[simp]
theorem layerActivation_reluSpec_castSucc {L : ℕ} (d : Fin (L + 2) → ℕ) (i : Fin L)
    (t : ℝ) :
    (reluSpec d).layerActivation i.castSucc t = max 0 t := by
  simp [MLPSpec.layerActivation_castSucc]

/-- Dropping layer `0` of `reluSpec d` yields `reluSpec (Fin.tail d)`. -/
@[simp]
theorem tail_reluSpec {L : ℕ} (d : Fin (L + 2) → ℕ) :
    (reluSpec d).tail = reluSpec (Fin.tail d) := by
  ext <;> simp [Fin.tail, MLPSpec.tail_activation]

/-- The ReLU network with widths `d` realizes `f : (Fin n → ℝ) → (Fin m → ℝ)`: its input
width is `n`, its output width is `m`, and for some parameters its realization agrees with `f`. -/
def ReLUNetRealizes {n m L : ℕ} (d : Fin (L + 1) → ℕ)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∃ (h0 : d 0 = n) (hL : d (Fin.last L) = m) (θ : (reluSpec d).Parameters),
    ∀ x j, (reluSpec d).realize θ (fun i => x (Fin.cast h0 i)) (Fin.cast hL.symm j) = f x j

/-- The ReLU network with widths `d` computes `f : (Fin n → ℝ) → ℝ`: its input width is `n`,
its output width is `1`, and for some parameters its realization agrees with `f` everywhere. -/
def ReLUNetComputes {n L : ℕ} (d : Fin (L + 1) → ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (h0 : d 0 = n) (hL : d (Fin.last L) = 1) (θ : (reluSpec d).Parameters),
    ∀ x, (reluSpec d).realize θ (fun i => x (Fin.cast h0 i)) (Fin.cast hL.symm 0) = f x

/-- Scalar computation by a ReLU network is realization of the one-coordinate vector map. -/
theorem reluNetComputes_iff_reluNetRealizes {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} :
    ReLUNetComputes d f ↔ ReLUNetRealizes d (fun x (_ : Fin 1) => f x) := by
  simp only [ReLUNetComputes, ReLUNetRealizes, Fin.forall_fin_one]

/-- A network realizing a map into `Fin m → ℝ` has input width `n`. -/
theorem ReLUNetRealizes.width_zero {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) : d 0 = n :=
  hf.choose

/-- A network realizing a map into `Fin m → ℝ` has output width `m`. -/
theorem ReLUNetRealizes.width_last {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) : d (Fin.last L) = m :=
  hf.choose_spec.choose

/-- A network computing a scalar function on `Fin n → ℝ` has input width `n`. -/
theorem ReLUNetComputes.width_zero {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) : d 0 = n :=
  hf.choose

/-- A network computing a scalar function has output width `1`. -/
theorem ReLUNetComputes.width_last {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) : d (Fin.last L) = 1 :=
  hf.choose_spec.choose

/-- Transporting `ReLUNetRealizes` along equal width functions. -/
theorem ReLUNetRealizes.of_width_eq {n m L : ℕ} {d d' : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) (hd : d = d') :
    ReLUNetRealizes d' f :=
  hd ▸ hf

/-- Transporting `ReLUNetComputes` along equal width functions. -/
theorem ReLUNetComputes.of_width_eq {n L : ℕ} {d d' : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) (hd : d = d') :
    ReLUNetComputes d' f :=
  hd ▸ hf

/-- The hidden layers of a network of depth `L`: the indices other than the input `0` and the
output `Fin.last L`. -/
def hiddenLayers (L : ℕ) : Finset (Fin (L + 1)) :=
  Finset.univ.filter fun i => i ≠ 0 ∧ i ≠ Fin.last L

/-- Membership in `hiddenLayers L` means being neither the input layer nor the output layer. -/
@[simp]
theorem mem_hiddenLayers_iff {L : ℕ} {i : Fin (L + 1)} :
    i ∈ hiddenLayers L ↔ i ≠ 0 ∧ i ≠ Fin.last L := by
  simp [hiddenLayers]

/-- Membership in `hiddenLayers L` in terms of natural-number indices: `0 < i.val < L`. -/
theorem mem_hiddenLayers_iff_lt {L : ℕ} {i : Fin (L + 1)} :
    i ∈ hiddenLayers L ↔ 0 < i.val ∧ i.val < L := by
  simp only [mem_hiddenLayers_iff, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  omega

/-- A depth-zero network has no hidden layers. -/
@[simp]
theorem hiddenLayers_zero : hiddenLayers 0 = ∅ := by
  ext i
  simp [Fin.eq_zero i]

/-- A depth-one network has no hidden layers. -/
@[simp]
theorem hiddenLayers_one : hiddenLayers 1 = ∅ := by
  ext i
  fin_cases i <;> simp

/-- A network of depth `L` has `L - 1` hidden layers. -/
@[simp]
theorem card_hiddenLayers (L : ℕ) : (hiddenLayers L).card = L - 1 := by
  let e : Fin (L - 1) ≃ hiddenLayers L :=
    { toFun := fun j =>
        have hj : j.val + 1 < L := Nat.add_lt_of_lt_sub j.isLt
        ⟨⟨j.val + 1, Nat.lt_succ_of_lt hj⟩,
          mem_hiddenLayers_iff_lt.mpr ⟨Nat.succ_pos _, hj⟩⟩
      invFun := fun i => ⟨i.val.val - 1, by
        have hi := mem_hiddenLayers_iff_lt.mp i.property
        omega⟩
      left_inv := fun j => Fin.ext (by simp)
      right_inv := fun i => by
        have hi := mem_hiddenLayers_iff_lt.mp i.property
        exact Subtype.ext (Fin.ext (by simp; omega)) }
  simpa only [Fintype.card_fin] using (Fintype.card_coe (hiddenLayers L)).symm.trans
    (Fintype.card_congr e).symm

/-! ### Composition -/

/-- The width tuple obtained by merging the output affine layer of a depth-`(L₁ + 1)` network
with the input affine layer of a depth-`(L₂ + 1)` network, producing depth `L₁ + L₂ + 1`. -/
def compWidths {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ) (d₂ : Fin (L₂ + 2) → ℕ) :
    Fin (L₁ + L₂ + 2) → ℕ :=
  fun i =>
    if _ : i.val ≤ L₁ then d₁ ⟨i.val, by omega⟩ else d₂ ⟨i.val - L₁, by omega⟩

/-- Below the merge index `L₁`, `compWidths` agrees with the first network's widths. -/
@[simp]
theorem compWidths_of_le {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₁ + 1)) :
    compWidths d₁ d₂ ⟨i.val, by omega⟩ = d₁ i.castSucc := by
  have hi : i.val ≤ L₁ := Nat.le_of_lt_succ i.isLt
  simp only [compWidths, hi, ↓reduceDIte]
  exact congrArg d₁ (Fin.ext rfl)

/-- Above the merge index `L₁`, `compWidths` agrees with the positive-index widths of the second
network. -/
@[simp]
theorem compWidths_of_gt {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₂ + 1)) :
    compWidths d₁ d₂ ⟨L₁ + 1 + i.val, by omega⟩ = d₂ i.succ := by
  have hi : ¬ (L₁ + 1 + i.val ≤ L₁) := by omega
  simp only [compWidths, hi, ↓reduceDIte]
  exact congrArg d₂ (Fin.ext (by simp; omega))

/-- The input width of `compWidths d₁ d₂` is `d₁ 0`. -/
@[simp]
theorem compWidths_zero {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) :
    compWidths d₁ d₂ 0 = d₁ 0 :=
  compWidths_of_le d₁ d₂ 0

/-- The output width of `compWidths d₁ d₂` is `d₂ (Fin.last (L₂ + 1))`. -/
@[simp]
theorem compWidths_last {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) :
    compWidths d₁ d₂ (Fin.last (L₁ + L₂ + 1)) = d₂ (Fin.last (L₂ + 1)) := by
  rw [show Fin.last (L₁ + L₂ + 1) = ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ from
    Fin.ext (by simp; omega)]
  exact compWidths_of_gt d₁ d₂ (Fin.last L₂)

private theorem width_compWidths_of_le {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} {j : Fin (L₁ + 2)}
    (hi : i.val ≤ L₁) (hij : i.val = j.val) :
    (reluSpec (compWidths d₁ d₂)).width i = (reluSpec d₁).width j := by
  simp only [reluSpec_width, compWidths, hi, ↓reduceDIte]
  exact congrArg d₁ (Fin.ext hij)

private theorem width_compWidths_of_gt {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} {j : Fin (L₂ + 2)}
    (hi : L₁ < i.val) (hij : i.val - L₁ = j.val) :
    (reluSpec (compWidths d₁ d₂)).width i = (reluSpec d₂).width j := by
  have hnot : ¬ i.val ≤ L₁ := Nat.not_le_of_lt hi
  simp only [reluSpec_width, compWidths, hnot, ↓reduceDIte]
  exact congrArg d₂ (Fin.ext hij)

private def compParams {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : d₁ (Fin.last (L₁ + 1)) = m) (hm₂ : d₂ 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (reluSpec (compWidths d₁ d₂)).Parameters := fun i =>
  if hi : i.val < L₁ then
    let k : Fin L₁ := ⟨i.val, hi⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ =
        (reluSpec d₁).width k.castSucc.succ :=
      width_compWidths_of_le d₁ d₂ (by simp; omega) (by simp [k])
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp; omega) (by simp [k])
    (fun r c => (θ₁ k.castSucc).1 (Fin.cast hr r) (Fin.cast hc c),
     fun r => (θ₁ k.castSucc).2 (Fin.cast hr r))
  else if heq : i.val = L₁ then
    let W₁ := (θ₁ (Fin.last L₁)).1
    let b₁ := (θ₁ (Fin.last L₁)).2
    let W₂ := (θ₂ 0).1
    let b₂ := (θ₂ 0).2
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ =
        (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ :=
      width_compWidths_of_gt d₁ d₂ (by simp; omega) (by simp [heq])
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width (Fin.last L₁).castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp; omega) (by simp [heq])
    (fun r c => ∑ k : Fin m,
        W₂ (Fin.cast hr r) (Fin.cast hm₂.symm k) * W₁ (Fin.cast hm₁.symm k) (Fin.cast hc c),
     fun r => (∑ k : Fin m, W₂ (Fin.cast hr r) (Fin.cast hm₂.symm k) *
        b₁ (Fin.cast hm₁.symm k)) + b₂ (Fin.cast hr r))
  else
    let k : Fin L₂ := ⟨i.val - (L₁ + 1), by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k.succ.succ :=
      width_compWidths_of_gt d₁ d₂ (by simp; omega) (by simp [k]; omega)
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_gt d₁ d₂ (by simp; omega) (by simp [k]; omega)
    (fun r c => (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c),
     fun r => (θ₂ k.succ).2 (Fin.cast hr r))

private theorem compParams_lt {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : d₁ (Fin.last (L₁ + 1)) = m) (hm₂ : d₂ 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L₁) :
    let i : Fin (L₁ + L₂ + 1) := ⟨k.val, by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ =
        (reluSpec d₁).width k.castSucc.succ :=
      width_compWidths_of_le d₁ d₂ (by dsimp [i]; omega) (by dsimp [i])
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.castSucc :=
      width_compWidths_of_le d₁ d₂ (by dsimp [i]; omega) (by dsimp [i])
    (∀ r c, (compParams hm₁ hm₂ θ₁ θ₂ i).1 r c =
        (θ₁ k.castSucc).1 (Fin.cast hr r) (Fin.cast hc c)) ∧
      (∀ r, (compParams hm₁ hm₂ θ₁ θ₂ i).2 r =
        (θ₁ k.castSucc).2 (Fin.cast hr r)) := by
  intro i hr hc
  have hi : i.val < L₁ := k.isLt
  simp [compParams, hi, i]

private theorem compParams_eq {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : d₁ (Fin.last (L₁ + 1)) = m) (hm₂ : d₂ 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (hr : (reluSpec (compWidths d₁ d₂)).width
        (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).succ =
        (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ)
    (hc : (reluSpec (compWidths d₁ d₂)).width
        (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).castSucc =
        (reluSpec d₁).width (Fin.last L₁).castSucc) :
    (∀ r c, (compParams hm₁ hm₂ θ₁ θ₂ ⟨L₁, by omega⟩).1 r c = ∑ k : Fin m,
        (θ₂ 0).1 (Fin.cast hr r) (Fin.cast hm₂.symm k) *
          (θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc c)) ∧
      (∀ r, (compParams hm₁ hm₂ θ₁ θ₂ ⟨L₁, by omega⟩).2 r = (∑ k : Fin m,
        (θ₂ 0).1 (Fin.cast hr r) (Fin.cast hm₂.symm k) *
          (θ₁ (Fin.last L₁)).2 (Fin.cast hm₁.symm k)) + (θ₂ 0).2 (Fin.cast hr r)) := by
  simp [compParams]

private theorem compParams_gt {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : d₁ (Fin.last (L₁ + 1)) = m) (hm₂ : d₂ 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L₂) :
    let i : Fin (L₁ + L₂ + 1) := ⟨L₁ + 1 + k.val, by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k.succ.succ :=
      width_compWidths_of_gt d₁ d₂ (by dsimp [i]; omega) (by dsimp [i]; omega)
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_gt d₁ d₂ (by dsimp [i]; omega) (by dsimp [i]; omega)
    (∀ r c, (compParams hm₁ hm₂ θ₁ θ₂ i).1 r c =
        (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c)) ∧
      (∀ r, (compParams hm₁ hm₂ θ₁ θ₂ i).2 r = (θ₂ k.succ).2 (Fin.cast hr r)) := by
  intro i hr hc
  have hi : ¬ (i.val < L₁) := by dsimp [i]; omega
  have heq : i.val ≠ L₁ := by dsimp [i]; omega
  have hfn : ∀ (k' : Fin L₂) (_ : k' = k)
      (hr' : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k'.succ.succ)
      (hc' : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k'.succ.castSucc),
      (∀ r c, (θ₂ k'.succ).1 (Fin.cast hr' r) (Fin.cast hc' c) =
          (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c)) ∧
        (∀ r, (θ₂ k'.succ).2 (Fin.cast hr' r) = (θ₂ k.succ).2 (Fin.cast hr r)) := by
    rintro _ rfl _ _
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  simp only [compParams, hi, ↓reduceDIte, heq]
  exact hfn ⟨i.val - (L₁ + 1), by dsimp [i]; omega⟩ (Fin.ext (by dsimp [i]; omega)) _ _

/-- Merging the affine output layer of a depth-`(L₁ + 1)` network realizing `g` with the affine
input layer of a depth-`(L₂ + 1)` network realizing `h` gives a depth-`(L₁ + L₂ + 1)` network
realizing `h ∘ g`. -/
theorem ReLUNetRealizes.comp {n m p L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → (Fin p → ℝ)}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetRealizes d₂ h) :
    ReLUNetRealizes (compWidths d₁ d₂) (h ∘ g) := by
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := hg
  obtain ⟨hm₂, hp₂, θ₂, hθ₂⟩ := hh
  have hm₂' : (reluSpec d₂).width 0 = m := hm₂
  let θ := compParams hm₁ hm₂ θ₁ θ₂
  refine ⟨by simp [h0₁], by simp [hp₂], θ, fun x j => ?_⟩
  let x₀ : Fin ((reluSpec (compWidths d₁ d₂)).width 0) → ℝ :=
    fun i => x (Fin.cast (by simp [h0₁]) i)
  let x₁ : Fin ((reluSpec d₁).width 0) → ℝ := fun i => x (Fin.cast h0₁ i)
  have hprefix₁ : ∀ (k : Fin (L₁ + 1))
      (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨k.val, by omega⟩)),
      (reluSpec (compWidths d₁ d₂)).evalPrefix θ x₀ ⟨k.val, by omega⟩ r =
        (reluSpec d₁).evalPrefix θ₁ x₁ k.castSucc
          (Fin.cast (width_compWidths_of_le d₁ d₂ (Nat.le_of_lt_succ k.isLt) rfl) r) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro r
      have h0_idx : (⟨(0 : Fin (L₁ + 1)).val, by omega⟩ : Fin (L₁ + L₂ + 2)) = 0 := rfl
      have h0_idx₁ : (0 : Fin (L₁ + 1)).castSucc = 0 := rfl
      rw [evalPrefix_cast _ _ _ h0_idx, MLPSpec.evalPrefix_zero,
        evalPrefix_cast (reluSpec d₁) _ _ h0_idx₁, MLPSpec.evalPrefix_zero]
      rfl
    | succ k ih =>
      intro r
      let i : Fin (L₁ + L₂ + 1) := ⟨k.val, by omega⟩
      have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i =
          (reluSpec d₁).layerActivation k.castSucc := by
        rw [(reluSpec (compWidths d₁ d₂)).layerActivation_of_lt i (by simp [i]; omega),
          (reluSpec d₁).layerActivation_castSucc]
        rfl
      have hsucc : (⟨k.succ.val, by omega⟩ : Fin (L₁ + L₂ + 2)) = i.succ := Fin.ext rfl
      have hsucc₁ : k.succ.castSucc = k.castSucc.succ := rfl
      rw [evalPrefix_cast _ _ _ hsucc, evalPrefix_succ_apply, hlayer,
        evalPrefix_cast (reluSpec d₁) _ _ hsucc₁, evalPrefix_succ_apply]
      apply congrArg ((reluSpec d₁).layerActivation k.castSucc)
      obtain ⟨hW, hb⟩ := compParams_lt hm₁ hm₂ θ₁ θ₂ k
      dsimp only [θ, i]
      simp only [Matrix.mulVec, dotProduct, hW, hb]
      congr 1
      let hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
          (reluSpec d₁).width k.castSucc.castSucc :=
        width_compWidths_of_le d₁ d₂ (by simp [i]) rfl
      refine Fintype.sum_equiv (finCongr hc) _ _ fun c => ?_
      simp only [finCongr_apply]
      congr 1
      exact ih c
  have hmid : ∀ r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1, by omega⟩),
      (reluSpec (compWidths d₁ d₂)).evalPrefix θ x₀ ⟨L₁ + 1, by omega⟩ r =
        (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂' u)) 1
          (Fin.cast (width_compWidths_of_gt d₁ d₂ (by simp) (by simp)) r) := by
    intro r
    let i_mid : Fin (L₁ + L₂ + 1) := ⟨L₁, by omega⟩
    have hsucc_mid : (⟨L₁ + 1, by omega⟩ : Fin (L₁ + L₂ + 2)) = i_mid.succ := Fin.ext rfl
    have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i_mid =
        (reluSpec d₂).layerActivation 0 := by
      by_cases hL₂ : L₂ = 0
      · subst hL₂
        rw [(reluSpec (compWidths d₁ d₂)).layerActivation_of_val_add_one_eq i_mid
            (by simp [i_mid]),
          (reluSpec d₂).layerActivation_of_val_add_one_eq 0 rfl]
      · rw [(reluSpec (compWidths d₁ d₂)).layerActivation_of_lt i_mid (by simp [i_mid]; omega),
          (reluSpec d₂).layerActivation_of_lt 0 (by simp; omega)]
        rfl
    have h1_succ : (1 : Fin (L₂ + 2)) = (0 : Fin (L₂ + 1)).succ := rfl
    rw [evalPrefix_cast _ _ _ hsucc_mid, evalPrefix_succ_apply, hlayer,
      evalPrefix_cast (reluSpec d₂) _ _ h1_succ, evalPrefix_succ_apply,
      evalPrefix_castSucc_zero]
    apply congrArg ((reluSpec d₂).layerActivation 0)
    have hr_mid :
        (reluSpec (compWidths d₁ d₂)).width
            (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).succ =
          (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ :=
      width_compWidths_of_gt d₁ d₂ (by simp) (by simp)
    have hc_mid :
        (reluSpec (compWidths d₁ d₂)).width
            (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).castSucc =
          (reluSpec d₁).width (Fin.last L₁).castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp) (by simp)
    obtain ⟨hW, hb⟩ := compParams_eq hm₁ hm₂ θ₁ θ₂ hr_mid hc_mid
    dsimp only [θ, i_mid]
    simp only [Matrix.mulVec, dotProduct, hW, hb]
    rw [← add_assoc]
    congr 1
    have hlhs_swap :
        (∑ c : Fin ((reluSpec (compWidths d₁ d₂)).width (⟨L₁, by omega⟩ :
              Fin (L₁ + L₂ + 1)).castSucc),
            (∑ k : Fin m, (θ₂ 0).1
                (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r)) (Fin.cast hm₂.symm k) *
                (θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc_mid c)) *
              (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂) x₀
                (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).castSucc c) =
          ∑ k : Fin m, ∑ c : Fin ((reluSpec (compWidths d₁ d₂)).width
              (⟨L₁, by omega⟩ : Fin (L₁ + L₂ + 1)).castSucc),
            (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r))
                (Fin.cast hm₂.symm k) *
              ((θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc_mid c) *
                (reluSpec d₁).evalPrefix θ₁ x₁ (Fin.last L₁).castSucc
                  (Fin.cast hc_mid c)) := by
      refine (Finset.sum_congr rfl fun c _ => ?_).trans Finset.sum_comm
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc := hprefix₁ (Fin.last L₁) c
      rw [mul_assoc]
      congr 2
    rw [hlhs_swap, ← Finset.sum_add_distrib]
    have hsum_k : ∀ k : Fin m,
        (∑ c : Fin ((reluSpec (compWidths d₁ d₂)).width (⟨L₁, by omega⟩ :
              Fin (L₁ + L₂ + 1)).castSucc),
            (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r))
                (Fin.cast hm₂.symm k) *
              ((θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc_mid c) *
                (reluSpec d₁).evalPrefix θ₁ x₁ (Fin.last L₁).castSucc
                  (Fin.cast hc_mid c))) +
          (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r))
              (Fin.cast hm₂.symm k) *
            (θ₁ (Fin.last L₁)).2 (Fin.cast hm₁.symm k) =
        (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r)) (Fin.cast hm₂.symm k) *
          g x k := by
      intro k
      rw [← Finset.mul_sum, ← mul_add]
      congr 1
      have hk := hθ₁ x k
      change (reluSpec d₁).realize θ₁ x₁ (Fin.cast hm₁.symm k) = g x k at hk
      rw [MLPSpec.realize_succ] at hk
      rw [← hk]
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
      congr 1
      refine Fintype.sum_equiv (finCongr hc_mid) _ _ fun c => ?_
      simp [finCongr_apply]
    refine (Finset.sum_congr rfl fun k _ => hsum_k k).trans ?_
    refine Fintype.sum_equiv (finCongr hm₂'.symm) _ _ fun k => ?_
    simp [finCongr_apply]
  have hprefix₂ : ∀ (k : Fin (L₂ + 1))
      (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1 + k.val, by omega⟩)),
      (reluSpec (compWidths d₁ d₂)).evalPrefix θ x₀ ⟨L₁ + 1 + k.val, by omega⟩ r =
        (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂' u)) k.succ
          (Fin.cast (width_compWidths_of_gt d₁ d₂ (by simp; omega) (by simp; omega)) r) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro r
      exact hmid r
    | succ k ih =>
      intro r
      let i : Fin (L₁ + L₂ + 1) := ⟨L₁ + 1 + k.val, by omega⟩
      have hsucc : (⟨L₁ + 1 + k.succ.val, by omega⟩ : Fin (L₁ + L₂ + 2)) = i.succ :=
        Fin.ext (by simp [i]; omega)
      have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i =
          (reluSpec d₂).layerActivation k.succ := by
        by_cases hlt : k.val + 1 < L₂
        · rw [(reluSpec (compWidths d₁ d₂)).layerActivation_of_lt i (by simp [i]; omega),
            (reluSpec d₂).layerActivation_of_lt k.succ (by simp; omega)]
          rfl
        · rw [(reluSpec (compWidths d₁ d₂)).layerActivation_of_val_add_one_eq i
              (by simp [i]; omega),
            (reluSpec d₂).layerActivation_of_val_add_one_eq k.succ (by simp; omega)]
      rw [evalPrefix_cast _ _ _ hsucc, evalPrefix_succ_apply, hlayer, evalPrefix_succ_apply]
      apply congrArg ((reluSpec d₂).layerActivation k.succ)
      obtain ⟨hW, hb⟩ := compParams_gt hm₁ hm₂ θ₁ θ₂ k
      dsimp only [θ, i]
      simp only [Matrix.mulVec, dotProduct, hW, hb]
      congr 1
      have hcast_c : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
          (reluSpec d₂).width k.succ.castSucc :=
        width_compWidths_of_gt d₁ d₂ (by simp [i]; omega) (by simp [i]; omega)
      refine Fintype.sum_equiv (finCongr hcast_c) _ _ fun c => ?_
      simp only [finCongr_apply]
      congr 1
      exact ih c
  have hlast_idx : (Fin.last (L₁ + L₂ + 1) : Fin (L₁ + L₂ + 2)) =
      ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ := Fin.ext (by simp; omega)
  have hp_eq :
      (reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ = p :=
    (width_compWidths_of_gt d₁ d₂ (by simp; omega) (by simp; omega)).trans hp₂
  have hlast := hprefix₂ (Fin.last L₂) (Fin.cast hp_eq.symm j)
  change (reluSpec (compWidths d₁ d₂)).realize θ x₀
      (Fin.cast (by simp [hp₂] :
        (compWidths d₁ d₂) (Fin.last (L₁ + L₂ + 1)) = p).symm j) =
    (h ∘ g) x j
  rw [MLPSpec.realize_def, evalPrefix_cast _ _ _ hlast_idx]
  have h_eq : Fin.cast (congrArg (reluSpec (compWidths d₁ d₂)).width hlast_idx)
      (Fin.cast (by simp [hp₂] :
        (compWidths d₁ d₂) (Fin.last (L₁ + L₂ + 1)) = p).symm j) =
      Fin.cast hp_eq.symm j := by
    ext; rfl
  rw [h_eq, hlast]
  have hlast_eq : (Fin.last L₂).succ = Fin.last (L₂ + 1) := Fin.succ_last L₂
  rw [evalPrefix_cast (reluSpec d₂) _ _ hlast_eq, ← MLPSpec.realize_def]
  have hcast_p : Fin.cast (congrArg (reluSpec d₂).width hlast_eq)
      (Fin.cast (width_compWidths_of_gt d₁ d₂ (by simp; omega) (by simp; omega))
        (Fin.cast hp_eq.symm j)) = Fin.cast hp₂.symm j := by
    ext; rfl
  rw [hcast_p]
  exact hθ₂ (g x) j

/-- Merging a depth-`(L₁ + 1)` network realizing `g : ℝⁿ → ℝᵐ` with a depth-`(L₂ + 1)`
network computing `h : ℝᵐ → ℝ` yields a depth-`(L₁ + L₂ + 1)` network computing
`h ∘ g`. -/
theorem ReLUNetComputes.comp {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → ℝ}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetComputes d₂ h) :
    ReLUNetComputes (compWidths d₁ d₂) (h ∘ g) :=
  reluNetComputes_iff_reluNetRealizes.mpr
    (hg.comp (reluNetComputes_iff_reluNetRealizes.mp hh))

/-! ### Affine layers -/

/-- Every continuous affine map `(Fin n → ℝ) →ᴬ[ℝ] (Fin m → ℝ)` is realized by a ReLU
network of depth `1` with widths `![n, m]`. -/
theorem ReLUNetRealizes.of_continuousAffineMap {n m : ℕ}
    (A : (Fin n → ℝ) →ᴬ[ℝ] (Fin m → ℝ)) :
    ReLUNetRealizes ![n, m] A := by
  let θ : (reluSpec ![n, m]).Parameters :=
    Fin.cons (fun r c => A.linear (Pi.single c 1) r, fun r => A 0 r) fun i => i.elim0
  refine ⟨rfl, rfl, θ, fun x j => ?_⟩
  rw [MLPSpec.realize_depth_one]
  have hx : x = ∑ c : Fin n, x c • Pi.single c (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  have hlin : ∑ c : Fin n, A.linear (Pi.single c 1) j * x c = A.linear x j := by
    conv_rhs => rw [hx, map_sum]
    simp [Finset.sum_apply, mul_comm]
  change (∑ c : Fin n, A.linear (Pi.single c 1) j * x c) + A 0 j = A x j
  rw [hlin]
  exact (congrFun (congrFun A.decomp x) j).symm

/-- Every continuous affine functional `(Fin n → ℝ) →ᴬ[ℝ] ℝ` is computed by a ReLU
network of depth `1` with widths `![n, 1]`. -/
theorem ReLUNetComputes.of_continuousAffineMap {n : ℕ} (A : (Fin n → ℝ) →ᴬ[ℝ] ℝ) :
    ReLUNetComputes ![n, 1] A := by
  refine reluNetComputes_iff_reluNetRealizes.mpr ?_
  let A' : (Fin n → ℝ) →ᴬ[ℝ] (Fin 1 → ℝ) :=
    { toFun := fun x _ => A x
      linear :=
        { toFun := fun x _ => A.linear x
          map_add' := fun x y => by ext; simp
          map_smul' := fun r x => by ext; simp }
      map_vadd' := fun v x => by ext; simpa [vadd_eq_add] using A.map_vadd v x
      cont := continuous_pi fun _ => A.continuous }
  exact ReLUNetRealizes.of_continuousAffineMap A'

/-! ### Parallel stacking and linear combinations -/

private def finAppendWidths {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    Fin (L + 2) → ℕ :=
  fun i => if i = 0 then n else d₁ i + d₂ i

private theorem finAppendWidths_zero {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
    (reluSpec (finAppendWidths n d₁ d₂)).width 0 = n := by
  simp [finAppendWidths]

private theorem finAppendWidths_succ {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ)
    (i : Fin (L + 1)) :
    (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
      (reluSpec d₁).width i.succ + (reluSpec d₂).width i.succ := by
  simp [finAppendWidths, Fin.succ_ne_zero]

private def finAppendParams {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (reluSpec (finAppendWidths n d₁ d₂)).Parameters := fun i =>
  Fin.cases
    (fun r c => Fin.addCases
        (fun r₁ => (θ₁ 0).1 r₁
          (Fin.cast h0₁.symm (Fin.cast (finAppendWidths_zero n d₁ d₂) c)))
        (fun r₂ => (θ₂ 0).1 r₂
          (Fin.cast h0₂.symm (Fin.cast (finAppendWidths_zero n d₁ d₂) c)))
        (Fin.cast (finAppendWidths_succ n d₁ d₂ 0) r),
     fun r => Fin.addCases (θ₁ 0).2 (θ₂ 0).2
        (Fin.cast (finAppendWidths_succ n d₁ d₂ 0) r))
    (fun k =>
      (fun r c => Fin.addCases
          (fun r₁ => Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0)
            (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
          (fun r₂ => Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂)
            (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r),
       fun r => Fin.addCases (θ₁ k.succ).2 (θ₂ k.succ).2
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r)))
    i

/-- Stacking two ReLU networks of the same positive depth `L + 1` in parallel yields a network of
depth `L + 1` with hidden widths `d₁ i + d₂ i` realizing
`fun x => Fin.append (f₁ x) (f₂ x)`. -/
theorem ReLUNetRealizes.finAppend {n m₁ m₂ L : ℕ}
    {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ : (Fin n → ℝ) → (Fin m₁ → ℝ)} {f₂ : (Fin n → ℝ) → (Fin m₂ → ℝ)}
    (hf₁ : ReLUNetRealizes d₁ f₁) (hf₂ : ReLUNetRealizes d₂ f₂) :
    ReLUNetRealizes (fun i : Fin (L + 2) => if i = 0 then n else d₁ i + d₂ i)
      (fun x => Fin.append (f₁ x) (f₂ x)) := by
  change ReLUNetRealizes (finAppendWidths n d₁ d₂) (fun x => Fin.append (f₁ x) (f₂ x))
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := hf₁
  obtain ⟨h0₂, hm₂, θ₂, hθ₂⟩ := hf₂
  have hm₁' : (reluSpec d₁).width (Fin.last L).succ = m₁ := hm₁
  have hm₂' : (reluSpec d₂).width (Fin.last L).succ = m₂ := hm₂
  let θ := finAppendParams (L := L) h0₁ h0₂ θ₁ θ₂
  have hd0 := finAppendWidths_zero n d₁ d₂
  have hd_succ := finAppendWidths_succ n d₁ d₂
  refine ⟨hd0, by simp [finAppendWidths, hm₁, hm₂], θ, fun x j => ?_⟩
  let x₀ : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width 0) → ℝ :=
    fun i => x (Fin.cast hd0 i)
  let x₁ : Fin ((reluSpec d₁).width 0) → ℝ := fun i => x (Fin.cast h0₁ i)
  let x₂ : Fin ((reluSpec d₂).width 0) → ℝ := fun i => x (Fin.cast h0₂ i)
  have hprefix : ∀ (k : Fin (L + 1))
      (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ)),
      (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix θ x₀ k.succ r =
        Fin.append
          ((reluSpec d₁).evalPrefix θ₁ x₁ k.succ)
          ((reluSpec d₂).evalPrefix θ₂ x₂ k.succ)
          (Fin.cast (hd_succ k) r) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro r
      have hlayer : ∀ t, (reluSpec (finAppendWidths n d₁ d₂)).layerActivation 0 t =
          (reluSpec d₁).layerActivation 0 t := fun t => by
        by_cases hL : L = 0
        · subst hL
          rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_val_add_one_eq 0 rfl,
            (reluSpec d₁).layerActivation_of_val_add_one_eq 0 rfl]
        · rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_lt 0 (by simp; omega),
            (reluSpec d₁).layerActivation_of_lt 0 (by simp; omega)]
          rfl
      have hlayer₂ : ∀ t, (reluSpec (finAppendWidths n d₁ d₂)).layerActivation 0 t =
          (reluSpec d₂).layerActivation 0 t := fun t => by
        by_cases hL : L = 0
        · subst hL
          rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_val_add_one_eq 0 rfl,
            (reluSpec d₂).layerActivation_of_val_add_one_eq 0 rfl]
        · rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_lt 0 (by simp; omega),
            (reluSpec d₂).layerActivation_of_lt 0 (by simp; omega)]
          rfl
      rw [evalPrefix_succ_apply, evalPrefix_castSucc_zero]
      cases hrc : Fin.cast (hd_succ 0) r using Fin.addCases with
      | left r₁ =>
        rw [Fin.append_left, evalPrefix_succ_apply, evalPrefix_castSucc_zero, hlayer]
        apply congrArg ((reluSpec d₁).layerActivation 0)
        dsimp only [θ, finAppendParams]
        simp only [Fin.cases_zero, hrc, Fin.addCases_left, Matrix.mulVec, dotProduct]
        congr 1
        refine Fintype.sum_equiv ((finCongr hd0).trans (finCongr h0₁).symm) _ _ fun c => ?_
        exact congrArg₂ (· * ·)
          (congrArg ((θ₁ 0).1 r₁) (Fin.ext (by simp [finCongr_apply])))
          (congrArg x (Fin.ext (by simp [finCongr_apply])))
      | right r₂ =>
        rw [Fin.append_right, evalPrefix_succ_apply, evalPrefix_castSucc_zero, hlayer₂]
        apply congrArg ((reluSpec d₂).layerActivation 0)
        dsimp only [θ, finAppendParams]
        simp only [Fin.cases_zero, hrc, Fin.addCases_right, Matrix.mulVec, dotProduct]
        congr 1
        refine Fintype.sum_equiv ((finCongr hd0).trans (finCongr h0₂).symm) _ _ fun c => ?_
        exact congrArg₂ (· * ·)
          (congrArg ((θ₂ 0).1 r₂) (Fin.ext (by simp [finCongr_apply])))
          (congrArg x (Fin.ext (by simp [finCongr_apply])))
    | succ k ih =>
      intro r
      have hlayer₁ : ∀ t, (reluSpec (finAppendWidths n d₁ d₂)).layerActivation k.succ t =
          (reluSpec d₁).layerActivation k.succ t := fun t => by
        by_cases hlt : k.val + 1 < L
        · rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_lt k.succ
              (by simp; omega),
            (reluSpec d₁).layerActivation_of_lt k.succ (by simp; omega)]
          rfl
        · rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_val_add_one_eq k.succ
              (by simp; omega),
            (reluSpec d₁).layerActivation_of_val_add_one_eq k.succ (by simp; omega)]
      have hlayer₂ : ∀ t, (reluSpec (finAppendWidths n d₁ d₂)).layerActivation k.succ t =
          (reluSpec d₂).layerActivation k.succ t := fun t => by
        by_cases hlt : k.val + 1 < L
        · rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_lt k.succ
              (by simp; omega),
            (reluSpec d₂).layerActivation_of_lt k.succ (by simp; omega)]
          rfl
        · rw [(reluSpec (finAppendWidths n d₁ d₂)).layerActivation_of_val_add_one_eq k.succ
              (by simp; omega),
            (reluSpec d₂).layerActivation_of_val_add_one_eq k.succ (by simp; omega)]
      have hcast_w : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc =
          (reluSpec d₁).width k.castSucc.succ + (reluSpec d₂).width k.castSucc.succ :=
        hd_succ k.castSucc
      rw [evalPrefix_succ_apply]
      cases hrc : Fin.cast (hd_succ k.succ) r using Fin.addCases with
      | left r₁ =>
        rw [Fin.append_left, evalPrefix_succ_apply, hlayer₁]
        apply congrArg ((reluSpec d₁).layerActivation k.succ)
        dsimp only [θ, finAppendParams]
        simp only [Fin.cases_succ, hrc, Fin.addCases_left, Matrix.mulVec, dotProduct]
        congr 1
        rw [← Equiv.sum_comp (finCongr hcast_w).symm, Fin.sum_univ_add]
        simp only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq,
          Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        congr 1
        have hidx_eq : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width
              (rfl : k.succ.castSucc = k.castSucc.succ))
            (Fin.cast hcast_w.symm (Fin.castAdd ((reluSpec d₂).width k.castSucc.succ) c₁)) =
            Fin.cast (hd_succ k.castSucc).symm
              (Fin.castAdd ((reluSpec d₂).width k.castSucc.succ) c₁) := Fin.ext rfl
        rw [evalPrefix_cast _ (finAppendParams h0₁ h0₂ θ₁ θ₂) x₀
          (rfl : k.succ.castSucc = k.castSucc.succ), hidx_eq]
        exact (ih _).trans (by
          simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
          rw [Fin.append_left, evalPrefix_cast (reluSpec d₁) θ₁ x₁
            (rfl : k.castSucc.succ = k.succ.castSucc)]
          rfl)
      | right r₂ =>
        rw [Fin.append_right, evalPrefix_succ_apply, hlayer₂]
        apply congrArg ((reluSpec d₂).layerActivation k.succ)
        dsimp only [θ, finAppendParams]
        simp only [Fin.cases_succ, hrc, Fin.addCases_right, Matrix.mulVec, dotProduct]
        congr 1
        rw [← Equiv.sum_comp (finCongr hcast_w).symm, Fin.sum_univ_add]
        simp only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq,
          Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, zero_add]
        refine Finset.sum_congr rfl fun c₂ _ => ?_
        congr 1
        have hidx_eq : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width
              (rfl : k.succ.castSucc = k.castSucc.succ))
            (Fin.cast hcast_w.symm (Fin.natAdd ((reluSpec d₁).width k.castSucc.succ) c₂)) =
            Fin.cast (hd_succ k.castSucc).symm
              (Fin.natAdd ((reluSpec d₁).width k.castSucc.succ) c₂) := Fin.ext rfl
        rw [evalPrefix_cast _ (finAppendParams h0₁ h0₂ θ₁ θ₂) x₀
          (rfl : k.succ.castSucc = k.castSucc.succ), hidx_eq]
        exact (ih _).trans (by
          simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
          rw [Fin.append_right, evalPrefix_cast (reluSpec d₂) θ₂ x₂
            (rfl : k.castSucc.succ = k.succ.castSucc)]
          rfl)
  have hm_eq : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last L).succ = m₁ + m₂ := by
    simp [finAppendWidths, hm₁, hm₂]
  have hlast := hprefix (Fin.last L) (Fin.cast hm_eq.symm j)
  change (reluSpec (finAppendWidths n d₁ d₂)).realize θ x₀
      (Fin.cast (by simp [finAppendWidths, hm₁, hm₂] :
        finAppendWidths n d₁ d₂ (Fin.last (L + 1)) = m₁ + m₂).symm j) =
    Fin.append (f₁ x) (f₂ x) j
  rw [MLPSpec.realize_def]
  have hlast_eq : (Fin.last (L + 1) : Fin (L + 2)) = (Fin.last L).succ := rfl
  rw [evalPrefix_cast _ _ _ hlast_eq]
  have hcast_j : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hlast_eq)
      (Fin.cast (by simp [finAppendWidths, hm₁, hm₂] :
        finAppendWidths n d₁ d₂ (Fin.last (L + 1)) = m₁ + m₂).symm j) =
      Fin.cast hm_eq.symm j := by
    ext; rfl
  rw [hcast_j, hlast]
  cases hj : j using Fin.addCases with
  | left j₁ =>
    have hidx : Fin.cast (hd_succ (Fin.last L)) (Fin.cast hm_eq.symm (Fin.castAdd m₂ j₁)) =
        Fin.castAdd ((reluSpec d₂).width (Fin.last L).succ) (Fin.cast hm₁'.symm j₁) := by
      ext; simp
    rw [hidx, Fin.append_left]
    have hfin : Fin.append (f₁ x) (f₂ x) (Fin.castAdd m₂ j₁) = f₁ x j₁ :=
      Fin.append_left _ _ j₁
    rw [hfin, evalPrefix_cast (reluSpec d₁) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₁ x j₁
  | right j₂ =>
    have hidx : Fin.cast (hd_succ (Fin.last L)) (Fin.cast hm_eq.symm (Fin.natAdd m₁ j₂)) =
        Fin.natAdd ((reluSpec d₁).width (Fin.last L).succ) (Fin.cast hm₂'.symm j₂) := by
      ext
      simp only [Fin.val_cast, Fin.val_natAdd, hm₁']
    rw [hidx, Fin.append_right]
    have hfin : Fin.append (f₁ x) (f₂ x) (Fin.natAdd m₁ j₂) = f₂ x j₂ :=
      Fin.append_right _ _ j₂
    rw [hfin, evalPrefix_cast (reluSpec d₂) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₂ x j₂

/-- Parallel sum of two ReLU networks of the same positive depth `L + 1`: if `d₁` computes `f₁`
and `d₂` computes `f₂`, then a network of depth `L + 1` with hidden widths `d₁ i + d₂ i`
computes `fun x => a * f₁ x + b * f₂ x + c`. -/
theorem ReLUNetComputes.linearComb {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ f₂ : (Fin n → ℝ) → ℝ} (hf₁ : ReLUNetComputes d₁ f₁)
    (hf₂ : ReLUNetComputes d₂ f₂) (a b c : ℝ) :
    ReLUNetComputes
      (fun i : Fin (L + 2) =>
        if i = 0 then n else if i = Fin.last (L + 1) then 1 else d₁ i + d₂ i)
      (fun x => a * f₁ x + b * f₂ x + c) := by
  let g₁ := reluNetComputes_iff_reluNetRealizes.mp hf₁
  let g₂ := reluNetComputes_iff_reluNetRealizes.mp hf₂
  let A : (Fin 2 → ℝ) →ᴬ[ℝ] ℝ :=
    { toFun := fun y => a * y 0 + b * y 1 + c
      linear :=
        { toFun := fun y => a * y 0 + b * y 1
          map_add' := fun y z => by simp only [Pi.add_apply]; ring
          map_smul' := fun r y => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
      map_vadd' := fun v y => by simp [vadd_eq_add]; ring
      cont := by fun_prop }
  have hcomp :=
    ReLUNetComputes.comp (g₁.finAppend g₂) (ReLUNetComputes.of_continuousAffineMap A)
  have heq : (A ∘ fun x => Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x)) =
      fun x => a * f₁ x + b * f₂ x + c := by
    funext x
    have h0 : Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x) 0 = f₁ x :=
      Fin.append_left _ _ 0
    have h1 : Fin.append (fun _ : Fin 1 => f₁ x) (fun _ : Fin 1 => f₂ x) 1 = f₂ x :=
      Fin.append_right _ _ 0
    simp [A, h0, h1]
  rw [heq] at hcomp
  refine hcomp.of_width_eq ?_
  ext i
  by_cases hi0 : i = 0
  · subst hi0
    simp
  · by_cases hiL : i = Fin.last (L + 1)
    · subst hiL
      simp
    · have hle : i.val ≤ L := by
        have := i.isLt
        have : i.val ≠ L + 1 := fun h => hiL (Fin.ext h)
        omega
      simp only [compWidths, hle, ↓reduceDIte, hi0, ↓reduceIte, hiL]

/-! ### Depth padding -/

private theorem reluNetRealizes_depth_two {a b c : ℕ}
    (W₀ : Matrix (Fin b) (Fin a) ℝ) (b₀ : Fin b → ℝ)
    (W₁ : Matrix (Fin c) (Fin b) ℝ) (b₁ : Fin c → ℝ)
    (f : (Fin a → ℝ) → (Fin c → ℝ))
    (hf : ∀ x j, (∑ k : Fin b, W₁ j k * max 0 ((W₀ *ᵥ x) k + b₀ k)) + b₁ j = f x j) :
    ReLUNetRealizes ![a, b, c] f := by
  let θ : (reluSpec ![a, b, c]).Parameters :=
    Fin.cons (W₀, b₀) (Fin.cons (W₁, b₁) fun i => i.elim0)
  have ha : (reluSpec ![a, b, c]).width 0 = a := rfl
  have hb : (reluSpec ![a, b, c]).width (0 : Fin 2).succ = b := rfl
  have hc : (reluSpec ![a, b, c]).width (Fin.last 1).succ = c := rfl
  refine ⟨rfl, rfl, θ, fun x j => ?_⟩
  let x₀ : Fin ((reluSpec ![a, b, c]).width 0) → ℝ := fun i => x (Fin.cast ha i)
  have h1 : ∀ k : Fin b,
      (reluSpec ![a, b, c]).evalPrefix θ x₀ (0 : Fin 2).succ (Fin.cast hb.symm k) =
        max 0 ((W₀ *ᵥ x) k + b₀ k) := fun k => by
    rw [evalPrefix_succ_apply, (reluSpec ![a, b, c]).layerActivation_of_lt 0 (by decide),
      evalPrefix_castSucc_zero, reluSpec_activation]
    congr 1
  change (reluSpec ![a, b, c]).realize θ x₀ (Fin.cast hc.symm j) = f x j
  rw [MLPSpec.realize_succ]
  have hlhs :
      ((θ (Fin.last 1)).1 *ᵥ (reluSpec ![a, b, c]).evalPrefix θ x₀ (Fin.last 1).castSucc +
          (θ (Fin.last 1)).2) (Fin.cast hc.symm j) =
        (∑ k : Fin b, W₁ j k * (reluSpec ![a, b, c]).evalPrefix θ x₀
          (0 : Fin 2).succ (Fin.cast hb.symm k)) + b₁ j := by
    change (∑ k : Fin ((reluSpec ![a, b, c]).width (0 : Fin 2).succ),
        W₁ (Fin.cast hc (Fin.cast hc.symm j)) (Fin.cast hb k) *
          (reluSpec ![a, b, c]).evalPrefix θ x₀ (0 : Fin 2).succ k) + b₁ j = _
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
    congr 1
  rw [hlhs]
  simp_rw [h1]
  exact hf x j

/-- A depth-2 ReLU network of hidden width `2 * m` realizes the identity on `Fin m → ℝ` via
`t = max 0 t - max 0 (-t)`. -/
theorem ReLUNetRealizes.id_depth_two (m : ℕ) :
    ReLUNetRealizes ![m, 2 * m, m] (id : (Fin m → ℝ) → (Fin m → ℝ)) := by
  have hm : 2 * m = m + m := Nat.two_mul m
  let W₀ : Matrix (Fin (2 * m)) (Fin m) ℝ := fun r c =>
    Fin.addCases (fun r₁ => if r₁ = c then 1 else 0) (fun r₂ => if r₂ = c then -1 else 0)
      (Fin.cast hm r)
  let W₁ : Matrix (Fin m) (Fin (2 * m)) ℝ := fun r c =>
    Fin.addCases (fun c₁ => if r = c₁ then 1 else 0) (fun c₂ => if r = c₂ then -1 else 0)
      (Fin.cast hm c)
  refine reluNetRealizes_depth_two W₀ 0 W₁ 0 id fun x j => ?_
  have h0 : ∀ r : Fin (2 * m), (W₀ *ᵥ x) r =
      Fin.addCases (fun r₁ => x r₁) (fun r₂ => -x r₂) (Fin.cast hm r) := by
    intro r
    simp only [Matrix.mulVec, dotProduct]
    cases hr : Fin.cast hm r using Fin.addCases with
    | left r₁ =>
      simp only [W₀, hr, Fin.addCases_left, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
    | right r₂ =>
      simp only [W₀, hr, Fin.addCases_right, ite_mul, neg_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [Pi.zero_apply, add_zero]
  simp_rw [h0]
  have hsum : (∑ k : Fin (2 * m), W₁ j k *
      max 0 (Fin.addCases (fun r₁ => x r₁) (fun r₂ => -x r₂) (Fin.cast hm k))) =
      ∑ k : Fin (m + m), W₁ j (Fin.cast hm.symm k) *
        max 0 (Fin.addCases (fun r₁ => x r₁) (fun r₂ => -x r₂) k) := by
    refine Fintype.sum_equiv (finCongr hm) _ _ fun k => ?_
    simp [finCongr_apply]
  rw [hsum, Fin.sum_univ_add]
  simp only [W₁, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.addCases_left, Fin.addCases_right,
    ite_mul, one_mul, neg_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  linarith [max_zero_sub_eq_self (x j)]
  where
    max_zero_sub_eq_self (t : ℝ) : max 0 t - max 0 (-t) = t := by
      rcases le_total 0 t with ht | ht <;> simp [ht]

/-- Appending a hidden layer of width `2 * m` preserves realization, increasing depth by one. -/
theorem ReLUNetRealizes.pad {n m L : ℕ} {d : Fin (L + 2) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) :
    ReLUNetRealizes
      (fun i : Fin (L + 3) =>
        if _ : i.val ≤ L then d ⟨i.val, by omega⟩
        else if i = Fin.last (L + 2) then m else 2 * m)
      f := by
  have hcomp := hf.comp (ReLUNetRealizes.id_depth_two m)
  refine hcomp.of_width_eq ?_
  ext i
  by_cases hi : i.val ≤ L
  · simp [compWidths, hi]
  · by_cases hiL : i = Fin.last (L + 2)
    · subst hiL
      have h1 : ¬ (L + 2 ≤ L) := by omega
      simp [compWidths, h1]
    · have hi1 : i.val = L + 1 := by
        have := i.isLt
        have : i.val ≠ L + 2 := fun h => hiL (Fin.ext h)
        omega
      simp [compWidths, hiL, hi1]

/-- Appending a two-unit hidden layer preserves scalar computation, increasing depth by one. -/
theorem ReLUNetComputes.pad {n L : ℕ} {d : Fin (L + 2) → ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ReLUNetComputes d f) :
    ReLUNetComputes
      (fun i : Fin (L + 3) =>
        if _ : i.val ≤ L then d ⟨i.val, by omega⟩
        else if i = Fin.last (L + 2) then 1 else 2)
      f :=
  reluNetComputes_iff_reluNetRealizes.mpr
    (reluNetComputes_iff_reluNetRealizes.mp hf).pad

private theorem ReLUNetComputes.pad_pos {n L : ℕ} (hL : 1 ≤ L) {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) :
    ∃ d' : Fin (L + 2) → ℕ, ReLUNetComputes d' f := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hL)
  subst hm
  exact ⟨_, hf.pad⟩

/-- A scalar function computed at depth `L₁ ≥ 1` is computed at every depth `L₂ ≥ L₁`. -/
theorem exists_reluNetComputes_of_le {n L₁ L₂ : ℕ} (hL₁ : 1 ≤ L₁) (hL : L₁ ≤ L₂)
    {d₁ : Fin (L₁ + 1) → ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d₁ f) :
    ∃ d₂ : Fin (L₂ + 1) → ℕ, ReLUNetComputes d₂ f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hL
  induction k with
  | zero => exact ⟨d₁, hf⟩
  | succ k ih =>
    obtain ⟨d, hd⟩ := ih (by omega)
    rw [← Nat.add_assoc]
    exact hd.pad_pos (by omega)

/-- Every continuous affine functional `(Fin n → ℝ) →ᴬ[ℝ] ℝ` is computed by a ReLU
network of every positive depth `L ≥ 1`. -/
theorem exists_reluNetComputes_of_continuousAffineMap {n L : ℕ} (hL : 1 ≤ L)
    (A : (Fin n → ℝ) →ᴬ[ℝ] ℝ) :
    ∃ d : Fin (L + 1) → ℕ, ReLUNetComputes d A :=
  exists_reluNetComputes_of_le (le_refl 1) hL (ReLUNetComputes.of_continuousAffineMap A)

/-! ### Edge cases and concrete networks -/

/-- A depth-zero ReLU network on `ℝ` computes only the identity `x ↦ x 0`. -/
theorem reluNetComputes_depth_zero_iff {f : (Fin 1 → ℝ) → ℝ} :
    ReLUNetComputes ![1] f ↔ f = fun x => x 0 := by
  constructor
  · rintro ⟨h0, hL, θ, hθ⟩
    ext x
    have hx := (hθ x).symm
    rw [MLPSpec.realize_depth_zero] at hx
    simpa [Fin.eq_zero] using hx
  · rintro rfl
    refine ⟨rfl, rfl, fun i => i.elim0, fun x => ?_⟩
    rw [MLPSpec.realize_depth_zero]
    exact congrArg x (Fin.eq_zero _)

/-- A depth-one ReLU network computes a function if and only if that function is continuous
affine. -/
theorem reluNetComputes_depth_one_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    (∃ d : Fin 2 → ℕ, ReLUNetComputes d f) ↔
      ∃ A : (Fin n → ℝ) →ᴬ[ℝ] ℝ, f = ⇑A := by
  constructor
  · rintro ⟨d, h0, hL, θ, hθ⟩
    let Lmap : (Fin n → ℝ) →L[ℝ] ℝ :=
      { toFun := fun x =>
          ∑ j : Fin ((reluSpec d).width 0), (θ 0).1 (Fin.cast hL.symm 0) j * x (Fin.cast h0 j)
        map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r x => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        cont := by fun_prop }
    refine ⟨Lmap.toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (Fin n → ℝ) ((θ 0).2 (Fin.cast hL.symm 0)), ?_⟩
    ext x
    have hx := (hθ x).symm
    rw [MLPSpec.realize_depth_one] at hx
    simp only [ContinuousAffineMap.add_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousAffineMap.coe_const, Function.const_apply]
    rw [hx]
    rfl
  · rintro ⟨A, rfl⟩
    exact ⟨![n, 1], ReLUNetComputes.of_continuousAffineMap A⟩

/-- A ReLU network with a hidden layer of width zero computes a constant function. -/
theorem reluSpec_realize_eq_of_width_eq_zero {L : ℕ} {d : Fin (L + 1) → ℕ}
    (θ : (reluSpec d).Parameters) {k : Fin (L + 1)} (hk : d k = 0)
    (x x' : Fin (d 0) → ℝ) :
    (reluSpec d).realize θ x = (reluSpec d).realize θ x' :=
  (reluSpec d).realize_eq_of_width_eq_zero θ hk x x'

/-- The absolute value `x ↦ |x 0|` on `ℝ` is computed by a depth-2 ReLU network with two hidden
units (`![1, 2, 1]`). -/
theorem reluNetComputes_abs :
    ReLUNetComputes ![1, 2, 1] (fun x : Fin 1 → ℝ => |x 0|) := by
  refine reluNetComputes_iff_reluNetRealizes.mpr
    (reluNetRealizes_depth_two !![1; -1] 0 !![1, 1] 0 _ fun x j => ?_)
  simp only [Fin.eq_zero j, Pi.zero_apply, add_zero, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, neg_mul]
  rcases le_total 0 (x 0) with h | h <;> simp [h, abs_of_nonneg, abs_of_nonpos]

/-- No depth-1 ReLU network computes `x ↦ |x 0|`, since depth-1 networks compute only affine
functions. -/
theorem not_reluNetComputes_depth_one_abs :
    ¬∃ d : Fin 2 → ℕ, ReLUNetComputes d (fun x : Fin 1 → ℝ => |x 0|) := by
  rw [reluNetComputes_depth_one_iff]
  rintro ⟨A, hA⟩
  let e : ℝ →ᴬ[ℝ] (Fin 1 → ℝ) :=
    { toFun := fun t _ => t
      linear :=
        { toFun := fun t _ => t
          map_add' := fun s t => rfl
          map_smul' := fun r t => rfl }
      map_vadd' := fun v t => rfl
      cont := continuous_pi fun _ => continuous_id }
  exact not_exists_continuousAffineMap_eq_abs
    ⟨A.comp e, fun t => congrFun hA (fun _ => t)⟩

/-- `max x₀ x₁ = max 0 (x₀ - x₁) + max 0 x₁ - max 0 (-x₁)` is computed by a depth-2 ReLU
network with three hidden units (`![2, 3, 1]`). -/
theorem reluNetComputes_max :
    ReLUNetComputes ![2, 3, 1] (fun x : Fin 2 → ℝ => max (x 0) (x 1)) := by
  refine reluNetComputes_iff_reluNetRealizes.mpr
    (reluNetRealizes_depth_two !![1, -1; 0, 1; 0, -1] 0 !![1, 1, -1] 0 _ fun x j => ?_)
  simp only [Fin.eq_zero j, Pi.zero_apply, add_zero, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, neg_mul, zero_mul, zero_add]
  rcases le_total (x 0) (x 1) with h | h <;> rcases le_total 0 (x 1) with h1 | h1 <;>
    simp [h, h1]

/-! ### ReLU networks compute piecewise-affine maps -/

/-- Every prefix evaluation of `reluSpec d` is globally piecewise affine on `Fin (d 0) → ℝ`. -/
theorem isPiecewiseAffineOn_reluSpec_evalPrefix {L : ℕ} (d : Fin (L + 1) → ℕ)
    (θ : (reluSpec d).Parameters) (i : Fin (L + 1)) :
    IsPiecewiseAffineOn (fun x => (reluSpec d).evalPrefix θ x i)
      (univ : Set (Fin (d 0) → ℝ)) := by
  induction i using Fin.induction with
  | zero =>
    exact (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.id ℝ (Fin ((reluSpec d).width 0) → ℝ)) univ).congr fun x _ =>
      MLPSpec.evalPrefix_zero (reluSpec d) θ x
  | succ i ih =>
    let Lmap : (Fin ((reluSpec d).width i.castSucc) → ℝ) →L[ℝ]
        (Fin ((reluSpec d).width i.succ) → ℝ) :=
      { toFun := fun v => (θ i).1 *ᵥ v
        map_add' := fun u v => Matrix.mulVec_add (θ i).1 u v
        map_smul' := fun r v => Matrix.mulVec_smul (θ i).1 r v
        cont := continuous_pi fun j => by
          simp only [Matrix.mulVec, dotProduct]
          fun_prop }
    have haff : IsPiecewiseAffineOn
        (fun v : Fin ((reluSpec d).width i.castSucc) → ℝ => (θ i).1 *ᵥ v + (θ i).2) univ :=
      (isPiecewiseAffineOn_continuousAffineMap
        (Lmap.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ (θ i).2)
        univ).congr fun _ _ => rfl
    have hstep := haff.comp ih (mapsTo_univ _ _)
    by_cases hlt : i.val + 1 < L
    · have hact : ∀ x, (reluSpec d).evalPrefix θ x i.succ =
          fun j => max 0 (((θ i).1 *ᵥ (reluSpec d).evalPrefix θ x i.castSucc) j + (θ i).2 j) :=
        fun x => by
          rw [MLPSpec.evalPrefix_succ, (reluSpec d).layerActivation_of_lt i hlt]
          rfl
      exact ((isPiecewiseAffineOn_pi_max_zero (Fin ((reluSpec d).width i.succ))).comp hstep
        (mapsTo_univ _ _)).congr fun x _ => hact x
    · have heq : i.val + 1 = L := by omega
      have hact : ∀ x, (reluSpec d).evalPrefix θ x i.succ =
          (θ i).1 *ᵥ (reluSpec d).evalPrefix θ x i.castSucc + (θ i).2 :=
        fun x => (reluSpec d).evalPrefix_succ_of_val_add_one_eq θ x i heq
      exact hstep.congr fun x _ => hact x

/-- The realization map of `reluSpec d` at any parameters `θ` is globally piecewise affine. -/
theorem isPiecewiseAffineOn_reluSpec_realize {L : ℕ} (d : Fin (L + 1) → ℕ)
    (θ : (reluSpec d).Parameters) :
    IsPiecewiseAffineOn ((reluSpec d).realize θ) (univ : Set (Fin (d 0) → ℝ)) :=
  (isPiecewiseAffineOn_reluSpec_evalPrefix d θ (Fin.last L)).congr fun x _ =>
    (reluSpec d).realize_def θ x

/-- Every function `(Fin n → ℝ) → (Fin m → ℝ)` realized by a ReLU network is globally
piecewise affine. -/
theorem isPiecewiseAffineOn_of_reluNetRealizes {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) :
    IsPiecewiseAffineOn f (univ : Set (Fin n → ℝ)) := by
  obtain ⟨h0, hL, θ, hθ⟩ := hf
  let eIn : (Fin n → ℝ) →L[ℝ] (Fin (d 0) → ℝ) :=
    { toFun := fun x i => x (Fin.cast h0 i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_pi fun i => continuous_apply _ }
  let eOut : (Fin (d (Fin.last L)) → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun := fun y j => y (Fin.cast hL.symm j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_pi fun j => continuous_apply _ }
  have h1 := (isPiecewiseAffineOn_reluSpec_realize d θ).comp
    (isPiecewiseAffineOn_continuousAffineMap eIn.toContinuousAffineMap univ) (mapsTo_univ _ _)
  have h2 := (isPiecewiseAffineOn_continuousAffineMap eOut.toContinuousAffineMap univ).comp
    h1 (mapsTo_univ _ _)
  exact h2.congr fun x _ => by
    ext j
    exact (hθ x j).symm

/-- Every scalar function `(Fin n → ℝ) → ℝ` computed by a ReLU network is continuous
piecewise linear (piecewise affine on the whole space). -/
theorem isPiecewiseAffineOn_of_reluNetComputes {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) :
    IsPiecewiseAffineOn f (univ : Set (Fin n → ℝ)) := by
  have hvec := isPiecewiseAffineOn_of_reluNetRealizes (reluNetComputes_iff_reluNetRealizes.mp hf)
  have hproj := isPiecewiseAffineOn_continuousAffineMap
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ)
      (0 : Fin 1)).toContinuousAffineMap
    univ
  exact (hproj.comp hvec (mapsTo_univ _ _)).congr fun _ _ => rfl

end TauCeti
