/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import TauCeti.Topology.PL.PiecewiseAffine
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# ReLU multilayer perceptrons and continuous piecewise-linear functions

A ReLU network of depth `L` with widths `d : Fin (L + 1) → ℕ` is the `Neuromanifold.MLPSpec`
`TauCeti.reluSpec d` whose every hidden activation is the scalar rectifier `t ↦ max 0 t`, with
an affine output layer.
The predicates `TauCeti.ReLUNetRealizes d f` (for `ℝⁿ → ℝᵐ`) and
`TauCeti.ReLUNetComputes d f` (for `ℝⁿ → ℝ`) assert that the input and output widths match
and some parameters realize `f`.

This file builds the structural calculus for ReLU networks of positive depth and connects them to
piecewise-affine maps:

* **Composition** (`ReLUNetRealizes.comp`, `ReLUNetComputes.comp`): merging the affine output
  layer of a depth-`(L₁ + 1)` network with the affine input layer of a depth-`(L₂ + 1)` network
  yields a depth-`(L₁ + L₂ + 1)` network realizing the composite with widths `compWidths`.
* **Parallel stacking and affine combinations** (`ReLUNetRealizes.finAppend`,
  `ReLUNetComputes.affineComb`): placing two networks of the same positive depth side by side adds
  their hidden widths; composing with an affine output layer gives arbitrary affine combinations
  `a * f₁ x + b * f₂ x + c`.
* **Affine layers and depth padding** (`ReLUNetRealizes.of_continuousAffineMap`,
  `ReLUNetRealizes.pad`, `ReLUNetComputes.pad`,
  `exists_reluNetComputes_of_continuousAffineMap`): continuous affine maps are realized at depth
  `1`, padding appends a `2 * m`-unit hidden layer (two units in the scalar case) via
  `t = max 0 t - max 0 (-t)`, and continuous affine functionals are computed at every positive
  depth.
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

namespace TauCeti

open Neuromanifold

/-! ### ReLU MLP specification and realization predicates -/

/-- The ReLU multilayer perceptron specification with widths `d 0, …, d L`: every hidden layer
applies `t ↦ max 0 t` coordinatewise, and the output layer is affine. -/
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

/-- Each layer of `reluSpec d` applies `t ↦ max 0 t` when hidden and `id` at the output. -/
theorem layerActivation_reluSpec {L : ℕ} (d : Fin (L + 1) → ℕ) (i : Fin L) :
    (reluSpec d).layerActivation i = if i.val + 1 < L then (max 0 ·) else id := by
  ext t
  have hi : i.val < L := i.isLt
  by_cases h : i.val + 1 < L
  · simp [MLPSpec.layerActivation_of_lt _ _ h, h]
  · have hi_eq : i.val + 1 = L := by omega
    simp [MLPSpec.layerActivation_of_val_add_one_eq _ _ hi_eq, h]

/-- Two ReLU specifications apply the same layer activation whenever their layer indices agree on
being hidden versus output. -/
theorem layerActivation_reluSpec_eq {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 1) → ℕ)
    (d₂ : Fin (L₂ + 1) → ℕ) {i₁ : Fin L₁} {i₂ : Fin L₂}
    (h : i₁.val + 1 < L₁ ↔ i₂.val + 1 < L₂) :
    (reluSpec d₁).layerActivation i₁ = (reluSpec d₂).layerActivation i₂ := by
  simp only [layerActivation_reluSpec, h]

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

/-- The hidden layers of a network of depth `L`: the indices strictly between the input `0` and
the output `Fin.last L`. -/
def hiddenLayers (L : ℕ) : Finset (Fin (L + 1)) :=
  Finset.Ioo 0 (Fin.last L)

/-- Membership in `hiddenLayers L` means being neither the input layer nor the output layer. -/
@[simp]
theorem mem_hiddenLayers_iff {L : ℕ} {i : Fin (L + 1)} :
    i ∈ hiddenLayers L ↔ i ≠ 0 ∧ i ≠ Fin.last L := by
  simp only [hiddenLayers, Finset.mem_Ioo, Fin.pos_iff_ne_zero, Fin.lt_last_iff_ne_last]

/-- Membership in `hiddenLayers L` in terms of natural-number indices: `0 < i.val < L`. -/
theorem mem_hiddenLayers_iff_lt {L : ℕ} {i : Fin (L + 1)} :
    i ∈ hiddenLayers L ↔ 0 < i.val ∧ i.val < L := by
  simp only [hiddenLayers, Finset.mem_Ioo, Fin.lt_def, Fin.val_zero, Fin.val_last]

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
  simp [hiddenLayers, Fin.card_Ioo]

/-! ### Composition -/

/-- The width tuple obtained by merging the output affine layer of a depth-`(L₁ + 1)` network
with the input affine layer of a depth-`(L₂ + 1)` network, producing depth `L₁ + L₂ + 1`. -/
def compWidths {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ) (d₂ : Fin (L₂ + 2) → ℕ) :
    Fin (L₁ + L₂ + 2) → ℕ :=
  fun i =>
    if _ : i.val ≤ L₁ then d₁ ⟨i.val, by omega⟩ else d₂ ⟨i.val - L₁, by omega⟩

/-- On indices `i : Fin (L₁ + 1)` below the merge layer, `compWidths` agrees with `d₁`. -/
@[simp]
theorem compWidths_left {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) (i : Fin (L₁ + 1)) :
    compWidths d₁ d₂ ⟨i.val, by omega⟩ = d₁ i.castSucc := by
  have hi : i.val ≤ L₁ := Nat.le_of_lt_succ i.isLt
  simp only [compWidths, hi, ↓reduceDIte]
  exact congrArg d₁ (Fin.ext rfl)

/-- On shifted indices `L₁ + 1 + i` above the merge layer, `compWidths` agrees with `d₂ i.succ`. -/
@[simp]
theorem compWidths_right {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
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
  compWidths_left d₁ d₂ 0

/-- The output width of `compWidths d₁ d₂` is `d₂ (Fin.last (L₂ + 1))`. -/
@[simp]
theorem compWidths_last {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) :
    compWidths d₁ d₂ (Fin.last (L₁ + L₂ + 1)) = d₂ (Fin.last (L₂ + 1)) := by
  rw [show Fin.last (L₁ + L₂ + 1) = ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ from
    Fin.ext (by simp; omega)]
  exact compWidths_right d₁ d₂ (Fin.last L₂)

private theorem width_compWidths_of_le {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} {j : Fin (L₁ + 2)}
    (hi : i.val ≤ L₁) (hij : i.val = j.val) :
    (reluSpec (compWidths d₁ d₂)).width i = (reluSpec d₁).width j := by
  simp only [reluSpec_width, compWidths, hi, ↓reduceDIte]
  exact congrArg d₁ (Fin.ext hij)

private theorem width_compWidths_of_lt {L₁ L₂ : ℕ} (d₁ : Fin (L₁ + 2) → ℕ)
    (d₂ : Fin (L₂ + 2) → ℕ) {i : Fin (L₁ + L₂ + 2)} {j : Fin (L₂ + 2)}
    (hi : L₁ < i.val) (hij : i.val - L₁ = j.val) :
    (reluSpec (compWidths d₁ d₂)).width i = (reluSpec d₂).width j := by
  have hnot : ¬ i.val ≤ L₁ := Nat.not_le_of_lt hi
  simp only [reluSpec_width, compWidths, hnot, ↓reduceDIte]
  exact congrArg d₂ (Fin.ext hij)

private def compParams {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
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
      width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp [heq])
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
      width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp [k]; omega)
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp [k]; omega)
    (fun r c => (θ₂ k.succ).1 (Fin.cast hr r) (Fin.cast hc c),
     fun r => (θ₂ k.succ).2 (Fin.cast hr r))

private theorem compParams_lt {m L₁ L₂ : ℕ} {d₁ : Fin (L₁ + 2) → ℕ}
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
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
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
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
    {d₂ : Fin (L₂ + 2) → ℕ} (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m)
    (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L₂) :
    let i : Fin (L₁ + L₂ + 1) := ⟨L₁ + 1 + k.val, by omega⟩
    have hr : (reluSpec (compWidths d₁ d₂)).width i.succ = (reluSpec d₂).width k.succ.succ :=
      width_compWidths_of_lt d₁ d₂ (by dsimp [i]; omega) (by dsimp [i]; omega)
    have hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_lt d₁ d₂ (by dsimp [i]; omega) (by dsimp [i]; omega)
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

private theorem compParams_evalPrefix_lt {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    (h0c : (reluSpec (compWidths d₁ d₂)).width 0 = n)
    (h0₁ : (reluSpec d₁).width 0 = n)
    (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m) (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (x : Fin n → ℝ) (k : Fin (L₁ + 1))
    (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨k.val, by omega⟩)) :
    (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
        (fun i => x (Fin.cast h0c i)) ⟨k.val, by omega⟩ r =
      (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.castSucc
        (Fin.cast (width_compWidths_of_le d₁ d₂ (Nat.le_of_lt_succ k.isLt) rfl) r) := by
  induction k using Fin.induction with
  | zero =>
    have hzero₁ : (⟨(0 : Fin (L₁ + 1)).val, by omega⟩ : Fin (L₁ + L₂ + 2)) = 0 := Fin.ext rfl
    rw [MLPSpec.evalPrefix_cast _ _ _ hzero₁, MLPSpec.evalPrefix_zero,
      MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ (Fin.castSucc_zero :
        (0 : Fin (L₁ + 1)).castSucc = 0), MLPSpec.evalPrefix_zero]
    exact congrArg x (Fin.ext rfl)
  | succ k ih =>
    let i : Fin (L₁ + L₂ + 1) := ⟨k.val, by omega⟩
    have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i =
        (reluSpec d₁).layerActivation k.castSucc :=
      layerActivation_reluSpec_eq _ _ (by simp [i]; omega)
    have hsucc : (⟨k.succ.val, by omega⟩ : Fin (L₁ + L₂ + 2)) = i.succ := Fin.ext rfl
    have hk_cast : k.succ.castSucc = k.castSucc.succ := Fin.ext rfl
    rw [MLPSpec.evalPrefix_cast _ _ _ hsucc, MLPSpec.evalPrefix_succ_apply, hlayer,
      MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ hk_cast, MLPSpec.evalPrefix_succ_apply]
    apply congrArg ((reluSpec d₁).layerActivation k.castSucc)
    obtain ⟨hW, hb⟩ := compParams_lt hm₁ hm₂ θ₁ θ₂ k
    dsimp only [i]
    simp only [Matrix.mulVec, dotProduct, hW, hb]
    congr 1
    let hc : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.castSucc :=
      width_compWidths_of_le d₁ d₂ (by simp [i]) rfl
    refine Fintype.sum_equiv (finCongr hc) _ _ fun c => ?_
    simp only [finCongr_apply]
    congr 1
    exact ih c

private theorem compParams_evalPrefix_mid {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    (h0c : (reluSpec (compWidths d₁ d₂)).width 0 = n)
    (h0₁ : (reluSpec d₁).width 0 = n)
    (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m) (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (g : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ)
    (hθ₁ : ∀ k : Fin m,
      (reluSpec d₁).realize θ₁ (fun i => x (Fin.cast h0₁ i)) (Fin.cast hm₁.symm k) = g x k)
    (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1, by omega⟩)) :
    (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
        (fun i => x (Fin.cast h0c i)) ⟨L₁ + 1, by omega⟩ r =
      (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂ u)) 1
        (Fin.cast (width_compWidths_of_lt d₁ d₂ (by simp) (by simp)) r) := by
  let i_mid : Fin (L₁ + L₂ + 1) := ⟨L₁, by omega⟩
  have hsucc_mid : (⟨L₁ + 1, by omega⟩ : Fin (L₁ + L₂ + 2)) = i_mid.succ := Fin.ext rfl
  have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i_mid =
      (reluSpec d₂).layerActivation 0 :=
    layerActivation_reluSpec_eq _ _ (by simp [i_mid]; omega)
  have h1_succ : (1 : Fin (L₂ + 2)) = (0 : Fin (L₂ + 1)).succ := Fin.ext rfl
  have h0₂ : (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂ u))
      (0 : Fin (L₂ + 1)).castSucc = fun u => g x (Fin.cast hm₂ u) := by simp
  rw [MLPSpec.evalPrefix_cast _ _ _ hsucc_mid, MLPSpec.evalPrefix_succ_apply, hlayer,
    MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ h1_succ,
    MLPSpec.evalPrefix_succ_apply, h0₂]
  apply congrArg ((reluSpec d₂).layerActivation 0)
  have hr_mid : (reluSpec (compWidths d₁ d₂)).width i_mid.succ =
      (reluSpec d₂).width (0 : Fin (L₂ + 1)).succ :=
    width_compWidths_of_lt d₁ d₂ (by simp [i_mid]) (by simp [i_mid])
  have hc_mid : (reluSpec (compWidths d₁ d₂)).width i_mid.castSucc =
      (reluSpec d₁).width (Fin.last L₁).castSucc :=
    width_compWidths_of_le d₁ d₂ (by simp [i_mid]) (by simp [i_mid])
  obtain ⟨hW, hb⟩ := compParams_eq hm₁ hm₂ θ₁ θ₂ hr_mid hc_mid
  dsimp only [i_mid]
  simp only [Matrix.mulVec, dotProduct, hW, hb]
  rw [← add_assoc]
  congr 1
  -- Swap sums over input coordinates `c` and merge coordinates `k`
  -- using `compParams_evalPrefix_lt`.
  have hlhs_swap :
      (∑ c : Fin ((reluSpec (compWidths d₁ d₂)).width i_mid.castSucc),
          (∑ k : Fin m, (θ₂ 0).1
              (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r)) (Fin.cast hm₂.symm k) *
              (θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc_mid c)) *
            (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
              (fun i => x (Fin.cast h0c i)) i_mid.castSucc c) =
        ∑ k : Fin m, ∑ c : Fin ((reluSpec (compWidths d₁ d₂)).width i_mid.castSucc),
          (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r))
              (Fin.cast hm₂.symm k) *
            ((θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc_mid c) *
              (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i))
                (Fin.last L₁).castSucc (Fin.cast hc_mid c)) := by
    refine (Finset.sum_congr rfl fun c _ => ?_).trans Finset.sum_comm
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc := compParams_evalPrefix_lt h0c h0₁ hm₁ hm₂ θ₁ θ₂ x (Fin.last L₁) c
    rw [mul_assoc]
    congr 2
  rw [hlhs_swap, ← Finset.sum_add_distrib]
  have hsum_k : ∀ k : Fin m,
      (∑ c : Fin ((reluSpec (compWidths d₁ d₂)).width i_mid.castSucc),
          (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r))
              (Fin.cast hm₂.symm k) *
            ((θ₁ (Fin.last L₁)).1 (Fin.cast hm₁.symm k) (Fin.cast hc_mid c) *
              (reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i))
                (Fin.last L₁).castSucc (Fin.cast hc_mid c))) +
        (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r))
            (Fin.cast hm₂.symm k) *
          (θ₁ (Fin.last L₁)).2 (Fin.cast hm₁.symm k) =
      (θ₂ 0).1 (Fin.cast hr_mid (Fin.cast (congrArg _ hsucc_mid) r)) (Fin.cast hm₂.symm k) *
        g x k := by
    intro k
    rw [← Finset.mul_sum, ← mul_add]
    congr 1
    have hk := hθ₁ k
    rw [MLPSpec.realize_succ] at hk
    rw [← hk]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    congr 1
    refine Fintype.sum_equiv (finCongr hc_mid) _ _ fun c => ?_
    simp [finCongr_apply]
  refine (Finset.sum_congr rfl fun k _ => hsum_k k).trans ?_
  refine Fintype.sum_equiv (finCongr hm₂.symm) _ _ fun k => ?_
  simp [finCongr_apply]

private theorem compParams_evalPrefix_gt {n m L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    (h0c : (reluSpec (compWidths d₁ d₂)).width 0 = n)
    (h0₁ : (reluSpec d₁).width 0 = n)
    (hm₁ : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m) (hm₂ : (reluSpec d₂).width 0 = m)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters)
    (g : (Fin n → ℝ) → (Fin m → ℝ)) (x : Fin n → ℝ)
    (hθ₁ : ∀ k : Fin m,
      (reluSpec d₁).realize θ₁ (fun i => x (Fin.cast h0₁ i)) (Fin.cast hm₁.symm k) = g x k)
    (k : Fin (L₂ + 1))
    (r : Fin ((reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1 + k.val, by omega⟩)) :
    (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁ hm₂ θ₁ θ₂)
        (fun i => x (Fin.cast h0c i)) ⟨L₁ + 1 + k.val, by omega⟩ r =
      (reluSpec d₂).evalPrefix θ₂ (fun u => g x (Fin.cast hm₂ u)) k.succ
        (Fin.cast (width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp; omega)) r) := by
  induction k using Fin.induction with
  | zero =>
    exact compParams_evalPrefix_mid h0c h0₁ hm₁ hm₂ θ₁ θ₂ g x hθ₁ r
  | succ k ih =>
    let i : Fin (L₁ + L₂ + 1) := ⟨L₁ + 1 + k.val, by omega⟩
    have hsucc : (⟨L₁ + 1 + k.succ.val, by omega⟩ : Fin (L₁ + L₂ + 2)) = i.succ :=
      Fin.ext (by simp [i]; omega)
    have hlayer : (reluSpec (compWidths d₁ d₂)).layerActivation i =
        (reluSpec d₂).layerActivation k.succ :=
      layerActivation_reluSpec_eq _ _ (by simp [i]; omega)
    rw [MLPSpec.evalPrefix_cast _ _ _ hsucc, MLPSpec.evalPrefix_succ_apply, hlayer,
      MLPSpec.evalPrefix_succ_apply]
    apply congrArg ((reluSpec d₂).layerActivation k.succ)
    obtain ⟨hW, hb⟩ := compParams_gt hm₁ hm₂ θ₁ θ₂ k
    dsimp only [i]
    simp only [Matrix.mulVec, dotProduct, hW, hb]
    congr 1
    have hcast_c : (reluSpec (compWidths d₁ d₂)).width i.castSucc =
        (reluSpec d₂).width k.succ.castSucc :=
      width_compWidths_of_lt d₁ d₂ (by simp [i]; omega) (by simp [i]; omega)
    refine Fintype.sum_equiv (finCongr hcast_c) _ _ fun c => ?_
    simp only [finCongr_apply]
    congr 1
    exact ih c

/-- Merging the affine output layer of a depth-`(L₁ + 1)` network realizing `g` with the affine
input layer of a depth-`(L₂ + 1)` network realizing `h` gives a depth-`(L₁ + L₂ + 1)` network
realizing `h ∘ g`. -/
theorem ReLUNetRealizes.comp {n m p L₁ L₂ : ℕ}
    {d₁ : Fin (L₁ + 2) → ℕ} {d₂ : Fin (L₂ + 2) → ℕ}
    {g : (Fin n → ℝ) → (Fin m → ℝ)} {h : (Fin m → ℝ) → (Fin p → ℝ)}
    (hg : ReLUNetRealizes d₁ g) (hh : ReLUNetRealizes d₂ h) :
    ReLUNetRealizes (compWidths d₁ d₂) (h ∘ g) := by
  -- Track `evalPrefix` in three stages: `compParams_evalPrefix_lt` below `L₁`,
  -- `compParams_evalPrefix_mid` at the merged affine layer `L₁ + 1`, and
  -- `compParams_evalPrefix_gt` from `L₁ + 1` to the output.
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := hg
  obtain ⟨hm₂, hp₂, θ₂, hθ₂⟩ := hh
  have h0₁' : (reluSpec d₁).width 0 = n := (congrFun (reluSpec_width d₁) 0).trans h0₁
  have hm₁' : (reluSpec d₁).width (Fin.last (L₁ + 1)) = m :=
    (congrFun (reluSpec_width d₁) (Fin.last (L₁ + 1))).trans hm₁
  have hm₂' : (reluSpec d₂).width 0 = m := (congrFun (reluSpec_width d₂) 0).trans hm₂
  have hp₂' : (reluSpec d₂).width (Fin.last (L₂ + 1)) = p :=
    (congrFun (reluSpec_width d₂) (Fin.last (L₂ + 1))).trans hp₂
  have h0c : compWidths d₁ d₂ 0 = n := by simp [h0₁]
  have h0c' : (reluSpec (compWidths d₁ d₂)).width 0 = n :=
    (congrFun (reluSpec_width _) 0).trans h0c
  have hpc : compWidths d₁ d₂ (Fin.last (L₁ + L₂ + 1)) = p := by simp [hp₂]
  have hpc' : (reluSpec (compWidths d₁ d₂)).width (Fin.last (L₁ + L₂ + 1)) = p :=
    (congrFun (reluSpec_width _) _).trans hpc
  refine ⟨h0c, hpc, compParams hm₁' hm₂' θ₁ θ₂, fun x j => ?_⟩
  have hθ₁' : ∀ k : Fin m,
      (reluSpec d₁).realize θ₁ (fun i => x (Fin.cast h0₁' i)) (Fin.cast hm₁'.symm k) = g x k :=
    fun k => hθ₁ x k
  have hlast_idx : (Fin.last (L₁ + L₂ + 1) : Fin (L₁ + L₂ + 2)) =
      ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ := Fin.ext (by simp; omega)
  have hp_eq :
      (reluSpec (compWidths d₁ d₂)).width ⟨L₁ + 1 + (Fin.last L₂).val, by omega⟩ = p :=
    (width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp; omega)).trans hp₂'
  have hlast := compParams_evalPrefix_gt h0c' h0₁' hm₁' hm₂' θ₁ θ₂ g x hθ₁' (Fin.last L₂)
    (Fin.cast hp_eq.symm j)
  have hrealize_eq :
      (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁' hm₂' θ₁ θ₂)
          (fun i => x (Fin.cast h0c i)) (Fin.last (L₁ + L₂ + 1)) (Fin.cast hpc.symm j) =
        (reluSpec (compWidths d₁ d₂)).evalPrefix (compParams hm₁' hm₂' θ₁ θ₂)
          (fun i => x (Fin.cast h0c' i)) (Fin.last (L₁ + L₂ + 1)) (Fin.cast hpc'.symm j) :=
    rfl
  rw [MLPSpec.realize_def]
  refine hrealize_eq.trans ?_
  rw [MLPSpec.evalPrefix_cast _ _ _ hlast_idx]
  have h_eq : Fin.cast (congrArg (reluSpec (compWidths d₁ d₂)).width hlast_idx)
      (Fin.cast hpc'.symm j) = Fin.cast hp_eq.symm j :=
    Fin.ext (by simp only [Fin.val_cast])
  rw [h_eq, hlast]
  have hlast_eq : (Fin.last L₂).succ = Fin.last (L₂ + 1) := Fin.succ_last L₂
  rw [MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ hlast_eq, ← MLPSpec.realize_def]
  have hcast_p : Fin.cast (congrArg (reluSpec d₂).width hlast_eq)
      (Fin.cast (width_compWidths_of_lt d₁ d₂ (by simp; omega) (by simp; omega))
        (Fin.cast hp_eq.symm j)) = Fin.cast hp₂'.symm j :=
    Fin.ext (by simp only [Fin.val_cast])
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

/-- A depth-1 ReLU network realizes `f` if a weight matrix and bias satisfy `W *ᵥ x + b = f x`. -/
private theorem reluNetRealizes_depth_one {a b : ℕ}
    (W : Matrix (Fin b) (Fin a) ℝ) (b₀ : Fin b → ℝ)
    (f : (Fin a → ℝ) → (Fin b → ℝ))
    (hf : ∀ x j, (W *ᵥ x + b₀) j = f x j) :
    ReLUNetRealizes ![a, b] f := by
  let θ : (reluSpec ![a, b]).Parameters := Fin.cons (W, b₀) fun i => i.elim0
  refine ⟨rfl, rfl, θ, fun x j => ?_⟩
  rw [MLPSpec.realize_depth_one]
  exact hf x j

/-- Every continuous affine map `(Fin n → ℝ) →ᴬ[ℝ] (Fin m → ℝ)` is realized by a ReLU
network of depth `1` with widths `![n, m]`. -/
theorem ReLUNetRealizes.of_continuousAffineMap {n m : ℕ}
    (A : (Fin n → ℝ) →ᴬ[ℝ] (Fin m → ℝ)) :
    ReLUNetRealizes ![n, m] A :=
  reluNetRealizes_depth_one (LinearMap.toMatrix' A.contLinear.toLinearMap) (A 0) A fun x j => by
    rw [Pi.add_apply, LinearMap.toMatrix'_mulVec]
    exact congrFun (congrFun A.decomp x).symm j

/-- Every continuous affine functional `(Fin n → ℝ) →ᴬ[ℝ] ℝ` is computed by a ReLU
network of depth `1` with widths `![n, 1]`. -/
theorem ReLUNetComputes.of_continuousAffineMap {n : ℕ} (A : (Fin n → ℝ) →ᴬ[ℝ] ℝ) :
    ReLUNetComputes ![n, 1] A := by
  let e : ℝ →ᴬ[ℝ] (Fin 1 → ℝ) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.toContinuousLinearMap.toContinuousAffineMap
  exact reluNetComputes_iff_reluNetRealizes.mpr (ReLUNetRealizes.of_continuousAffineMap (e.comp A))

/-! ### Parallel stacking and affine combinations -/

private abbrev finAppendWidths {L : ℕ} (n : ℕ) (d₁ d₂ : Fin (L + 2) → ℕ) :
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
  if hi : i = 0 then
    have hr : (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
        (reluSpec d₁).width (0 : Fin (L + 1)).succ +
          (reluSpec d₂).width (0 : Fin (L + 1)).succ := by
      subst hi; exact finAppendWidths_succ n d₁ d₂ 0
    have hc : (reluSpec (finAppendWidths n d₁ d₂)).width i.castSucc = n := by
      subst hi; exact finAppendWidths_zero n d₁ d₂
    (fun r c => Fin.addCases
        (fun r₁ => (θ₁ 0).1 r₁ (Fin.cast h0₁.symm (Fin.cast hc c)))
        (fun r₂ => (θ₂ 0).1 r₂ (Fin.cast h0₂.symm (Fin.cast hc c)))
        (Fin.cast hr r),
     fun r => Fin.addCases (θ₁ 0).2 (θ₂ 0).2 (Fin.cast hr r))
  else
    let k : Fin L := ⟨i.val - 1, by have := Fin.pos_iff_ne_zero.mpr hi; omega⟩
    have hi_eq : i = k.succ := Fin.ext (by simp [k]; have := Fin.pos_iff_ne_zero.mpr hi; omega)
    have hr : (reluSpec (finAppendWidths n d₁ d₂)).width i.succ =
        (reluSpec d₁).width k.succ.succ + (reluSpec d₂).width k.succ.succ := by
      rw [hi_eq]; exact finAppendWidths_succ n d₁ d₂ k.succ
    have hc : (reluSpec (finAppendWidths n d₁ d₂)).width i.castSucc =
        (reluSpec d₁).width k.castSucc.succ + (reluSpec d₂).width k.castSucc.succ := by
      rw [hi_eq]; exact finAppendWidths_succ n d₁ d₂ k.castSucc
    (fun r c => Fin.addCases
        (fun r₁ => Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0) (Fin.cast hc c))
        (fun r₂ => Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂) (Fin.cast hc c))
        (Fin.cast hr r),
     fun r => Fin.addCases (θ₁ k.succ).2 (θ₂ k.succ).2 (Fin.cast hr r))

private theorem finAppendParams_zero {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) :
    (∀ r c, (finAppendParams h0₁ h0₂ θ₁ θ₂ 0).1 r c =
      Fin.addCases
        (fun r₁ => (θ₁ 0).1 r₁ (Fin.cast h0₁.symm (Fin.cast (finAppendWidths_zero n d₁ d₂) c)))
        (fun r₂ => (θ₂ 0).1 r₂ (Fin.cast h0₂.symm (Fin.cast (finAppendWidths_zero n d₁ d₂) c)))
        (Fin.cast (finAppendWidths_succ n d₁ d₂ 0) r)) ∧
    (∀ r, (finAppendParams h0₁ h0₂ θ₁ θ₂ 0).2 r =
      Fin.addCases (θ₁ 0).2 (θ₂ 0).2 (Fin.cast (finAppendWidths_succ n d₁ d₂ 0) r)) :=
  ⟨fun r c => by simp only [finAppendParams, ↓reduceDIte]; rfl,
   fun r => by simp only [finAppendParams, ↓reduceDIte]⟩

private theorem finAppendParams_succ {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (k : Fin L) :
    (∀ r c, (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 r c =
      Fin.addCases
        (fun r₁ => Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0)
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
        (fun r₂ => Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂)
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
        (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r)) ∧
    (∀ r, (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).2 r =
      Fin.addCases (θ₁ k.succ).2 (θ₂ k.succ).2
        (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r)) := by
  have hk_ne : k.succ ≠ 0 := Fin.succ_ne_zero k
  have hfn₁ : ∀ (k' : Fin L) (_ : k' = k)
      (hr' : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ =
        (reluSpec d₁).width k'.succ.succ + (reluSpec d₂).width k'.succ.succ)
      (hc' : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc =
        (reluSpec d₁).width k'.castSucc.succ + (reluSpec d₂).width k'.castSucc.succ)
      (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ))
      (c : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc)),
      Fin.addCases (motive := fun _ => ℝ)
          (fun r₁ => Fin.addCases (motive := fun _ => ℝ)
            (fun c₁ => (θ₁ k'.succ).1 r₁ c₁) (fun _ => 0) (Fin.cast hc' c))
          (fun r₂ => Fin.addCases (motive := fun _ => ℝ)
            (fun _ => 0) (fun c₂ => (θ₂ k'.succ).1 r₂ c₂) (Fin.cast hc' c))
          (Fin.cast hr' r) =
        Fin.addCases (motive := fun _ => ℝ)
          (fun r₁ => Fin.addCases (motive := fun _ => ℝ)
            (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0)
            (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
          (fun r₂ => Fin.addCases (motive := fun _ => ℝ)
            (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂)
            (Fin.cast (finAppendWidths_succ n d₁ d₂ k.castSucc) c))
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r) := by
    rintro _ rfl _ _ _ _
    rfl
  have hfn₂ : ∀ (k' : Fin L) (_ : k' = k)
      (hr' : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ =
        (reluSpec d₁).width k'.succ.succ + (reluSpec d₂).width k'.succ.succ)
      (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ.succ)),
      Fin.addCases (motive := fun _ => ℝ) (θ₁ k'.succ).2 (θ₂ k'.succ).2 (Fin.cast hr' r) =
        Fin.addCases (motive := fun _ => ℝ) (θ₁ k.succ).2 (θ₂ k.succ).2
          (Fin.cast (finAppendWidths_succ n d₁ d₂ k.succ) r) := by
    rintro _ rfl _ _
    rfl
  refine ⟨fun r c => ?_, fun r => ?_⟩
  · simp only [finAppendParams, hk_ne, ↓reduceDIte]
    exact hfn₁ ⟨k.succ.val - 1, _⟩ (Fin.ext (by simp)) _ _ r c
  · simp only [finAppendParams, hk_ne, ↓reduceDIte]
    exact hfn₂ ⟨k.succ.val - 1, _⟩ (Fin.ext (by simp)) _ r

private theorem finAppend_zero_step {n L : ℕ} {d dₐ : Fin (L + 2) → ℕ}
    (hd0 : (reluSpec d).width 0 = n) (h0ₐ : (reluSpec dₐ).width 0 = n)
    (θ : (reluSpec d).Parameters) (θₐ : (reluSpec dₐ).Parameters)
    (x : Fin n → ℝ) (r : Fin ((reluSpec d).width (0 : Fin (L + 1)).succ))
    (rₐ : Fin ((reluSpec dₐ).width (0 : Fin (L + 1)).succ))
    (hW : ∀ c, (θ 0).1 r c =
      (θₐ 0).1 rₐ (Fin.cast h0ₐ.symm (Fin.cast hd0 c)))
    (hb : (θ 0).2 r = (θₐ 0).2 rₐ) :
    (reluSpec d).evalPrefix θ (fun i => x (Fin.cast hd0 i)) (0 : Fin (L + 1)).succ r =
      (reluSpec dₐ).evalPrefix θₐ (fun i => x (Fin.cast h0ₐ i)) (0 : Fin (L + 1)).succ rₐ := by
  have h0 : (reluSpec d).evalPrefix θ (fun i => x (Fin.cast hd0 i)) (0 : Fin (L + 1)).castSucc =
      fun i => x (Fin.cast hd0 i) := by simp
  have h0ₐ' : (reluSpec dₐ).evalPrefix θₐ (fun i => x (Fin.cast h0ₐ i))
      (0 : Fin (L + 1)).castSucc = fun i => x (Fin.cast h0ₐ i) := by simp
  rw [MLPSpec.evalPrefix_succ_apply, MLPSpec.evalPrefix_succ_apply, h0, h0ₐ',
    layerActivation_reluSpec_eq d dₐ Iff.rfl]
  congr 1
  simp only [Matrix.mulVec, dotProduct, hW, hb]
  congr 1
  refine Fintype.sum_equiv ((finCongr hd0).trans (finCongr h0ₐ).symm) _ _ fun c => ?_
  simp [finCongr_apply]

private theorem dotProduct_cast_addCases {w₁ w₂ w : ℕ} (hw : w = w₁ + w₂)
    (f₁ : Fin w₁ → ℝ) (f₂ : Fin w₂ → ℝ) (v : Fin w → ℝ) :
    (fun c => Fin.addCases f₁ f₂ (Fin.cast hw c)) ⬝ᵥ v =
      (∑ c₁ : Fin w₁, f₁ c₁ * v (Fin.cast hw.symm (Fin.castAdd w₂ c₁))) +
      (∑ c₂ : Fin w₂, f₂ c₂ * v (Fin.cast hw.symm (Fin.natAdd w₁ c₂))) := by
  simp only [dotProduct]
  rw [← Equiv.sum_comp (finCongr hw).symm, Fin.sum_univ_add]
  simp [finCongr_apply]

private theorem finAppend_succ_step {L : ℕ} {d dₐ : Fin (L + 2) → ℕ}
    (k : Fin L) (θ : (reluSpec d).Parameters) (θₐ : (reluSpec dₐ).Parameters)
    (x₀ : Fin ((reluSpec d).width 0) → ℝ) (xₐ : Fin ((reluSpec dₐ).width 0) → ℝ)
    (r : Fin ((reluSpec d).width k.succ.succ)) (rₐ : Fin ((reluSpec dₐ).width k.succ.succ))
    (hdot : (θ k.succ).1 r ⬝ᵥ (reluSpec d).evalPrefix θ x₀ k.succ.castSucc =
      (θₐ k.succ).1 rₐ ⬝ᵥ (reluSpec dₐ).evalPrefix θₐ xₐ k.succ.castSucc)
    (hb : (θ k.succ).2 r = (θₐ k.succ).2 rₐ) :
    (reluSpec d).evalPrefix θ x₀ k.succ.succ r =
      (reluSpec dₐ).evalPrefix θₐ xₐ k.succ.succ rₐ := by
  rw [MLPSpec.evalPrefix_succ_apply, MLPSpec.evalPrefix_succ_apply,
    layerActivation_reluSpec_eq d dₐ Iff.rfl]
  congr 1
  simp only [Matrix.mulVec]
  rw [hdot, hb]

private theorem finAppendParams_evalPrefix {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
    (h0₁ : (reluSpec d₁).width 0 = n) (h0₂ : (reluSpec d₂).width 0 = n)
    (θ₁ : (reluSpec d₁).Parameters) (θ₂ : (reluSpec d₂).Parameters) (x : Fin n → ℝ)
    (k : Fin (L + 1)) (r : Fin ((reluSpec (finAppendWidths n d₁ d₂)).width k.succ)) :
    (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁ h0₂ θ₁ θ₂)
        (fun i => x (Fin.cast (finAppendWidths_zero n d₁ d₂) i)) k.succ r =
      Fin.append
        ((reluSpec d₁).evalPrefix θ₁ (fun i => x (Fin.cast h0₁ i)) k.succ)
        ((reluSpec d₂).evalPrefix θ₂ (fun i => x (Fin.cast h0₂ i)) k.succ)
        (Fin.cast (finAppendWidths_succ n d₁ d₂ k) r) := by
  have hd0 := finAppendWidths_zero n d₁ d₂
  have hd_succ := finAppendWidths_succ n d₁ d₂
  induction k using Fin.induction with
  | zero =>
    obtain ⟨hW0, hb0⟩ := finAppendParams_zero h0₁ h0₂ θ₁ θ₂
    cases hrc : Fin.cast (hd_succ 0) r using Fin.addCases with
    | left r₁ =>
      rw [Fin.append_left]
      exact finAppend_zero_step hd0 h0₁ (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₁ x r r₁
        (fun c => by rw [hW0, hrc, Fin.addCases_left])
        (by rw [hb0, hrc, Fin.addCases_left])
    | right r₂ =>
      rw [Fin.append_right]
      exact finAppend_zero_step hd0 h0₂ (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₂ x r r₂
        (fun c => by rw [hW0, hrc, Fin.addCases_right])
        (by rw [hb0, hrc, Fin.addCases_right])
  | succ k ih =>
    obtain ⟨hWk, hbk⟩ := finAppendParams_succ h0₁ h0₂ θ₁ θ₂ k
    have hcast_w : (reluSpec (finAppendWidths n d₁ d₂)).width k.succ.castSucc =
        (reluSpec d₁).width k.castSucc.succ + (reluSpec d₂).width k.castSucc.succ :=
      hd_succ k.castSucc
    have hk_cast : k.succ.castSucc = k.castSucc.succ := Fin.ext rfl
    cases hrc : Fin.cast (hd_succ k.succ) r using Fin.addCases with
    | left r₁ =>
      rw [Fin.append_left]
      refine finAppend_succ_step k (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₁
        (fun i => x (Fin.cast hd0 i)) (fun i => x (Fin.cast h0₁ i)) r r₁ ?_
        (by simp [hbk, hrc])
      have hrow : (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 r = fun c =>
          Fin.addCases (fun c₁ => (θ₁ k.succ).1 r₁ c₁) (fun _ => 0) (Fin.cast hcast_w c) := by
        ext c
        simp [hWk, hrc]
      rw [hrow, dotProduct_cast_addCases hcast_w]
      simp only [zero_mul, Finset.sum_const_zero, add_zero, dotProduct]
      refine Finset.sum_congr rfl fun c₁ _ => ?_
      congr 1
      have hidx_eq : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hk_cast)
          (Fin.cast hcast_w.symm (Fin.castAdd ((reluSpec d₂).width k.castSucc.succ) c₁)) =
          Fin.cast (hd_succ k.castSucc).symm
            (Fin.castAdd ((reluSpec d₂).width k.castSucc.succ) c₁) :=
        Fin.ext (by simp only [Fin.val_cast])
      rw [MLPSpec.evalPrefix_cast _ (finAppendParams h0₁ h0₂ θ₁ θ₂) _ hk_cast, hidx_eq, ih,
        Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_left,
        MLPSpec.evalPrefix_cast (reluSpec d₁) θ₁ _ hk_cast]
      exact congrArg _ (Fin.ext (by simp only [Fin.val_cast]))
    | right r₂ =>
      rw [Fin.append_right]
      refine finAppend_succ_step k (finAppendParams h0₁ h0₂ θ₁ θ₂) θ₂
        (fun i => x (Fin.cast hd0 i)) (fun i => x (Fin.cast h0₂ i)) r r₂ ?_
        (by simp [hbk, hrc])
      have hrow : (finAppendParams h0₁ h0₂ θ₁ θ₂ k.succ).1 r = fun c =>
          Fin.addCases (fun _ => 0) (fun c₂ => (θ₂ k.succ).1 r₂ c₂) (Fin.cast hcast_w c) := by
        ext c
        simp [hWk, hrc]
      rw [hrow, dotProduct_cast_addCases hcast_w]
      simp only [zero_mul, Finset.sum_const_zero, zero_add, dotProduct]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      congr 1
      have hidx_eq : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hk_cast)
          (Fin.cast hcast_w.symm (Fin.natAdd ((reluSpec d₁).width k.castSucc.succ) c₂)) =
          Fin.cast (hd_succ k.castSucc).symm
            (Fin.natAdd ((reluSpec d₁).width k.castSucc.succ) c₂) :=
        Fin.ext (by simp only [Fin.val_cast])
      rw [MLPSpec.evalPrefix_cast _ (finAppendParams h0₁ h0₂ θ₁ θ₂) _ hk_cast, hidx_eq, ih,
        Fin.cast_cast, Fin.cast_refl, id_eq, Fin.append_right,
        MLPSpec.evalPrefix_cast (reluSpec d₂) θ₂ _ hk_cast]
      exact congrArg _ (Fin.ext (by simp only [Fin.val_cast]))

/-- Stacking two ReLU networks of the same positive depth `L + 1` in parallel yields a network of
depth `L + 1` with hidden widths `d₁ i + d₂ i` realizing
`fun x => Fin.append (f₁ x) (f₂ x)`. -/
theorem ReLUNetRealizes.finAppend {n m₁ m₂ L : ℕ}
    {d₁ d₂ : Fin (L + 2) → ℕ}
    {f₁ : (Fin n → ℝ) → (Fin m₁ → ℝ)} {f₂ : (Fin n → ℝ) → (Fin m₂ → ℝ)}
    (hf₁ : ReLUNetRealizes d₁ f₁) (hf₂ : ReLUNetRealizes d₂ f₂) :
    ReLUNetRealizes (fun i : Fin (L + 2) => if i = 0 then n else d₁ i + d₂ i)
      (fun x => Fin.append (f₁ x) (f₂ x)) := by
  obtain ⟨h0₁, hm₁, θ₁, hθ₁⟩ := hf₁
  obtain ⟨h0₂, hm₂, θ₂, hθ₂⟩ := hf₂
  have h0₁' : (reluSpec d₁).width 0 = n := (congrFun (reluSpec_width d₁) 0).trans h0₁
  have h0₂' : (reluSpec d₂).width 0 = n := (congrFun (reluSpec_width d₂) 0).trans h0₂
  have hm₁' : (reluSpec d₁).width (Fin.last L).succ = m₁ :=
    (congrFun (reluSpec_width d₁) (Fin.last (L + 1))).trans hm₁
  have hm₂' : (reluSpec d₂).width (Fin.last L).succ = m₂ :=
    (congrFun (reluSpec_width d₂) (Fin.last (L + 1))).trans hm₂
  have hd0' : finAppendWidths n d₁ d₂ 0 = n := by simp
  have hd0 := finAppendWidths_zero n d₁ d₂
  have hdL : finAppendWidths n d₁ d₂ (Fin.last (L + 1)) = m₁ + m₂ := by
    simp [finAppendWidths, hm₁, hm₂]
  have hdL' : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last (L + 1)) = m₁ + m₂ :=
    (congrFun (reluSpec_width _) _).trans hdL
  have hd_succ := finAppendWidths_succ n d₁ d₂
  refine ⟨hd0', hdL, finAppendParams h0₁' h0₂' θ₁ θ₂, fun x j => ?_⟩
  have hm_eq : (reluSpec (finAppendWidths n d₁ d₂)).width (Fin.last L).succ = m₁ + m₂ := by
    simp [finAppendWidths, hm₁, hm₂]
  have hlast := finAppendParams_evalPrefix h0₁' h0₂' θ₁ θ₂ x (Fin.last L) (Fin.cast hm_eq.symm j)
  have hlast_eq : (Fin.last (L + 1) : Fin (L + 2)) = (Fin.last L).succ := Fin.ext rfl
  have hrealize_eq :
      (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁' h0₂' θ₁ θ₂)
          (fun i => x (Fin.cast hd0' i)) (Fin.last (L + 1)) (Fin.cast hdL.symm j) =
        (reluSpec (finAppendWidths n d₁ d₂)).evalPrefix (finAppendParams h0₁' h0₂' θ₁ θ₂)
          (fun i => x (Fin.cast hd0 i)) (Fin.last (L + 1)) (Fin.cast hdL'.symm j) :=
    rfl
  rw [MLPSpec.realize_def]
  refine hrealize_eq.trans ?_
  rw [MLPSpec.evalPrefix_cast _ _ _ hlast_eq]
  have hcast_j : Fin.cast (congrArg (reluSpec (finAppendWidths n d₁ d₂)).width hlast_eq)
      (Fin.cast hdL'.symm j) = Fin.cast hm_eq.symm j :=
    Fin.ext (by simp only [Fin.val_cast])
  rw [hcast_j, hlast]
  dsimp only
  cases j using Fin.addCases with
  | left j₁ =>
    have hidx : Fin.cast (hd_succ (Fin.last L)) (Fin.cast hm_eq.symm (Fin.castAdd m₂ j₁)) =
        Fin.castAdd ((reluSpec d₂).width (Fin.last L).succ) (Fin.cast hm₁'.symm j₁) :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_castAdd])
    rw [hidx, Fin.append_left, Fin.append_left,
      MLPSpec.evalPrefix_cast (reluSpec d₁) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₁ x j₁
  | right j₂ =>
    have hidx : Fin.cast (hd_succ (Fin.last L)) (Fin.cast hm_eq.symm (Fin.natAdd m₁ j₂)) =
        Fin.natAdd ((reluSpec d₁).width (Fin.last L).succ) (Fin.cast hm₂'.symm j₂) :=
      Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd, hm₁'])
    rw [hidx, Fin.append_right, Fin.append_right,
      MLPSpec.evalPrefix_cast (reluSpec d₂) _ _ hlast_eq.symm, ← MLPSpec.realize_def]
    exact hθ₂ x j₂

/-- Parallel affine combination of two ReLU networks of the same positive depth `L + 1`: if `d₁`
computes `f₁` and `d₂` computes `f₂`, then a network of depth `L + 1` with hidden widths
`d₁ i + d₂ i` computes `fun x => a * f₁ x + b * f₂ x + c`. -/
theorem ReLUNetComputes.affineComb {n L : ℕ} {d₁ d₂ : Fin (L + 2) → ℕ}
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
  refine ⟨rfl, rfl, θ, fun x j => ?_⟩
  have h1 : ∀ (x₀ : Fin ((reluSpec ![a, b, c]).width 0) → ℝ),
      (∀ i, x₀ i = x (Fin.cast ha i)) → ∀ (k : Fin b),
      (reluSpec ![a, b, c]).evalPrefix θ x₀ (0 : Fin 2).succ (Fin.cast hb.symm k) =
        max 0 ((W₀ *ᵥ x) k + b₀ k) := fun x₀ hx₀ k => by
    have h0 : (reluSpec ![a, b, c]).evalPrefix θ x₀ (0 : Fin 2).castSucc = x₀ := by simp
    rw [MLPSpec.evalPrefix_succ_apply, (reluSpec ![a, b, c]).layerActivation_of_lt 0 (by decide),
      h0, reluSpec_activation]
    congr 1
    simp only [θ, Fin.cons_zero, Matrix.mulVec, dotProduct]
    congr 1
    refine Fintype.sum_equiv (finCongr ha) _ _ fun i => ?_
    simp only [hx₀, finCongr_apply]
    rfl
  rw [MLPSpec.realize_succ]
  -- Unfold `(θ (Fin.last 1))` and `mulVec`/`dotProduct` at depth 2 with `h0 = rfl`, `hc = rfl`.
  have hlhs : ∀ (x₀ : Fin ((reluSpec ![a, b, c]).width 0) → ℝ),
      ((θ (Fin.last 1)).1 *ᵥ (reluSpec ![a, b, c]).evalPrefix θ x₀ (Fin.last 1).castSucc +
        (θ (Fin.last 1)).2) (Fin.cast (rfl : ![a, b, c] (Fin.last 2) = c).symm j) =
      (∑ k : Fin b, W₁ j k * (reluSpec ![a, b, c]).evalPrefix θ
        x₀ (0 : Fin 2).succ (Fin.cast hb.symm k)) + b₁ j := fun _ =>
    rfl
  refine (hlhs (fun i => x (Fin.cast ha i))).trans ?_
  simp_rw [h1 _ fun _ => rfl]
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
  simpa [max_comm, mul_neg_one, sub_eq_add_neg] using max_zero_sub_max_neg_zero_eq_self (x j)

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

private theorem exists_reluNetComputes_of_le_pos {n L₁ L₂ : ℕ} (hL₁ : 1 ≤ L₁) (hL : L₁ ≤ L₂)
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
  exists_reluNetComputes_of_le_pos (le_refl 1) hL (ReLUNetComputes.of_continuousAffineMap A)

/-- A scalar function computed at depth `L₁` is computed at every depth `L₂ ≥ L₁`. -/
theorem exists_reluNetComputes_of_le {n L₁ L₂ : ℕ} (hL : L₁ ≤ L₂)
    {d₁ : Fin (L₁ + 1) → ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d₁ f) :
    ∃ d₂ : Fin (L₂ + 1) → ℕ, ReLUNetComputes d₂ f := by
  rcases Nat.eq_zero_or_pos L₁ with rfl | hL₁
  · rcases Nat.eq_zero_or_pos L₂ with rfl | hL₂
    · exact ⟨d₁, hf⟩
    · obtain ⟨h0, h1, θ, hθ⟩ := hf
      have hn : n = 1 := h0.symm.trans h1
      subst hn
      have haff : f =
          ⇑((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 1)).toContinuousAffineMap) := by
        ext x
        have hx := (hθ x).symm
        rw [MLPSpec.realize_depth_zero] at hx
        simpa [Fin.eq_zero] using hx
      rw [haff]
      exact exists_reluNetComputes_of_continuousAffineMap hL₂ _
  · exact exists_reluNetComputes_of_le_pos hL₁ hL hf

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
    have h0' : (reluSpec d).width 0 = n := (congrFun (reluSpec_width d) 0).trans h0
    have hL' : (reluSpec d).width (Fin.last 1) = 1 :=
      (congrFun (reluSpec_width d) (Fin.last 1)).trans hL
    let M : Matrix (Fin 1) (Fin n) ℝ := (θ 0).1.reindex (finCongr hL') (finCongr h0')
    let Lmap : (Fin n → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearMap.comp
        (LinearMap.toContinuousLinearMap (Matrix.toLin' M))
    refine ⟨Lmap.toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (Fin n → ℝ) ((θ 0).2 (Fin.cast hL'.symm 0)), ?_⟩
    ext x
    have hx := (hθ x).symm
    rw [MLPSpec.realize_depth_one] at hx
    refine hx.trans ?_
    simp only [Lmap, M, ContinuousAffineMap.add_apply,
      ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousAffineMap.coe_const,
      Function.const_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_funUnique, Function.eval, Fin.default_eq_zero,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Pi.add_apply, Matrix.mulVec,
      dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply]
    congr 1
    refine Fintype.sum_equiv (finCongr h0') _ _ fun j => ?_
    simp only [finCongr_apply]
    rfl
  · rintro ⟨A, rfl⟩
    exact ⟨![n, 1], ReLUNetComputes.of_continuousAffineMap A⟩

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
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.toContinuousLinearMap.toContinuousAffineMap
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
    let Lmap := LinearMap.toContinuousLinearMap (Matrix.toLin' (θ i).1)
    have haff : IsPiecewiseAffineOn
        (fun v : Fin ((reluSpec d).width i.castSucc) → ℝ => (θ i).1 *ᵥ v + (θ i).2) univ :=
      (isPiecewiseAffineOn_continuousAffineMap
        (Lmap.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ (θ i).2)
        univ).congr fun _ _ => by
          simp [Lmap]
    have hstep := haff.comp ih (mapsTo_univ _ _)
    by_cases hlt : i.val + 1 < L
    · have hact : ∀ x, (reluSpec d).evalPrefix θ x i.succ =
          fun j => max 0 (((θ i).1 *ᵥ (reluSpec d).evalPrefix θ x i.castSucc) j + (θ i).2 j) :=
        fun x => by
          simp [MLPSpec.evalPrefix_succ, (reluSpec d).layerActivation_of_lt i hlt]
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
  have h0' : (reluSpec d).width 0 = n := (congrFun (reluSpec_width d) 0).trans h0
  have hL' : (reluSpec d).width (Fin.last L) = m :=
    (congrFun (reluSpec_width d) (Fin.last L)).trans hL
  let eIn :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ)
      (finCongr h0')).symm.toContinuousLinearMap.toContinuousAffineMap
  let eOut :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ)
      (finCongr hL')).toContinuousLinearMap.toContinuousAffineMap
  have h1 := (isPiecewiseAffineOn_reluSpec_realize d θ).comp
    (isPiecewiseAffineOn_continuousAffineMap eIn univ) (mapsTo_univ _ _)
  have h2 := (isPiecewiseAffineOn_continuousAffineMap eOut univ).comp
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
  exact (hproj.comp hvec (mapsTo_univ _ _)).congr fun _ _ => by simp

end TauCeti
