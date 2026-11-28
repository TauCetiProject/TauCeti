/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Neuromanifold.MLP.Composition

/-!
# ReLU multilayer perceptrons

A ReLU network of depth `L` with widths `d : Fin (L + 1) → ℕ` is the `Neuromanifold.MLPSpec`
`TauCeti.reluSpec d` whose every hidden activation is the scalar rectifier `t ↦ max 0 t`, with
an affine output layer.
The predicates `TauCeti.ReLUNetRealizes d f` (for `ℝⁿ → ℝᵐ`) and
`TauCeti.ReLUNetComputes d f` (for `ℝⁿ → ℝ`) assert that the input and output widths match
and some parameters realize `f`.

This file defines the ReLU MLP specification and realization predicates, establishes affine
layer realizations (`ReLUNetRealizes.of_continuousAffineMap`,
`ReLUNetComputes.of_continuousAffineMap`), and characterizes depth-zero and depth-one networks
as well as concrete depth-two realizations of the identity (`ReLUNetRealizes.id_depth_two`),
absolute value (`reluNetComputes_abs`), and binary maximum (`reluNetComputes_max`).

## References

* Raman Arora, Amitabh Basu, Poorya Mianjy, and Anirbit Mukherjee, *Understanding deep neural
  networks with rectified linear units*, ICLR 2018;
  [arXiv:1611.01491v6](https://arxiv.org/abs/1611.01491v6), Theorem 2.1 and Appendix D.
* Christoph Hertrich, Amitabh Basu, Marco Di Summa, and Martin Skutella, *Towards lower bounds on
  the depth of ReLU neural networks*, Discrete & Computational Geometry (2024);
  [arXiv:2105.14835v5](https://arxiv.org/abs/2105.14835v5), §2 and Figure 1.
-/

public section

open Matrix

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
  ReLUNetRealizes d (fun x (_ : Fin 1) => f x)

/-- A ReLU network with widths `d` realizes `f` if and only if its input and output widths match
`n` and `m` and some parameters realize `f` up to the endpoint casts. -/
theorem reluNetRealizes_iff {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} :
    ReLUNetRealizes d f ↔
      ∃ (h0 : d 0 = n) (hL : d (Fin.last L) = m) (θ : (reluSpec d).Parameters),
        ∀ x j, (reluSpec d).realize θ (fun i => x (Fin.cast h0 i)) (Fin.cast hL.symm j) = f x j :=
  Iff.rfl

/-- Scalar computation by a ReLU network is realization of the one-coordinate vector map. -/
theorem reluNetComputes_iff_reluNetRealizes {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} :
    ReLUNetComputes d f ↔ ReLUNetRealizes d (fun x (_ : Fin 1) => f x) :=
  Iff.rfl

/-- A ReLU network with widths `d` computes `f` if and only if its input width is `n`, its output
width is `1`, and some parameters realize `f` at output coordinate `0`. -/
theorem reluNetComputes_iff {n L : ℕ} {d : Fin (L + 1) → ℕ} {f : (Fin n → ℝ) → ℝ} :
    ReLUNetComputes d f ↔
      ∃ (h0 : d 0 = n) (hL : d (Fin.last L) = 1) (θ : (reluSpec d).Parameters),
        ∀ x, (reluSpec d).realize θ (fun i => x (Fin.cast h0 i)) (Fin.cast hL.symm 0) = f x := by
  simp only [reluNetComputes_iff_reluNetRealizes, reluNetRealizes_iff, Fin.forall_fin_one]

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
  (reluNetComputes_iff_reluNetRealizes.mp hf).width_zero

/-- A network computing a scalar function has output width `1`. -/
theorem ReLUNetComputes.width_last {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) : d (Fin.last L) = 1 :=
  (reluNetComputes_iff_reluNetRealizes.mp hf).width_last

/-- Transporting `ReLUNetRealizes` along equal width functions. -/
theorem ReLUNetRealizes.of_width_eq {n m L : ℕ} {d d' : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) (hd : d = d') :
    ReLUNetRealizes d' f :=
  hd ▸ hf

/-- Transporting `ReLUNetComputes` along equal width functions. -/
theorem ReLUNetComputes.of_width_eq {n L : ℕ} {d d' : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) (hd : d = d') :
    ReLUNetComputes d' f :=
  reluNetComputes_iff_reluNetRealizes.mpr
    ((reluNetComputes_iff_reluNetRealizes.mp hf).of_width_eq hd)

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

/-! ### Concrete networks and low-depth characterizations -/

private theorem reluNetRealizes_depth_two {a b c : ℕ}
    (W₀ : Matrix (Fin b) (Fin a) ℝ) (b₀ : Fin b → ℝ)
    (W₁ : Matrix (Fin c) (Fin b) ℝ) (b₁ : Fin c → ℝ)
    (f : (Fin a → ℝ) → (Fin c → ℝ))
    (hf : ∀ x j, (W₁ *ᵥ (fun k => max 0 ((W₀ *ᵥ x) k + b₀ k)) + b₁) j = f x j) :
    ReLUNetRealizes ![a, b, c] f := by
  let θ₁ : (reluSpec ![a, b, c]).tail.Parameters := Fin.cons (W₁, b₁) fun i => i.elim0
  let θ₀ : Matrix (Fin ((reluSpec ![a, b, c]).width 1)) (Fin ((reluSpec ![a, b, c]).width 0)) ℝ ×
      (Fin ((reluSpec ![a, b, c]).width 1) → ℝ) := (W₀, b₀)
  refine ⟨rfl, rfl, Fin.cons θ₀ θ₁, fun x j => ?_⟩
  let x₀ : Fin ((reluSpec ![a, b, c]).width 0) → ℝ := fun i => x (Fin.cast rfl i)
  have hact : ∀ k : Fin b,
      Neuromanifold.activation ((reluSpec ![a, b, c]).layerActivation 0) ()
        (Neuromanifold.dense θ₀ x₀) (Fin.cast rfl k) = max 0 ((W₀ *ᵥ x) k + b₀ k) := fun k => by
    rw [Neuromanifold.activation_apply, Neuromanifold.dense_apply, layerActivation_reluSpec]
    rfl
  have hreal := congrFun (congrFun (MLPSpec.realize_cons (reluSpec ![a, b, c]) θ₀ θ₁) x₀)
    (Fin.cast rfl j)
  rw [Function.comp_apply, Function.comp_apply, MLPSpec.realize_depth_one_eq_dense,
    Neuromanifold.dense_apply] at hreal
  refine hreal.trans ?_
  have hmid :
      ((θ₁ 0).1 *ᵥ Neuromanifold.activation ((reluSpec ![a, b, c]).layerActivation 0) ()
          (Neuromanifold.dense θ₀ x₀) + (θ₁ 0).2) (Fin.cast rfl j) =
        (W₁ *ᵥ (fun k => max 0 ((W₀ *ᵥ x) k + b₀ k)) + b₁) j := by
    change (W₁ *ᵥ (fun k => Neuromanifold.activation ((reluSpec ![a, b, c]).layerActivation 0) ()
        (Neuromanifold.dense θ₀ x₀) (Fin.cast rfl k)) + b₁) j = _
    simp_rw [hact]
  exact hmid.trans (hf x j)

/-- A depth-2 ReLU network of hidden width `2 * m` realizes the identity on `Fin m → ℝ` via
`t = max 0 t - max 0 (-t)`. -/
theorem ReLUNetRealizes.id_depth_two (m : ℕ) :
    ReLUNetRealizes ![m, 2 * m, m] (id : (Fin m → ℝ) → (Fin m → ℝ)) := by
  have hm : 2 * m = m + m := Nat.two_mul m
  let e : Fin (2 * m) ≃ Fin m ⊕ Fin m := (finCongr hm).trans finSumFinEquiv.symm
  let W₀ : Matrix (Fin (2 * m)) (Fin m) ℝ :=
    (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) ℝ) (-1)).submatrix e (Equiv.refl _)
  let W₁ : Matrix (Fin m) (Fin (2 * m)) ℝ :=
    (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℝ) (-1)).submatrix (Equiv.refl _) e
  refine reluNetRealizes_depth_two W₀ 0 W₁ 0 id fun x j => ?_
  have h0 : W₀ *ᵥ x = (Sum.elim x (-x)) ∘ e := by
    dsimp only [W₀]
    rw [Matrix.submatrix_mulVec_equiv]
    simp [Matrix.neg_mulVec, Matrix.one_mulVec]
  have hact : (fun k : Fin (2 * m) => max 0 ((W₀ *ᵥ x) k + (0 : Fin (2 * m) → ℝ) k)) =
      (fun s : Fin m ⊕ Fin m => max 0 (Sum.elim x (-x) s)) ∘ e := by
    funext k
    simp [h0]
  rw [hact]
  have h1 : W₁ *ᵥ ((fun s : Fin m ⊕ Fin m => max 0 (Sum.elim x (-x) s)) ∘ e) =
      (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℝ) (-1)) *ᵥ
        (fun s : Fin m ⊕ Fin m => max 0 (Sum.elim x (-x) s)) := by
    dsimp only [W₁]
    rw [Matrix.submatrix_mulVec_equiv]
    simp [Function.comp_assoc]
  simp only [Pi.add_apply, Pi.zero_apply, add_zero, h1, Matrix.fromCols_mulVec,
    Matrix.one_mulVec, Matrix.neg_mulVec]
  simpa [max_comm, sub_eq_add_neg] using max_zero_sub_max_neg_zero_eq_self (x j)

/-- A depth-zero ReLU network on `ℝ` computes only the identity `x ↦ x 0`. -/
theorem reluNetComputes_depth_zero_iff {f : (Fin 1 → ℝ) → ℝ} :
    ReLUNetComputes ![1] f ↔ f = fun x => x 0 := by
  rw [reluNetComputes_iff]
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
  · rintro ⟨d, hd⟩
    obtain ⟨h0, hL, θ, hθ⟩ := reluNetComputes_iff.mp hd
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

end TauCeti
