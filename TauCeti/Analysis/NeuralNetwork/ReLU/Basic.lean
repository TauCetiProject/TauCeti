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
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin
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
@[grind →]
theorem ReLUNetRealizes.width_zero {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) : d 0 = n :=
  hf.choose

/-- A network realizing a map into `Fin m → ℝ` has output width `m`. -/
@[grind →]
theorem ReLUNetRealizes.width_last {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) : d (Fin.last L) = m :=
  hf.choose_spec.choose

/-- A network computing a scalar function on `Fin n → ℝ` has input width `n`. -/
@[grind →]
theorem ReLUNetComputes.width_zero {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) : d 0 = n :=
  (reluNetComputes_iff_reluNetRealizes.mp hf).width_zero

/-- A network computing a scalar function has output width `1`. -/
@[grind →]
theorem ReLUNetComputes.width_last {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) : d (Fin.last L) = 1 :=
  (reluNetComputes_iff_reluNetRealizes.mp hf).width_last

/-- If any layer of a ReLU network realizing `f` has width zero, then `f` is constant. -/
theorem ReLUNetRealizes.eq_of_width_eq_zero {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f)
    {k : Fin (L + 1)} (hk : d k = 0) (x x' : Fin n → ℝ) :
    f x = f x' := by
  obtain ⟨h0, hL, θ, hθ⟩ := reluNetRealizes_iff.mp hf
  have hconst := (reluSpec d).realize_eq_of_width_eq_zero θ hk
    (fun i => x (Fin.cast h0 i)) (fun i => x' (Fin.cast h0 i))
  ext j
  rw [← hθ x j, ← hθ x' j, hconst]

/-- If any layer of a ReLU network computing `f` has width zero, then `f` is constant. -/
theorem ReLUNetComputes.eq_of_width_eq_zero {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f)
    {k : Fin (L + 1)} (hk : d k = 0) (x x' : Fin n → ℝ) :
    f x = f x' :=
  congrFun ((reluNetComputes_iff_reluNetRealizes.mp hf).eq_of_width_eq_zero hk x x') 0

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

/-- Transporting `ReLUNetRealizes` along equal depths and cast-indexed widths. -/
theorem ReLUNetRealizes.congr_depth {n m L L' : ℕ} {d : Fin (L + 1) → ℕ}
    {d' : Fin (L' + 1) → ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (hf : ReLUNetRealizes d f) (hL : L = L')
    (hd : ∀ i : Fin (L + 1), d i = d' (Fin.cast (congrArg (· + 1) hL) i)) :
    ReLUNetRealizes d' f := by
  subst hL
  exact hf.of_width_eq (funext hd)

/-- Transporting `ReLUNetComputes` along equal depths and cast-indexed widths. -/
theorem ReLUNetComputes.congr_depth {n L L' : ℕ} {d : Fin (L + 1) → ℕ}
    {d' : Fin (L' + 1) → ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ReLUNetComputes d f) (hL : L = L')
    (hd : ∀ i : Fin (L + 1), d i = d' (Fin.cast (congrArg (· + 1) hL) i)) :
    ReLUNetComputes d' f :=
  reluNetComputes_iff_reluNetRealizes.mpr
    ((reluNetComputes_iff_reluNetRealizes.mp hf).congr_depth hL hd)

/-- The hidden layers of a network of depth `L`: the indices strictly between the input `0` and
the output `Fin.last L`. -/
def hiddenLayers (L : ℕ) : Finset (Fin (L + 1)) :=
  Finset.Ioo 0 (Fin.last L)

/-- `hiddenLayers L` is the finite interval `Finset.Ioo 0 (Fin.last L)`. -/
theorem hiddenLayers_def (L : ℕ) : hiddenLayers L = Finset.Ioo 0 (Fin.last L) := (rfl)

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

/-- A depth-2 ReLU network with widths `![a, b, c]` realizes `f` if and only if `f` is given by
two affine layers with a coordinatewise ReLU hidden layer of width `b`. -/
theorem reluNetRealizes_depth_two_iff {a b c : ℕ} {f : (Fin a → ℝ) → (Fin c → ℝ)} :
    ReLUNetRealizes ![a, b, c] f ↔
      ∃ (W₀ : Matrix (Fin b) (Fin a) ℝ) (b₀ : Fin b → ℝ)
        (W₁ : Matrix (Fin c) (Fin b) ℝ) (b₁ : Fin c → ℝ),
        f = fun x => W₁ *ᵥ (fun k => max 0 ((W₀ *ᵥ x) k + b₀ k)) + b₁ := by
  have hact (v : Fin ((reluSpec ![a, b, c]).width 1) → ℝ) :
      Neuromanifold.activation ((reluSpec ![a, b, c]).layerActivation 0) () v =
        fun k => max 0 (v k) := funext fun k => by
    rw [Neuromanifold.activation_apply]
    exact layerActivation_reluSpec_castSucc ![a, b, c] 0 (v k)
  have hreal (θ : (reluSpec ![a, b, c]).Parameters) (x : Fin a → ℝ) :
      (reluSpec ![a, b, c]).realize θ x =
        (θ 1).1 *ᵥ (fun k => max 0 (((θ 0).1 *ᵥ x) k + (θ 0).2 k)) + (θ 1).2 := by
    have h1 := congrFun (MLPSpec.realize_eq_tail_comp (reluSpec ![a, b, c]) θ) x
    have h2 := congrFun (MLPSpec.realize_depth_one_eq_dense (reluSpec ![a, b, c]).tail (Fin.tail θ))
      (Neuromanifold.activation ((reluSpec ![a, b, c]).layerActivation 0) ()
        (Neuromanifold.dense (θ 0) x))
    have h3 : Neuromanifold.dense (Fin.tail θ 0)
        (Neuromanifold.activation ((reluSpec ![a, b, c]).layerActivation 0) ()
          (Neuromanifold.dense (θ 0) x)) =
        (θ 1).1 *ᵥ (fun k => max 0 (((θ 0).1 *ᵥ x) k + (θ 0).2 k)) + (θ 1).2 := by
      have hd0 : Neuromanifold.dense (θ 0) x = (θ 0).1 *ᵥ x + (θ 0).2 :=
        Neuromanifold.dense_apply (θ 0) x
      rw [Neuromanifold.dense_apply, hact, hd0]
      rfl
    exact h1.trans (h2.trans h3)
  constructor
  · intro hf
    obtain ⟨h0, hL, θ, hθ⟩ := reluNetRealizes_iff.mp hf
    exact ⟨(θ 0).1, (θ 0).2, (θ 1).1, (θ 1).2, funext fun x => funext fun j =>
      (hθ x j).symm.trans (congrFun (hreal θ x) j)⟩
  · rintro ⟨W₀, b₀, W₁, b₁, rfl⟩
    let θ₀ : Matrix (Fin ((reluSpec ![a, b, c]).width 1)) (Fin ((reluSpec ![a, b, c]).width 0)) ℝ ×
        (Fin ((reluSpec ![a, b, c]).width 1) → ℝ) := (W₀, b₀)
    let θ₁ : (reluSpec ![a, b, c]).tail.Parameters := Fin.cons (W₁, b₁) fun i => i.elim0
    refine ⟨rfl, rfl, Fin.cons θ₀ θ₁, fun x j => ?_⟩
    exact congrFun (hreal (Fin.cons θ₀ θ₁) x) j

/-- A depth-2 ReLU network with widths `![a, b, 1]` computes `f` if and only if `f` is given by
two affine layers with a coordinatewise ReLU hidden layer of width `b`. -/
theorem reluNetComputes_depth_two_iff {a b : ℕ} {f : (Fin a → ℝ) → ℝ} :
    ReLUNetComputes ![a, b, 1] f ↔
      ∃ (W₀ : Matrix (Fin b) (Fin a) ℝ) (b₀ : Fin b → ℝ)
        (W₁ : Matrix (Fin 1) (Fin b) ℝ) (b₁ : Fin 1 → ℝ),
        f = fun x => (W₁ *ᵥ (fun k => max 0 ((W₀ *ᵥ x) k + b₀ k)) + b₁) 0 := by
  rw [reluNetComputes_iff_reluNetRealizes, reluNetRealizes_depth_two_iff]
  constructor
  · rintro ⟨W₀, b₀, W₁, b₁, hf⟩
    exact ⟨W₀, b₀, W₁, b₁, funext fun x => congrFun (congrFun hf x) 0⟩
  · rintro ⟨W₀, b₀, W₁, b₁, rfl⟩
    exact ⟨W₀, b₀, W₁, b₁, funext fun x => funext fun j => by rw [Fin.eq_zero j]⟩

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
  refine reluNetRealizes_depth_two_iff.mpr ⟨W₀, 0, W₁, 0, funext fun x => funext fun j => ?_⟩
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
    Matrix.one_mulVec, Matrix.neg_mulVec, id_eq]
  simpa [max_comm, sub_eq_add_neg] using (max_zero_sub_max_neg_zero_eq_self (x j)).symm

/-- A depth-zero ReLU network with widths `![n]` realizes only the identity on `Fin n → ℝ`. -/
theorem reluNetRealizes_depth_zero_iff {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} :
    ReLUNetRealizes ![n] f ↔ f = id := by
  rw [reluNetRealizes_iff]
  constructor
  · rintro ⟨h0, hL, θ, hθ⟩
    ext x j
    have hx := (hθ x j).symm
    rw [MLPSpec.realize_depth_zero] at hx
    exact hx.trans (congrArg x (Fin.ext rfl))
  · rintro rfl
    refine ⟨rfl, rfl, fun i => i.elim0, fun x j => ?_⟩
    rw [MLPSpec.realize_depth_zero]
    exact congrArg x (Fin.ext rfl)

/-- A depth-zero ReLU network on `ℝ` computes only the identity `x ↦ x 0`. -/
theorem reluNetComputes_depth_zero_iff {f : (Fin 1 → ℝ) → ℝ} :
    ReLUNetComputes ![1] f ↔ f = fun x => x 0 := by
  rw [reluNetComputes_iff_reluNetRealizes, reluNetRealizes_depth_zero_iff]
  constructor
  · intro h
    ext x
    exact congrFun (congrFun h x) 0
  · rintro rfl
    ext x j
    rw [Fin.eq_zero j]
    rfl

/-- A depth-one ReLU network with widths `![n, m]` realizes `f` if and only if `f` is a
continuous affine map. -/
theorem reluNetRealizes_depth_one_iff {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)} :
    ReLUNetRealizes ![n, m] f ↔ ∃ A : (Fin n → ℝ) →ᴬ[ℝ] (Fin m → ℝ), f = ⇑A := by
  constructor
  · intro hf
    obtain ⟨h0, hL, θ, hθ⟩ := reluNetRealizes_iff.mp hf
    let W : Matrix (Fin m) (Fin n) ℝ := fun i j => (θ 0).1 i j
    let b : Fin m → ℝ := fun i => (θ 0).2 i
    let Lmap : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
      LinearMap.toContinuousLinearMap (Matrix.toLin' W)
    refine ⟨Lmap.toContinuousAffineMap + ContinuousAffineMap.const ℝ (Fin n → ℝ) b, ?_⟩
    ext x j
    have hx := (hθ x j).symm
    rw [MLPSpec.realize_depth_one] at hx
    change f x j = (W *ᵥ (fun i : Fin n => x (Fin.cast h0 i)) + b) (Fin.cast hL.symm j) at hx
    have hx' : (fun i : Fin n => x (Fin.cast h0 i)) = x := funext fun i => congrArg x (Fin.ext rfl)
    rw [hx'] at hx
    refine hx.trans ((congrArg (W *ᵥ x + b) (Fin.ext rfl)).trans ?_)
    simp [Lmap]
  · rintro ⟨A, rfl⟩
    exact ReLUNetRealizes.of_continuousAffineMap A

/-- A depth-one ReLU network with widths `![n, 1]` computes `f` if and only if `f` is a
continuous affine functional. -/
theorem reluNetComputes_depth_one_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    ReLUNetComputes ![n, 1] f ↔ ∃ A : (Fin n → ℝ) →ᴬ[ℝ] ℝ, f = ⇑A := by
  constructor
  · intro hf
    rw [reluNetComputes_iff_reluNetRealizes, reluNetRealizes_depth_one_iff] at hf
    obtain ⟨B, hB⟩ := hf
    let eval0 : (Fin 1 → ℝ) →ᴬ[ℝ] ℝ :=
      (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap
    exact ⟨eval0.comp B, funext fun x => congrFun (congrFun hB x) 0⟩
  · rintro ⟨A, rfl⟩
    exact ReLUNetComputes.of_continuousAffineMap A

/-- A depth-one ReLU network computes a function if and only if that function is continuous
affine. -/
theorem exists_reluNetComputes_depth_one_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    (∃ d : Fin 2 → ℕ, ReLUNetComputes d f) ↔
      ∃ A : (Fin n → ℝ) →ᴬ[ℝ] ℝ, f = ⇑A := by
  constructor
  · rintro ⟨d, hd⟩
    have hd_eq : d = ![n, 1] := funext fun i => by
      fin_cases i
      · exact hd.width_zero
      · exact hd.width_last
    exact reluNetComputes_depth_one_iff.mp (hd.of_width_eq hd_eq)
  · rintro h
    exact ⟨![n, 1], reluNetComputes_depth_one_iff.mpr h⟩

/-- The absolute value `x ↦ |x 0|` on `ℝ` is computed by a depth-2 ReLU network with two hidden
units (`![1, 2, 1]`). -/
theorem reluNetComputes_abs :
    ReLUNetComputes ![1, 2, 1] (fun x : Fin 1 → ℝ => |x 0|) := by
  refine reluNetComputes_depth_two_iff.mpr ⟨!![1; -1], 0, !![1, 1], 0, funext fun x => ?_⟩
  simp only [Pi.add_apply, Pi.zero_apply, add_zero, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, neg_mul]
  rcases le_total 0 (x 0) with h | h <;> simp [h, abs_of_nonneg, abs_of_nonpos]

/-- `max x₀ x₁ = max 0 (x₀ - x₁) + max 0 x₁ - max 0 (-x₁)` is computed by a depth-2 ReLU
network with three hidden units (`![2, 3, 1]`). -/
theorem reluNetComputes_max :
    ReLUNetComputes ![2, 3, 1] (fun x : Fin 2 → ℝ => max (x 0) (x 1)) := by
  refine reluNetComputes_depth_two_iff.mpr
    ⟨!![1, -1; 0, 1; 0, -1], 0, !![1, 1, -1], 0, funext fun x => ?_⟩
  simp only [Pi.add_apply, Pi.zero_apply, add_zero, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, neg_mul, zero_mul, zero_add]
  rcases le_total (x 0) (x 1) with h | h <;> rcases le_total 0 (x 1) with h1 | h1 <;>
    simp [h, h1]

end TauCeti
