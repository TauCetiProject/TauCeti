/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite chains of realization maps

`chain` composes a finite family of supplied models with possibly different intermediate
spaces and parameter types. Its parameters are the dependent product of all layer parameter
spaces, including the empty product for a chain of length zero. No injectivity of any layer
or of its parametrization is required.

The head and last-layer recursion laws express evaluation as iterated composition.
`Fin.consEquiv` and `Fin.snocEquiv` identify the full parameter product with the parameter
of an end layer and the product for the remaining chain. The corresponding range formula
describes the realized functions, rather than identifying different parameter tuples.

This iterates the layer-composition convention of Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
-/

public section

namespace TauCeti.Neuromanifold

universe u v

/-- Compose finitely many supplied realization maps, retaining every layer's parameters.
The spaces are indexed by vertices and the parameter types and maps by edges. -/
def chain : {n : ℕ} → {X : Fin (n + 1) → Type u} → {W : Fin n → Type v} →
    (∀ i, W i → X i.castSucc → X i.succ) → (∀ i, W i) → X 0 → X (Fin.last n)
  | 0, _, _, _, _, x => x
  | n + 1, X, _, f, w, x =>
      chain (X := fun i : Fin (n + 1) => X i.succ)
        (fun i => f i.succ) (fun i => w i.succ) (f 0 (w 0) x)

/-- An empty chain realizes the identity, with its empty parameter product. -/
@[simp] theorem chain_zero {X : Fin 1 → Type u} {W : Fin 0 → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = id := (rfl)

/-- Evaluate a nonempty chain by applying the first layer and then the remaining chain. -/
@[simp] theorem chain_succ {n : ℕ} {X : Fin (n + 2) → Type u} {W : Fin (n + 1) → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = chain (X := fun i : Fin (n + 1) => X i.succ)
      (fun i => f i.succ) (fun i => w i.succ) ∘ f 0 (w 0) := (rfl)

/-- The head-layer recursion under the canonical equivalence of parameter products. -/
theorem chain_consEquiv {n : ℕ} {X : Fin (n + 2) → Type u}
    {W : Fin (n + 1) → Type v} (f : ∀ i, W i → X i.castSucc → X i.succ)
    (p : W 0 × (∀ i : Fin n, W i.succ)) :
    chain f (Fin.consEquiv W p) =
      chain (X := fun i : Fin (n + 1) => X i.succ)
        (fun i => f i.succ) p.2 ∘ f 0 p.1 := by
  simp [chain_succ]

/-- Evaluate a nonempty chain by applying its last layer to the preceding chain. -/
theorem chain_snoc {n : ℕ} {X : Fin (n + 2) → Type u} {W : Fin (n + 1) → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = f (Fin.last n) (w (Fin.last n)) ∘
      chain (X := fun i : Fin (n + 1) => X i.castSucc)
        (fun i => f i.castSucc) (fun i => w i.castSucc) := by
  induction n with
  | zero =>
      funext x
      simp
  | succ n ih =>
      rw [chain_succ,
        ih (X := fun i => X i.succ) (fun i => f i.succ) (fun i => w i.succ),
        chain_succ (X := fun i => X i.castSucc) (fun i => f i.castSucc)]
      rfl

/-- The last-layer recursion under the canonical equivalence of parameter products. -/
theorem chain_snocEquiv {n : ℕ} {X : Fin (n + 2) → Type u}
    {W : Fin (n + 1) → Type v} (f : ∀ i, W i → X i.castSucc → X i.succ)
    (p : W (Fin.last n) × (∀ i : Fin n, W i.castSucc)) :
    chain f (Fin.snocEquiv W p) = f (Fin.last n) p.1 ∘
      chain (X := fun i : Fin (n + 1) => X i.castSucc)
        (fun i => f i.castSucc) p.2 := by
  rw [chain_snoc]
  simp

/-- Replacing each layer by the same realized function leaves the whole chain unchanged.
The two chains may have different parameter spaces and redundant parametrizations. -/
theorem chain_congr {n : ℕ} {X : Fin (n + 1) → Type u}
    {W : Fin n → Type v} {V : Fin n → Type*}
    (f : ∀ i, W i → X i.castSucc → X i.succ)
    (g : ∀ i, V i → X i.castSucc → X i.succ)
    (w : ∀ i, W i) (v : ∀ i, V i)
    (h : ∀ i, f i (w i) = g i (v i)) : chain f w = chain g v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [chain_succ, chain_succ, h 0,
        ih (X := fun i => X i.succ) (fun i => f i.succ) (fun i => g i.succ)
          (fun i => w i.succ) (fun i => v i.succ) (fun i => h i.succ)]

/-- Reparametrizing each layer reparametrizes the full chain by the dependent product map.
For instance, zero-bias embeddings can be supplied separately at each layer. -/
theorem chain_reparametrize {n : ℕ} {X : Fin (n + 1) → Type u}
    {W : Fin n → Type v} {V : Fin n → Type*}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (r : ∀ i, V i → W i) :
    chain (fun i v => f i (r i v)) = chain f ∘ Pi.map r := by
  funext v
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.comp_apply, chain_succ, chain_succ,
        ih (X := fun i => X i.succ) (fun i => f i.succ) (fun i => r i.succ)]
      rfl

/-- The empty chain has exactly the identity as its realized function. -/
@[simp] theorem realizedFunctions_chain_zero {X : Fin 1 → Type u}
    {W : Fin 0 → Type v} (f : ∀ i, W i → X i.castSucc → X i.succ) :
    realizedFunctions (chain f) = {id} := by
  simp [realizedFunctions_def, chain_zero]

/-- The functions realized by a chain are exactly the composites of a first-layer
realization and a realization of the remaining chain. This also covers empty parameter
spaces, when the corresponding range is empty. -/
theorem realizedFunctions_chain_succ {n : ℕ} {X : Fin (n + 2) → Type u}
    {W : Fin (n + 1) → Type v} (f : ∀ i, W i → X i.castSucc → X i.succ) :
    realizedFunctions (chain f) =
      {h | ∃ a ∈ realizedFunctions (f 0),
        ∃ b ∈ realizedFunctions
          (chain (X := fun i : Fin (n + 1) => X i.succ) (fun i => f i.succ)),
          b ∘ a = h} := by
  ext h
  simp only [mem_realizedFunctions]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨f 0 (w 0), ⟨w 0, rfl⟩,
      chain (X := fun i : Fin (n + 1) => X i.succ)
        (fun i => f i.succ) (fun i => w i.succ),
      ⟨fun i => w i.succ, rfl⟩, (chain_succ f w).symm⟩
  · rintro ⟨a, ⟨w₀, rfl⟩, b, ⟨w, rfl⟩, rfl⟩
    exact ⟨Fin.consEquiv W (w₀, w), chain_consEquiv f (w₀, w)⟩

end TauCeti.Neuromanifold
