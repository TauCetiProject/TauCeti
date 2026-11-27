/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Batteries.Data.Fin.Fold
public import Mathlib.Data.Fin.Tuple.Basic
public import TauCeti.Geometry.Neuromanifold.Composition

/-!
# Finite chains of realization maps

`chain f` composes a finite family of supplied realization maps, allowing both the intermediate
spaces and the layer parameter types to vary. Its parameter space is the full dependent product;
no injectivity or nonemptiness is assumed. The empty chain realizes the identity.

Evaluation is Mathlib/Batteries' `Fin.dfoldl`, not a separate recursion. Splitting off either end
identifies the parameter product with the parameters of a binary `compose`. Accordingly, the
neuromanifold is the set of composites of functions realized by the two pieces. These formulas
can be iterated even when some layer has an empty parameter space.

The layer-composition convention follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
-/

public section

namespace TauCeti.Neuromanifold

universe u v t

variable {n : ℕ} {X : Fin (n + 1) → Type u} {W : Fin n → Type v}

/-- Compose supplied layer models in increasing index order, retaining every layer's parameters.
The intermediate value is computed by `Fin.dfoldl`. -/
def chain (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    X 0 → X (Fin.last n) :=
  Fin.dfoldl n X (fun i => f i (w i))

/-- The chain evaluator is the dependent left fold of the chosen layer functions. -/
theorem chain_eq_dfoldl (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = Fin.dfoldl n X (fun i => f i (w i)) := (rfl)

/-- An empty chain realizes the identity, regardless of the (empty) parameter tuple. -/
@[simp] theorem chain_zero {X : Fin 1 → Type u} {W : Fin 0 → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = id := by
  funext x
  exact Fin.dfoldl_zero _ x

/-- Split off the first layer of a chain. -/
@[simp] theorem chain_succ {X : Fin (n + 2) → Type u} {W : Fin (n + 1) → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = chain (X := fun i => X i.succ) (fun i => f i.succ) (fun i => w i.succ) ∘
      f 0 (w 0) := by
  funext x
  exact Fin.dfoldl_succ _ x

/-- Split off the last layer of a chain. -/
theorem chain_succ_last {X : Fin (n + 2) → Type u} {W : Fin (n + 1) → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w = f (Fin.last n) (w (Fin.last n)) ∘
      chain (X := fun i => X i.castSucc) (fun i => f i.castSucc) (fun i => w i.castSucc) := by
  funext x
  exact Fin.dfoldl_succ_last _ x

/-- The canonical first-layer parameter split turns a chain into binary model composition. -/
theorem chain_comp_consEquiv {X : Fin (n + 2) → Type u} {W : Fin (n + 1) → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) :
    chain f ∘ Fin.consEquiv W =
      compose (f 0) (chain (X := fun i => X i.succ) (fun i => f i.succ)) := by
  funext p
  simpa only [Function.comp_apply, Fin.consEquiv_apply, Fin.cons_succ, Fin.cons_zero,
    compose_apply] using chain_succ f (Fin.cons p.1 p.2)

/-- The canonical last-layer parameter split turns a chain into binary model composition.
`Fin.snocEquiv` lists the last parameter first, so the pair is swapped before composition. -/
theorem chain_comp_snocEquiv {X : Fin (n + 2) → Type u} {W : Fin (n + 1) → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) :
    chain f ∘ Fin.snocEquiv W =
      compose (chain (X := fun i => X i.castSucc) (fun i => f i.castSucc)) (f (Fin.last n)) ∘
        Equiv.prodComm _ _ := by
  funext p
  simpa only [Function.comp_apply, Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_castSucc,
    compose_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    using chain_succ_last f (Fin.snoc p.2 p.1)

/-- The empty chain's neuromanifold consists exactly of the identity function. -/
@[simp] theorem realizedFunctions_chain_zero {X : Fin 1 → Type u} {W : Fin 0 → Type v}
    (f : ∀ i, W i → X i.castSucc → X i.succ) :
    realizedFunctions (chain f) = {id} := by
  simp [realizedFunctions_def]

/-- The functions realized by a nonempty chain are the composites of a first-layer function
and a function realized by the remaining chain. -/
theorem realizedFunctions_chain_succ {X : Fin (n + 2) → Type u}
    {W : Fin (n + 1) → Type v} (f : ∀ i, W i → X i.castSucc → X i.succ) :
    realizedFunctions (chain f) =
      Set.image2 (fun a b => b ∘ a) (realizedFunctions (f 0))
        (realizedFunctions (chain (X := fun i => X i.succ) (fun i => f i.succ))) := by
  calc
    _ = realizedFunctions (chain f ∘ Fin.consEquiv W) := by
      simp only [realizedFunctions_def, (Fin.consEquiv W).surjective.range_comp]
    _ = realizedFunctions (X := X 0) (Y := X (Fin.last (n + 1)))
        (compose (f 0) (chain (X := fun i => X i.succ) (fun i => f i.succ))) :=
      congrArg realizedFunctions (chain_comp_consEquiv f)
    _ = _ := realizedFunctions_compose _ _

/-- The functions realized by a nonempty chain are the composites of a function realized by
its prefix and a last-layer function. -/
theorem realizedFunctions_chain_succ_last {X : Fin (n + 2) → Type u}
    {W : Fin (n + 1) → Type v} (f : ∀ i, W i → X i.castSucc → X i.succ) :
    realizedFunctions (chain f) =
      Set.image2 (fun a b => b ∘ a)
        (realizedFunctions (chain (X := fun i => X i.castSucc) (fun i => f i.castSucc)))
        (realizedFunctions (f (Fin.last n))) := by
  calc
    _ = realizedFunctions (chain f ∘ Fin.snocEquiv W) := by
      simp only [realizedFunctions_def, (Fin.snocEquiv W).surjective.range_comp]
    _ = realizedFunctions (X := X 0) (Y := X (Fin.last (n + 1)))
        (compose (chain (X := fun i => X i.castSucc) (fun i => f i.castSucc))
          (f (Fin.last n)) ∘ Equiv.prodComm _ _) :=
      congrArg realizedFunctions (chain_comp_snocEquiv f)
    _ = realizedFunctions (X := X 0) (Y := X (Fin.last (n + 1)))
        (compose (chain (X := fun i => X i.castSucc) (fun i => f i.castSucc))
          (f (Fin.last n))) := by
      simp only [realizedFunctions_def, (Equiv.prodComm _ _).surjective.range_comp]
    _ = _ := realizedFunctions_compose _ _

/-- Reparametrizing every layer reparametrizes the chain by the induced map of parameter
products. The parameter maps need not be injective or surjective. -/
theorem chain_eq_chain_comp_piMap {V : Fin n → Type t}
    (f : ∀ i, W i → X i.castSucc → X i.succ) (r : ∀ i, V i → W i) :
    chain (fun i v => f i (r i v)) = chain f ∘ Pi.map r := by
  funext v
  simp only [chain_eq_dfoldl, Function.comp_apply, Pi.map_apply]

end TauCeti.Neuromanifold
