/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Chain.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Data.Fin.Fold

/-!
# Splitting finite chains of realization maps

A chain can be cut at any intermediate space. Its realization is the composition of the
realizations of its two blocks, after identifying the full parameter product with the product
of the block parameter spaces by Mathlib's `Equiv.piCongrLeft` and `Equiv.sumPiEquivProdPi`.
Consequently its realized functions are exactly the composites realized by the two blocks.
Both blocks may have length zero, and the layer parameter types may be empty.
-/

public section

namespace TauCeti.Neuromanifold

universe u v

variable {m n : ℕ} {X : Fin (m + n + 1) → Type u} {W : Fin (m + n) → Type v}

/-- Cut a chain after its first `m` layers. The second block acts on the output of the first. -/
theorem chain_add (f : ∀ i, W i → X i.castSucc → X i.succ) (w : ∀ i, W i) :
    chain f w =
      chain (X := fun i => X (i.natAdd m)) (fun i => f (i.natAdd m))
        (fun i => w (i.natAdd m)) ∘
      chain (X := fun i => X (i.castLE (by omega))) (fun i => f (i.castAdd n))
        (fun i => w (i.castAdd n)) := by
  funext x
  simp only [chain_eq_dfoldl]
  exact Fin.dfoldl_add (fun i => f i (w i)) x

/-- The canonical equivalence splitting the parameter product turns an arbitrary cut of a
chain into binary model composition. -/
theorem chain_comp_split (f : ∀ i, W i → X i.castSucc → X i.succ) :
    chain f ∘
        ((Equiv.piCongrLeft W finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)).symm =
      compose
        (chain (X := fun i => X (i.castLE (by omega))) (fun i => f (i.castAdd n)))
        (chain (X := fun i => X (i.natAdd m)) (fun i => f (i.natAdd m))) := by
  let e : (∀ i, W i) ≃
      (∀ i : Fin m, W (i.castAdd n)) × (∀ i : Fin n, W (i.natAdd m)) :=
    (Equiv.piCongrLeft W finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)
  funext p
  have hleft : (fun i : Fin m => e.symm p (i.castAdd n)) = p.1 :=
    congrArg Prod.fst (e.apply_symm_apply p)
  have hright : (fun i : Fin n => e.symm p (i.natAdd m)) = p.2 :=
    congrArg Prod.snd (e.apply_symm_apply p)
  exact (chain_add f (e.symm p)).trans
    ((congrArg₂ (fun a b => b ∘ a) (congrArg _ hleft) (congrArg _ hright)).trans
      (compose_apply _ _ p).symm)

/-- The neuromanifold of a chain is the set of composites of functions realized by its two
blocks at any chosen cut. No parameter nonemptiness hypothesis is needed. -/
theorem realizedFunctions_chain_add (f : ∀ i, W i → X i.castSucc → X i.succ) :
    realizedFunctions (chain f) =
      Set.image2 (fun a b => b ∘ a)
        (realizedFunctions
          (chain (X := fun i => X (i.castLE (by omega))) (fun i => f (i.castAdd n))))
        (realizedFunctions
          (chain (X := fun i => X (i.natAdd m)) (fun i => f (i.natAdd m)))) := by
  let e := (Equiv.piCongrLeft W finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)
  calc
    _ = realizedFunctions (chain f ∘ e.symm) := by
      simp only [realizedFunctions_def, e.symm.surjective.range_comp]
    _ = _ := (congrArg realizedFunctions (chain_comp_split f)).trans
      (realizedFunctions_compose _ _)

end TauCeti.Neuromanifold
