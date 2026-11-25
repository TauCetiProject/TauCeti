/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Cofinite
import TauCeti.Data.List.Finite

/-!
# Weighted length of reduced words

Injectively numbering the generators by natural numbers gives a reduced-word weight
with finite sublevel sets.
-/

public section

open Filter

namespace FreeGroup

/-- With an injective numbering of generators, the reduced-word weight obtained by adding one to
each letter's number tends to infinity along the cofinite filter. -/
theorem tendsto_cofinite_sum_map_toWord {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) (hn : Function.Injective n) :
    Tendsto (fun g : FreeGroup ι => (g.toWord.map fun x => n x.1 + 1).sum) cofinite atTop := by
  refine tendsto_atTop.2 fun N => eventually_cofinite.2 ?_
  let w (x : ι × Bool) := n x.1 + 1
  have hcut : {x ∈ (Set.univ : Set (ι × Bool)) | w x ≤ N}.Finite := by
    refine ((Set.finite_range (fun i : Fin N => (i : ℕ))).preimage hn.injOn |>.prod
      Set.finite_univ).subset ?_
    rintro x ⟨_, hx⟩
    dsimp only [w] at hx
    exact ⟨⟨⟨n x.1, by omega⟩, rfl⟩, Set.mem_univ _⟩
  have hlists := TauCeti.finite_setOf_sum_map_le_nat w N
    (fun x _ => Nat.succ_pos (n x.1)) hcut
  exact (hlists.preimage toWord_injective.injOn).subset fun _ hg =>
    ⟨fun _ _ => Set.mem_univ _, (not_le.mp hg).le⟩

end FreeGroup
