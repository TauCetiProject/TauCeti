/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Matroid.Circuit

/-!
# The symmetric exchange property of bases

For two bases `B` and `B'` of a matroid and `e ∈ B \ B'`, Mathlib's `Matroid.IsBase.exchange`
finds `f ∈ B' \ B` such that `insert f (B \ {e})` is a base. This file proves Brualdi's
strengthening: `f` can be chosen so that, in addition, `insert e (B' \ {f})` is a base. No
finiteness is assumed.

The element `f` is found in the intersection of the fundamental circuit of `e` with respect to
`B'` and the fundamental cocircuit of `e` with respect to `B`: a circuit and a cocircuit never
meet in exactly one element.

The property is the exchange step behind the optimality criteria for bases of maximum weight.

## Main declarations

* `Matroid.IsBase.mem_fundCircuit_iff_isBase_exchange`: the fundamental circuit of `e` in a
  base `B` consists of `e` and the elements of `B` that can be exchanged for `e`.
* `Matroid.IsBase.exists_symm_exchange`: the symmetric exchange property of bases.

## References

* R. A. Brualdi, *Comments on bases in dependence structures*, Bull. Austral. Math. Soc. 1
  (1969), 161–167.
-/

public section

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' : Set α} {e f : α}

/-- For a base `B` and `e ∈ M.E \ B`, an element `f ≠ e` lies on the fundamental circuit of `e` in
`B` if and only if exchanging `f` for `e` gives a base. -/
theorem IsBase.mem_fundCircuit_iff_isBase_exchange (hB : M.IsBase B) (heE : e ∈ M.E)
    (heB : e ∉ B) (hfe : f ≠ e) : f ∈ M.fundCircuit e B ↔ M.IsBase (insert e (B \ {f})) := by
  rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) heB,
    ← insert_sdiff_singleton_comm hfe.symm]
  exact ⟨hB.exchange_isBase_of_indep heB, IsBase.indep⟩

/-- **Symmetric exchange** (Brualdi). If `B` and `B'` are bases and `e ∈ B \ B'`, there is
`f ∈ B' \ B` such that both `insert f (B \ {e})` and `insert e (B' \ {f})` are bases. -/
theorem IsBase.exists_symm_exchange (hB : M.IsBase B) (hB' : M.IsBase B') (he : e ∈ B \ B') :
    ∃ f ∈ B' \ B, M.IsBase (insert f (B \ {e})) ∧ M.IsBase (insert e (B' \ {f})) := by
  have heE : e ∈ M.E := hB.subset_ground he.1
  have hC := hB'.fundCircuit_isCircuit heE he.2
  have hK := M.fundCocircuit_isCocircuit he.1 hB
  -- `e` lies in both the circuit and the cocircuit, which cannot meet in `{e}` alone.
  obtain ⟨f, ⟨hfC, hfK⟩, hfe⟩ : ∃ f ∈ M.fundCircuit e B' ∩ M.fundCocircuit e B, f ≠ e := by
    by_contra! h
    exact hC.inter_isCocircuit_ne_singleton hK <| subset_antisymm (fun x hx ↦ h x hx)
      (singleton_subset_iff.2 ⟨M.mem_fundCircuit e B', M.mem_fundCocircuit e B⟩)
  have hfB' : f ∈ B' := ((M.fundCircuit_subset_insert e B') hfC).resolve_left hfe
  have hfB : f ∉ B := fun hfB ↦ hfe <| by
    simpa [M.fundCocircuit_inter_eq he.1] using (show f ∈ M.fundCocircuit e B ∩ B from ⟨hfK, hfB⟩)
  -- `f` lies in the fundamental cocircuit of `e` in `B`, so `e` lies on the fundamental circuit
  -- of `f` in `B`.
  exact ⟨f, ⟨hfB', hfB⟩, (hB.mem_fundCircuit_iff_isBase_exchange (hB'.subset_ground hfB') hfB
      hfe.symm).1 (hB.mem_fundCocircuit_iff_mem_fundCircuit.1 hfK),
    (hB'.mem_fundCircuit_iff_isBase_exchange heE he.2 hfe).1 hfC⟩

end Matroid
