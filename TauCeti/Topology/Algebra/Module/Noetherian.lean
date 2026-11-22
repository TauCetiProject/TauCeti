/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.Topology.Algebra.Module.Baire

/-!
# Noetherianity from closed submodules

Let `A` be a ring with a topology in which zero is a limit of units. This holds whenever `A`
admits a sequence of units converging to zero, such as a Tate ring, through the instance
`TauCeti.HasZeroSequenceOfUnits.nhdsWithin_isUnit_neBot`. Over such a ring a topological module
has no proper submodule with nonempty interior (Mathlib's
`Submodule.eq_top_of_nonempty_interior'`), so by Baire category a Baire module is not a countable
union of proper closed submodules (`Submodule.exists_forall_notMem_of_isClosed`). This file draws a
consequence of that for completely pseudometrisable modules. The same fact about interiors gives
the remaining implications of Wedhorn's Theorem 6.16, in
`TauCeti.Topology.Algebra.OpenMapping.Converse`.

Over such a ring, a completely pseudometrisable topological module all of whose submodules are
closed is noetherian, generalising the converse half of Wedhorn's Proposition 6.17. Given an
`ℕ`-indexed ascending chain of submodules, their union `S` is closed, hence completely
pseudometrisable and so a Baire space. The members of the chain are countably many closed
submodules of `S` covering it, so one of them is all of `S`, and the chain stops there.

Over a complete Hausdorff Tate ring the forward half, that every submodule of a noetherian module is
closed, is `TauCeti.Huber.isClosed_of_isNoetherian`; the two halves are assembled into Wedhorn's
equivalence in `TauCeti.Huber.isNoetherian_iff_forall_isClosed`.

## Main results

* `TauCeti.isNoetherian_of_forall_isClosed`: over a ring in which zero is a limit of units, a
  completely pseudometrisable topological module whose submodules are all closed is noetherian.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.17.
-/

public section

open Filter TopologicalSpace Topology

namespace TauCeti

variable {A : Type*} [Ring A] [TopologicalSpace A] [NeBot (𝓝[{x : A | IsUnit x}] 0)]

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **Over a ring in which zero is a limit of units, a completely pseudometrisable topological
module all of whose submodules are closed is noetherian**, generalising
[Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.17, *if* direction. -/
theorem isNoetherian_of_forall_isClosed [TopologicalSpace M]
    [IsCompletelyPseudoMetrizableSpace M] [ContinuousAdd M] [ContinuousSMul A M]
    (h : ∀ N : Submodule A M, IsClosed (N : Set M)) : IsNoetherian A M := by
  refine monotone_stabilizes_iff_noetherian.mp fun f ↦ ?_
  let S : Submodule A M := ⨆ n, f n
  -- The union `S` of the chain is closed, hence completely pseudometrisable and Baire.
  have : IsCompletelyPseudoMetrizableSpace S := (h S).isCompletelyPseudoMetrizableSpace
  have : ContinuousAdd S := S.toAddSubmonoid.continuousAdd
  -- The members of the chain, seen inside `S`, are closed submodules covering `S`; as `S` is
  -- Baire, they are not all proper.
  obtain ⟨n, hn⟩ : ∃ n, (f n).comap S.subtype = ⊤ := by
    by_contra! hne
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_isClosed _
      (fun n ↦ by
        rw [Submodule.comap_coe, Submodule.coe_subtype]
        exact (h (f n)).preimage continuous_subtypeVal) hne
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed f f.monotone.directed_le).mp x.property
    exact hx n (Submodule.mem_comap.mpr hn)
  have hS : S ≤ f n := Submodule.comap_subtype_eq_top.mp hn
  exact ⟨n, fun m hm ↦ le_antisymm (f.monotone hm) ((le_iSup f m).trans hS)⟩

end TauCeti
