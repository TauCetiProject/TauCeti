/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.Topology.Algebra.IsUniformGroup.Submodule
public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits

/-!
# Modules over a ring with a zero sequence of units

Let `A` be a topological ring admitting a sequence of units converging to zero, such as a Tate ring.
Over such a ring a topological module has no proper submodule with nonempty interior
(Mathlib's `Submodule.eq_top_of_nonempty_interior'`, through the instance
`TauCeti.HasZeroSequenceOfUnits.nhdsWithin_isUnit_neBot`), and this file draws a consequence of
that for complete metrisable modules. The same fact gives the remaining implications of Wedhorn's
Theorem 6.16, in `TauCeti.Topology.Algebra.OpenMapping.Converse`.

A complete first-countable module all of whose submodules are closed is noetherian, the converse
half of Wedhorn's Proposition 6.17. Given an ascending chain of submodules, their union `S` is
closed, hence complete and so a Baire space. The members of the chain are closed in `S` and cover
it, so one of them has interior in `S`. That member is then an open submodule of `S`, hence all of
`S`, and the chain stops there.

Over a complete Hausdorff Tate ring the forward half, that every submodule of a noetherian module is
closed, is `TauCeti.Huber.isClosed_of_isNoetherian`; the two halves are assembled into Wedhorn's
equivalence in `TauCeti.Huber.isNoetherian_iff_forall_isClosed`.

## Main results

* `TauCeti.HasZeroSequenceOfUnits.isNoetherian_of_forall_isClosed`: a complete first-countable
  module whose submodules are all closed is noetherian.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.17.
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti

namespace HasZeroSequenceOfUnits

variable {A : Type*} [Ring A] [TopologicalSpace A] [HasZeroSequenceOfUnits A]

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **A complete first-countable module all of whose submodules are closed is noetherian**
([Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.17, *if* direction). -/
theorem isNoetherian_of_forall_isClosed [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
    [(𝓤 M).IsCountablyGenerated] [ContinuousSMul A M]
    (h : ∀ N : Submodule A M, IsClosed (N : Set M)) : IsNoetherian A M := by
  refine monotone_stabilizes_iff_noetherian.mp fun f ↦ ?_
  let S : Submodule A M := ⨆ n, f n
  -- The union `S` of the chain is closed, hence complete, hence (being metrisable) Baire.
  have : CompleteSpace S := (h S).completeSpace_coe
  -- The members of the chain, seen inside `S`, are closed and cover `S`.
  let C : ℕ → Submodule A S := fun n ↦ (f n).comap S.subtype
  have hC : ∀ n, IsClosed (C n : Set S) := fun n ↦ (h (f n)).preimage continuous_subtype_val
  have hcover : ⋃ n, (C n : Set S) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    exact (Submodule.mem_iSup_of_directed f f.monotone.directed_le).mp x.2
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hC hcover
  -- That member is open in `S`, hence all of `S`.
  have hS : S ≤ f n :=
    Submodule.comap_subtype_eq_top.mp (Submodule.eq_top_of_nonempty_interior' _ hn)
  exact ⟨n, fun m hm ↦ le_antisymm (f.monotone hm) ((le_iSup f m).trans hS)⟩

end HasZeroSequenceOfUnits

end TauCeti
