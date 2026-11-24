/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.Topology.FilledIn
-- Provides `NormedSpace.toLocallyConvexSpace`, hence `LocallyConnectedSpace E`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected

/-!
# Normed-space operations on sets filled in an open set

`TauCeti/Topology/FilledIn.lean` defines when a set `K` is filled in an ambient set `Ω`
(`TauCeti.IsFilledIn K Ω`, meaning no connected component of `Ω \ K` has compact closure inside
`Ω`) and defines `TauCeti.fillIn K Ω`, the union of `K` with all relatively compact components of
`Ω \ K` in `Ω`.

In a real normed space, boundedness of filled hulls (`TauCeti.isBounded_filledHull`) and
connectedness of punctured open sets in real dimension greater than one
(`TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`) supply two further
operations on domain-relative filled sets, independent of compact exhaustions:

* In a proper real normed space, filling a compact set `K` inside an open set `Ω` produces a
  compact set (`IsCompact.fillIn`), combining `IsClosed.fillIn` with enclosure inside
  `TauCeti.filledHull K` (`TauCeti.fillIn_subset_filledHull`).
* When `1 < Module.rank ℝ E` and `Ω \ K` is open, inserting a single point `z` into a set `K` filled
  in `Ω` preserves `TauCeti.IsFilledIn` (`TauCeti.IsFilledIn.insert`), since puncturing a connected
  component of `Ω \ K` at `z` leaves it preconnected.

Both results enter the topological identification of `TauCeti.holomorphicHull Ω K` in
`TauCeti/Analysis/Complex/Runge/Approximation.lean`.

## Main results

* `IsCompact.fillIn`: filling a compact set inside an open set produces a compact set.
* `TauCeti.IsFilledIn.insert`: inserting a point preserves `TauCeti.IsFilledIn` in real dimension
  greater than one.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Lemma 11.3.
-/

public section

open Metric Set

section CompactFill

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- In a proper real normed space, filling a compact set `K` inside an open set `Ω` produces a
compact set. -/
protected theorem IsCompact.fillIn {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) :
    IsCompact (TauCeti.fillIn K Ω) :=
  isCompact_of_isClosed_isBounded (hK.isClosed.fillIn hΩ)
    ((isBounded_filledHull.mpr hK.isBounded).subset
      (fillIn_subset_filledHull (hΩ.sdiff hK.isClosed)))

end CompactFill

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space of dimension greater than one, inserting a point into `K` when `Ω \ K`
is open preserves `TauCeti.IsFilledIn K Ω`. -/
protected theorem IsFilledIn.insert {K Ω : Set E} (h : IsFilledIn K Ω)
    (hrank : 1 < Module.rank ℝ E) (hΩK : IsOpen (Ω \ K)) (z : E) :
    IsFilledIn (insert z K) Ω := by
  refine isFilledIn_iff.mpr fun x hx ⟨hcpt, hsub⟩ => ?_
  have hxΩK : x ∈ Ω \ K := ⟨hx.1, fun hxK => hx.2 (mem_insert_of_mem z hxK)⟩
  have hxz : x ≠ z := fun hxz => hx.2 (hxz ▸ mem_insert z K)
  let C := connectedComponentIn (Ω \ K) x
  let C₁ := connectedComponentIn (Ω \ insert z K) x
  have hpre : IsPreconnected (C \ {z}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank (E := E) hrank
      hΩK.connectedComponentIn isPreconnected_connectedComponentIn
      isClosed_singleton (finite_singleton z).isDiscrete
  have hC_sub : C \ {z} ⊆ C₁ :=
    hpre.subset_connectedComponentIn ⟨mem_connectedComponentIn hxΩK, hxz⟩ fun w ⟨hwC, hwz⟩ =>
      ⟨(connectedComponentIn_subset _ _ hwC).1,
        fun hw_ins => hw_ins.elim hwz (connectedComponentIn_subset _ _ hwC).2⟩
  by_cases hzC : z ∈ C
  · have hzΩ : z ∈ Ω := (connectedComponentIn_subset _ _ hzC).1
    have hcl_sub : closure C ⊆ insert z (closure C₁) := by
      have hC_ins : C ⊆ insert z C₁ := fun w hw => by
        by_cases hwz : w = z
        · exact mem_insert_iff.mpr (Or.inl hwz)
        · exact mem_insert_of_mem z (hC_sub ⟨hw, hwz⟩)
      exact (closure_mono hC_ins).trans <| by
        rw [insert_eq, closure_union, isClosed_singleton.closure_eq, ← insert_eq]
    exact isFilledIn_iff.mp h x hxΩK
      ⟨(hcpt.insert z).of_isClosed_subset isClosed_closure hcl_sub,
        hcl_sub.trans (insert_subset_iff.mpr ⟨hzΩ, hsub⟩)⟩
  · have hC_eq : connectedComponentIn (Ω \ K) x = C₁ :=
      Subset.antisymm ((sdiff_singleton_eq_self hzC).symm.trans_subset hC_sub)
        (connectedComponentIn_mono x (sdiff_subset_sdiff Subset.rfl (subset_insert z K)))
    exact isFilledIn_iff.mp h x hxΩK ⟨hC_eq.symm ▸ hcpt, hC_eq.symm ▸ hsub⟩

end TauCeti
