/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.GraphAutomorphism
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Graph automorphisms as based endomorphisms

Every pinned graph automorphism `TauCeti.DynkinType.chevalleyGraphAut` of the simply
connected Chevalley datum `TauCeti.DynkinType.scChevalleyDatum` is a based endomorphism
(`TauCeti.DynkinType.isBasedEndomorphism_chevalleyGraphAut`).

## Main results

* `TauCeti.DynkinType.isBasedEndomorphism_chevalleyGraphAut`: every pinned graph
  automorphism of `scChevalleyDatum` is a based endomorphism over every commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
-/

public section

namespace TauCeti.DynkinType

open Multiplicative

universe v

/-- Every pinned graph automorphism of `scChevalleyDatum` is a based endomorphism over every
commutative ring. -/
theorem isBasedEndomorphism_chevalleyGraphAut {t : DynkinType} (ht : t.Valid)
    {σ : Equiv.Perm (Fin t.rank)} (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    (t.scChevalleyDatum ht).IsBasedEndomorphism A
      (t.chevalleyGraphAut ht hσ A).toMonoidHom := by
  have hmap (α : Fin t.numRoots) :
      ((t.scChevalleyDatum ht).rootSubgroupPoints α A).range.map
          (t.chevalleyGraphAut ht hσ A).toMonoidHom =
        ((t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A).range := by
    let ε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom (t.chevalleyDiagramSign ht hσ α)
    refine MonoidHom.map_range_eq_range_of_comp_eq _ _ _
      ((ofAdd.surjective.comp (Units.mulLeft_bijective ε).surjective).comp toAdd.surjective)
      fun u => by simp [ε]
  exact ChevalleyDatum.isBasedEndomorphism_iff.mpr
    ⟨ChevalleyDatum.isStandardEndomorphism_iff.mpr fun α =>
        ⟨t.diagramRootPerm ht hσ α, hmap α⟩,
      fun α hα => ⟨t.diagramRootPerm ht hσ α,
        by simpa only [mem_posRoots, isPos_diagramRootPerm_iff] using hα, hmap α⟩⟩

end TauCeti.DynkinType
