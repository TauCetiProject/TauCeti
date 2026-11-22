/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Diagram automorphisms as based endomorphisms

Every diagram automorphism `TauCeti.DynkinType.scChevalleyDatumDiagramAut` of the simply
connected Chevalley datum `TauCeti.DynkinType.scChevalleyDatum` is a based endomorphism
(`TauCeti.DynkinType.isBasedEndomorphism_scChevalleyDatumDiagramAut`).

## Main results

* `TauCeti.DynkinType.isBasedEndomorphism_scChevalleyDatumDiagramAut`: every diagram
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

/-- Every diagram automorphism of `scChevalleyDatum` is a based endomorphism over every
commutative ring. -/
theorem isBasedEndomorphism_scChevalleyDatumDiagramAut {t : DynkinType} (ht : t.Valid)
    {σ : Equiv.Perm (Fin t.rank)} (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    (t.scChevalleyDatum ht).IsBasedEndomorphism A
      (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom := by
  have hmap (α : Fin t.numRoots) :
      ((t.scChevalleyDatum ht).rootSubgroupPoints α A).range.map
          (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom =
        ((t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A).range := by
    let ε : Aˣ := Units.map (Int.castRingHom A).toMonoidHom (t.chevalleyDiagramSign ht hσ α)
    refine MonoidHom.map_range_eq_of_surjective _ _ _
      ((ofAdd.surjective.comp (Units.mulLeft_bijective ε).surjective).comp toAdd.surjective)
      fun u => by
        simpa [ε] using t.scChevalleyDatumDiagramAut_rootSubgroupPoints ht hσ α A (toAdd u)
  exact ChevalleyDatum.isBasedEndomorphism_iff.mpr
    ⟨ChevalleyDatum.isStandardEndomorphism_iff.mpr fun α =>
        ⟨t.diagramRootPerm ht hσ α, hmap α⟩,
      fun α hα => ⟨t.diagramRootPerm ht hσ α,
        (t.diagramRootPerm_mem_posRoots_iff ht hσ α).mpr hα, hmap α⟩⟩

end TauCeti.DynkinType
