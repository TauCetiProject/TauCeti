/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.ToralClosure
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism

/-!
# Character maps of the full-weight diagram action

The character pullback of `scToralDiagramAutPoints` on the represented weight torus is the
weight map of the inverse root-datum diagram automorphism.
To compute the pullback of its composite with Frobenius, combine
`isCharacterMap_scToralDiagramAutPoints` with `isCharacterMap_kostantToralFrobenius` via
`IsCharacterMap.comp`, obtaining `p ^ k • (diagramAut σ)⁻¹.weightMap`.

The proof uses the weight-torus action formula and identifies inverse relabelling with the
dual of the diagram weight map. It does not require the diagram action to permute the weight
basis, nor generation of the point group by root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} (ht : t.Valid) {σ : Equiv.Perm (Fin t.rank)}

/-- On the full-weight toral closure, the pinned diagram action has character pullback equal
to the weight map of the inverse diagram automorphism of the simply connected root datum. -/
theorem isCharacterMap_scToralDiagramAutPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    IsCharacterMap
      (kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A)
      (t.scToralDiagramAutPoints ht hσ A).toMonoidHom
      (diagramAut ht hσ)⁻¹.toHom.weightMap := by
  refine isCharacterMap_iff.mpr fun s => ?_
  have hs : torusPointMap (diagramAut ht hσ)⁻¹.toHom.weightMap s =
      fun j => s (σ⁻¹ j) := by
    funext j
    have hsingle : LinearMap.funLeft ℤ ℤ σ (Pi.single j 1) =
        (Pi.single (σ.symm j) 1 : Fin t.rank → ℤ) :=
      Pi.single_comp_equiv σ j 1
    simp only [torusPointMap_apply, diagramAut_inv_weightMap, LinearEquiv.coe_coe,
      LinearEquiv.funCongrLeft_apply, hsingle, torusCharacter_single, zpow_one,
      Equiv.Perm.inv_def]
  simpa only [MulEquiv.coe_toMonoidHom, hs] using
    t.scToralDiagramAutPoints_kostantToralWeightTorusPoints ht hσ A s

end TauCeti.DynkinType
