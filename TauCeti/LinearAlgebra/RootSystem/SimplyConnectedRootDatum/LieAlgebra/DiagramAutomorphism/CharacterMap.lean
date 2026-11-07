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

The proof specializes the weight-component compatibility of `scModuleDiagramEquiv` and the
generic toral-closure character-map theorem. In particular it does not require the diagram
action to permute the weight basis, nor generation of the point group by root subgroups.

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
  have h := isCharacterMap_kostantNumberedSymmetryPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
    (t.kostantForm_apply_mem_scLattice ht)
    (t.isNilpotent_representation_scModule_rootGenerator ht)
    (t.scWeightBasis ht) (t.scWeight ht) (diagramRootGeneratorPerm σ)
    (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    (t.scModuleDiagramEquiv_representation_rootGenerator ht hσ)
    (diagramRootGeneratorPerm σ).surjective σ
    (fun _ _ hxy => t.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero ht hσ hxy) A
  have hφ : (diagramAut ht hσ)⁻¹.toHom.weightMap = LinearMap.funLeft ℤ ℤ σ := by
    rw [diagramAut_inv_weightMap]
    apply LinearMap.ext
    intro x
    exact LinearEquiv.funCongrLeft_apply ℤ ℤ σ x
  -- Transport only the character-map argument: rewriting the whole specialized point action
  -- with `rw [hφ]` causes an elaboration timeout.
  apply (congrArg (IsCharacterMap _ _) hφ).mpr
  rw [isCharacterMap_iff]
  intro s
  apply Subtype.ext
  simpa only [MulEquiv.coe_toMonoidHom, coe_scToralDiagramAutPoints,
    coe_kostantNumberedSymmetryPoints] using congrArg Subtype.val (h.map_apply s)

end TauCeti.DynkinType
