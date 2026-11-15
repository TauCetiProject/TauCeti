/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Steinberg
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.CharacterMap
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Steinberg
import all TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import all TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Steinberg
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.ToralClosure

/-!
# Indexed Steinberg maps on simply connected full-weight points

For an ordinary or graph-twisted index, `GraphTwistedIndex.scSteinberg` composes the integral
full-weight diagram action with the index's field Frobenius. It acts on the entire point group
of the full-weight Kostant toral closure, not just on its root-generated subgroup. This is the
point group of the simply connected Chevalley scheme by
`DynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup`; no additional carrier is defined here.

The map has the prescribed values on both signs of the simple roots and on the weight torus.
Its character pullback agrees with the independently defined `GraphTwistedIndex.datumSteinberg`,
and its twist-order iterate is Frobenius. These statements hold over any commutative value ring
of the indexed exponential characteristic, in particular over `ValidLieTypeIndex.Closure`.
No finiteness, simplicity, or generation assertion is used.

The construction specializes `kostantToralSteinberg` and the integral symmetries
`DynkinType.scModuleDiagramEquiv`. Character compatibility and the power law use the generic
whole-point theorems, without reconstructing an action from its values on root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.GraphTwistedIndex

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

attribute [local instance high] Algebra.toModule

variable (d : GraphTwistedIndex) (A : Type v) [CommRing A] [ExpChar A d.1.characteristic]

/-- The independently pinned Steinberg map on the full-weight simply connected point group:
the selected integral diagram action after the indexed field Frobenius. -/
def scSteinberg :=
  kostantToralSteinberg
    (d.1.dynkinType.lieBasis d.1.dynkinType_valid).rootGenerator
    (d.1.dynkinType.lieBasis d.1.dynkinType_valid).h
    (representation ℚ (d.1.dynkinType.lieAlgebra d.1.dynkinType_valid)
      (d.1.dynkinType.scModule d.1.dynkinType_valid))
    (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
    (d.1.dynkinType.kostantForm_apply_mem_scLattice d.1.dynkinType_valid)
    (d.1.dynkinType.isNilpotent_representation_scModule_rootGenerator d.1.dynkinType_valid)
    (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
    (d.1.dynkinType.scWeight d.1.dynkinType_valid)
    (DynkinType.diagramRootGeneratorPerm d.diagramPerm)
    (d.1.dynkinType.scModuleDiagramEquiv d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
    (fun _ => d.1.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
      d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
    (d.1.dynkinType.scModuleDiagramEquiv_representation_rootGenerator
      d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
    (DynkinType.diagramRootGeneratorPerm d.diagramPerm).surjective d.diagramPerm
    (fun _ _ hxy => d.1.dynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero
      d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry hxy)
    d.1.characteristic d.1.fieldExponent A

/-- On every point, the Steinberg map is integral lattice conjugation after entrywise
Frobenius. This characterizes it without a point-generation hypothesis. -/
@[simp]
theorem coe_scSteinberg (g) :
    (d.scSteinberg A g : Matrix.GeneralLinearGroup _ A) =
      kostantNumberedSymmetryMatrix
          (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
          (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
          (d.1.dynkinType.scModuleDiagramEquiv d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)
          (fun _ => d.1.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
            d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) A *
        Matrix.GeneralLinearGroup.map (iterateFrobenius A d.1.characteristic d.1.fieldExponent) g *
      (kostantNumberedSymmetryMatrix
          (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
          (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
          (d.1.dynkinType.scModuleDiagramEquiv d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)
          (fun _ => d.1.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
            d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) A)⁻¹ :=
  coe_kostantToralSteinberg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g

/-- The Steinberg map sends each signed simple root parameter to its selected diagram image
and raises the additive parameter to the indexed field order. -/
@[simp]
theorem scSteinberg_rootSubgroup (i : Fin d.1.rank ⊕ Fin d.1.rank) (u : Multiplicative A) :
    d.scSteinberg A
      (kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _ i A u) =
      kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _
        (DynkinType.diagramRootGeneratorPerm d.diagramPerm i) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  simpa only [scSteinberg, kostantToralRootSubgroupPoints,
    MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    d.1.fieldOrder_eq_characteristic_pow] using
    kostantToralSteinberg_kostantRootSubgroupMatrix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i u

/-- The character pullback is precisely the native root-datum Steinberg weight map.
In particular, triality acts contravariantly, rather than by the source-node permutation. -/
theorem isCharacterMap_scSteinberg :
    IsCharacterMap (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A)
      (d.scSteinberg A) d.datumSteinberg.weightMap := by
  have h : IsCharacterMap (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A)
      (d.scSteinberg A)
      ((d.1.characteristic ^ d.1.fieldExponent : ℕ) • LinearMap.funLeft ℤ ℤ d.diagramPerm) :=
    isCharacterMap_kostantNumberedSymmetryPoints_comp_frobenius
      _ _ _ _ _ _ _ _ (DynkinType.diagramRootGeneratorPerm d.diagramPerm) _ _
      (d.1.dynkinType.scModuleDiagramEquiv_representation_rootGenerator
        d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
      (DynkinType.diagramRootGeneratorPerm d.diagramPerm).surjective d.diagramPerm
      (fun _ _ hxy => d.1.dynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero
        d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry hxy) _ _ _
  have hw : ((d.1.characteristic ^ d.1.fieldExponent : ℕ) •
      LinearMap.funLeft ℤ ℤ d.diagramPerm) = d.datumSteinberg.weightMap := by
    simp only [datumSteinberg_weightMap, datumGraphAut_def,
      DynkinType.diagramAut_inv_weightMap, d.1.fieldOrder_eq_characteristic_pow,
      LinearMap.comp_smul, LinearMap.comp_id]
    -- Both linear maps are precomposition with the same forward node permutation.
    rfl
  -- Transport only the character parameter, leaving the whole-point construction fixed.
  exact Eq.mp (congrArg (IsCharacterMap _ (d.scSteinberg A)) hw) h

/-- The torus coordinates are raised to `q` and then relabelled by the inverse diagram action. -/
@[simp]
theorem scSteinberg_weightTorus (s : Fin d.1.rank → Aˣ) :
    d.scSteinberg A (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A s) =
      kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A
        (fun j => s (d.diagramPerm⁻¹ j) ^ d.1.fieldOrder) := by
  refine ((d.isCharacterMap_scSteinberg A).map_apply s).trans ?_
  apply congrArg (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A)
  funext j
  simp only [datumSteinberg_weightMap, datumGraphAut_def, LinearMap.comp_smul,
    LinearMap.comp_id, DynkinType.diagramAut_inv_weightMap, torusPointMap_nsmul,
    torusPointMap_funCongrLeft, MonoidHom.pow_apply, Pi.pow_apply, Equiv.Perm.inv_def]

/-- The native twist-order power of the indexed Steinberg map is `q^r`-Frobenius.
The Frobenius iteration index is the product of the field exponent and the twist order. -/
-- Select composition, rather than pointwise operations on bundled homomorphisms.
theorem scSteinberg_pow_twistOrder :
    (show _root_.Monoid.End _ from d.scSteinberg A) ^ d.twistOrder =
      kostantToralFrobenius _ _ _ _ _ _ _ _ d.1.characteristic
        (d.1.fieldExponent * d.twistOrder) A := by
  let γ := d.1.dynkinType.scToralDiagramAutPoints
    d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry A
  have hγ : γ ^ d.twistOrder = 1 :=
    d.1.dynkinType.scToralDiagramAutPoints_pow_eq_one
      d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry A d.diagramPerm_pow_twistOrder
  let G := ↥(kostantToralPointsSubgroup
      (d.1.dynkinType.lieBasis d.1.dynkinType_valid).rootGenerator
      (d.1.dynkinType.lieBasis d.1.dynkinType_valid).h
      (representation ℚ (d.1.dynkinType.lieAlgebra d.1.dynkinType_valid)
        (d.1.dynkinType.scModule d.1.dynkinType_valid))
      (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
      (d.1.dynkinType.kostantForm_apply_mem_scLattice d.1.dynkinType_valid)
      (d.1.dynkinType.isNilpotent_representation_scModule_rootGenerator d.1.dynkinType_valid)
      (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
      (d.1.dynkinType.scWeight d.1.dynkinType_valid) A)
  let φ := MulDistribMulAction.toMonoidEnd (MulAut G) G
  -- The evaluation action forgets only the inverse, so its image is the underlying
  -- endomorphism whose power occurs in the generic Steinberg power law.
  have hφ : φ γ = (show _root_.Monoid.End G from γ.toMonoidHom) := rfl
  have hp := (φ.map_pow γ d.twistOrder).symm.trans ((congrArg φ hγ).trans φ.map_one)
  simp only [hφ] at hp
  -- Identify the generic numbered symmetry with the indexed diagram action, so that
  -- the transported twist-order relation applies to the graph factor of that law.
  have hsym : kostantNumberedSymmetryPoints
      (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
      (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
      (d.1.dynkinType.scModuleDiagramEquiv d.1.dynkinType_valid
        d.diagramPerm_mem_diagramSymmetry)
      (fun _ => d.1.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
        d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) A _
      (map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
        _ _ _ _ _ _ _ _ (DynkinType.diagramRootGeneratorPerm d.diagramPerm) _ _
        (d.1.dynkinType.scModuleDiagramEquiv_representation_rootGenerator
          d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
        (DynkinType.diagramRootGeneratorPerm d.diagramPerm).surjective d.diagramPerm
        (fun _ _ hxy => d.1.dynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero
          d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry hxy) A) = γ := rfl
  dsimp only [scSteinberg]
  simp only [kostantToralSteinberg_pow, hsym, hp]
  exact one_mul _

end

end TauCeti.GraphTwistedIndex
