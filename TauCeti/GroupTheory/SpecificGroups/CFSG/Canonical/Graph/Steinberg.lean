/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Steinberg
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup
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
On every root subgroup, `scSteinberg_chevalleyToralRootSubgroupPoints` sends the parameter `u`
at `α` to `ε u ^ q` at the diagram image of `α`, where `ε` is the sign of the pinned diagram
action at the source root. At nonsimple roots this sign need not be one. The formula combines
`DynkinType.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints` with matrix Frobenius
naturality, without a point-generation assumption.

Its character pullback agrees with the independently defined `GraphTwistedIndex.datumSteinberg`,
and its twist-order iterate is Frobenius. These statements hold over any commutative value ring
of the indexed exponential characteristic, in particular over `ValidLieTypeIndex.Closure`.
No finiteness, simplicity, or generation assertion is used.

The construction specializes `kostantToralSteinberg` and the integral symmetries
`DynkinType.scModuleDiagramEquiv`. Character compatibility and the power law use the generic
whole-point theorems, without reconstructing an action from its values on root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29, and Chapter 11.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.GraphTwistedIndex

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

attribute [local instance high] Algebra.toModule

variable (d : GraphTwistedIndex) (A : Type v) [CommRing A] [ExpChar A d.val.characteristic]

/-- The independently pinned Steinberg map on the full-weight simply connected point group:
the selected integral diagram action after the indexed field Frobenius. -/
def scSteinberg :=
  kostantToralSteinberg
    (d.val.dynkinType.lieBasis d.val.dynkinType_valid).rootGenerator
    (d.val.dynkinType.lieBasis d.val.dynkinType_valid).h
    (representation ℚ (d.val.dynkinType.lieAlgebra d.val.dynkinType_valid)
      (d.val.dynkinType.scModule d.val.dynkinType_valid))
    (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
    (d.val.dynkinType.kostantForm_apply_mem_scLattice d.val.dynkinType_valid)
    (d.val.dynkinType.isNilpotent_representation_scModule_rootGenerator d.val.dynkinType_valid)
    (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
    (d.val.dynkinType.scWeight d.val.dynkinType_valid)
    (DynkinType.diagramRootGeneratorPerm d.diagramPerm)
    (d.val.dynkinType.scModuleDiagramEquiv d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
    (fun _ => d.val.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
      d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
    (d.val.dynkinType.scModuleDiagramEquiv_representation_rootGenerator
      d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
    (DynkinType.diagramRootGeneratorPerm d.diagramPerm).surjective d.diagramPerm
    (fun _ _ hxy => d.val.dynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero
      d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry hxy)
    d.val.characteristic d.val.fieldExponent A

/-- On every point, the Steinberg map is integral lattice conjugation after entrywise
Frobenius. This characterizes it without a point-generation hypothesis. -/
@[simp]
theorem coe_scSteinberg (g) :
    (d.scSteinberg A g : Matrix.GeneralLinearGroup _ A) =
      kostantNumberedSymmetryMatrix
          (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
          (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
          (d.val.dynkinType.scModuleDiagramEquiv d.val.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)
          (fun _ => d.val.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
            d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) A *
        Matrix.GeneralLinearGroup.map (iterateFrobenius A d.val.characteristic d.val.fieldExponent)
            g *
      (kostantNumberedSymmetryMatrix
          (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
          (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
          (d.val.dynkinType.scModuleDiagramEquiv d.val.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)
          (fun _ => d.val.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
            d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) A)⁻¹ :=
  coe_kostantToralSteinberg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g

/-- The Steinberg map sends each signed simple root parameter to its selected diagram image
and raises the additive parameter to the indexed field order. -/
@[simp]
theorem scSteinberg_rootSubgroup (i : Fin d.val.rank ⊕ Fin d.val.rank) (u : Multiplicative A) :
    d.scSteinberg A
      (kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _ i A u) =
      kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _
        (DynkinType.diagramRootGeneratorPerm d.diagramPerm i) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.val.fieldOrder)) := by
  simpa only [scSteinberg, kostantToralRootSubgroupPoints,
    MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    d.val.fieldOrder_eq_characteristic_pow] using
    kostantToralSteinberg_kostantRootSubgroupMatrix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i u

/-- On every root subgroup, the indexed Steinberg map applies field-order Frobenius to the
parameter and then the signed diagram action. The sign is indexed on the source root. -/
@[simp]
theorem scSteinberg_chevalleyToralRootSubgroupPoints
    (α : Fin d.val.dynkinType.numRoots) (u : Multiplicative A) :
    d.scSteinberg A
      (DynkinType.chevalleyToralRootSubgroupPoints
        (representation ℚ (d.val.dynkinType.lieAlgebra d.val.dynkinType_valid)
          (d.val.dynkinType.scModule d.val.dynkinType_valid))
        (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
        (d.val.dynkinType.kostantForm_apply_mem_scLattice d.val.dynkinType_valid)
        (d.val.dynkinType.isNilpotent_representation_scModule_rootGenerator d.val.dynkinType_valid)
        (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
        (d.val.dynkinType.scWeight d.val.dynkinType_valid) α A u) =
      DynkinType.chevalleyToralRootSubgroupPoints _ _ _ _ _ _
        (d.val.dynkinType.diagramRootPerm d.val.dynkinType_valid
          d.diagramPerm_mem_diagramSymmetry α) A
        (Multiplicative.ofAdd
          (((d.val.dynkinType.chevalleyDiagramSign d.val.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry α : ℤ) : A) *
            Multiplicative.toAdd u ^ d.val.fieldOrder)) := by
  have hγ := congrArg Subtype.val
    (d.val.dynkinType.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints
      d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry α A
        (Multiplicative.toAdd u ^ d.val.characteristic ^ d.val.fieldExponent))
  simp only [DynkinType.coe_scToralDiagramAutPoints] at hγ
  have hp := DynkinType.map_iterateFrobenius_chevalleyToralRootSubgroupPoints
    (representation ℚ (d.val.dynkinType.lieAlgebra d.val.dynkinType_valid)
      (d.val.dynkinType.scModule d.val.dynkinType_valid))
    (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
    (d.val.dynkinType.kostantForm_apply_mem_scLattice d.val.dynkinType_valid)
    (d.val.dynkinType.isNilpotent_representation_scModule_rootGenerator d.val.dynkinType_valid)
    (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
    (d.val.dynkinType.scWeight d.val.dynkinType_valid)
    d.val.characteristic d.val.fieldExponent A α u
  apply Subtype.ext
  refine (d.coe_scSteinberg A _).trans ?_
  simpa only [d.val.fieldOrder_eq_characteristic_pow] using
    (congrArg (fun g => _ * g * _) hp).trans hγ

/-- The character pullback is precisely the native root-datum Steinberg weight map.
In particular, triality acts contravariantly, rather than by the source-node permutation. -/
theorem isCharacterMap_scSteinberg :
    IsCharacterMap (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A)
      (d.scSteinberg A) d.datumSteinberg.weightMap := by
  have h : IsCharacterMap (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A)
      (d.scSteinberg A)
      ((d.val.characteristic ^ d.val.fieldExponent : ℕ) • LinearMap.funLeft ℤ ℤ d.diagramPerm) :=
    isCharacterMap_kostantNumberedSymmetryPoints_comp_frobenius
      _ _ _ _ _ _ _ _ (DynkinType.diagramRootGeneratorPerm d.diagramPerm) _ _
      (d.val.dynkinType.scModuleDiagramEquiv_representation_rootGenerator
        d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
      (DynkinType.diagramRootGeneratorPerm d.diagramPerm).surjective d.diagramPerm
      (fun _ _ hxy => d.val.dynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero
        d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry hxy) _ _ _
  have hw : ((d.val.characteristic ^ d.val.fieldExponent : ℕ) •
      LinearMap.funLeft ℤ ℤ d.diagramPerm) = d.datumSteinberg.weightMap := by
    simp only [datumSteinberg_weightMap, datumGraphAut_def,
      DynkinType.diagramAut_inv_weightMap, d.val.fieldOrder_eq_characteristic_pow,
      LinearMap.comp_smul, LinearMap.comp_id]
    -- Both linear maps are precomposition with the same forward node permutation.
    rfl
  -- Transport only the character parameter, leaving the whole-point construction fixed.
  exact Eq.mp (congrArg (IsCharacterMap _ (d.scSteinberg A)) hw) h

/-- The torus coordinates are raised to `q` and then relabelled by the inverse diagram action. -/
@[simp]
theorem scSteinberg_weightTorus (s : Fin d.val.rank → Aˣ) :
    d.scSteinberg A (kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A s) =
      kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A
        (fun j => s (d.diagramPerm⁻¹ j) ^ d.val.fieldOrder) := by
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
      kostantToralFrobenius _ _ _ _ _ _ _ _ d.val.characteristic
        (d.val.fieldExponent * d.twistOrder) A := by
  let γ := d.val.dynkinType.scToralDiagramAutPoints
    d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry A
  have hγ : γ ^ d.twistOrder = 1 :=
    d.val.dynkinType.scToralDiagramAutPoints_pow_eq_one
      d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry A d.diagramPerm_pow_twistOrder
  let G := ↥(kostantToralPointsSubgroup
      (d.val.dynkinType.lieBasis d.val.dynkinType_valid).rootGenerator
      (d.val.dynkinType.lieBasis d.val.dynkinType_valid).h
      (representation ℚ (d.val.dynkinType.lieAlgebra d.val.dynkinType_valid)
        (d.val.dynkinType.scModule d.val.dynkinType_valid))
      (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
      (d.val.dynkinType.kostantForm_apply_mem_scLattice d.val.dynkinType_valid)
      (d.val.dynkinType.isNilpotent_representation_scModule_rootGenerator d.val.dynkinType_valid)
      (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
      (d.val.dynkinType.scWeight d.val.dynkinType_valid) A)
  let φ := MulDistribMulAction.toMonoidEnd (MulAut G) G
  -- The evaluation action forgets only the inverse, so its image is the underlying
  -- endomorphism whose power occurs in the generic Steinberg power law.
  have hφ : φ γ = (show _root_.Monoid.End G from γ.toMonoidHom) := rfl
  have hp := (φ.map_pow γ d.twistOrder).symm.trans ((congrArg φ hγ).trans φ.map_one)
  simp only [hφ] at hp
  -- Identify the generic numbered symmetry with the indexed diagram action, so that
  -- the transported twist-order relation applies to the graph factor of that law.
  have hsym : kostantNumberedSymmetryPoints
      (d.val.dynkinType.scLattice d.val.dynkinType_valid).toAddSubgroup
      (d.val.dynkinType.scWeightBasis d.val.dynkinType_valid)
      (d.val.dynkinType.scModuleDiagramEquiv d.val.dynkinType_valid
        d.diagramPerm_mem_diagramSymmetry)
      (fun _ => d.val.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
        d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) A _
      (map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
        _ _ _ _ _ _ _ _ (DynkinType.diagramRootGeneratorPerm d.diagramPerm) _ _
        (d.val.dynkinType.scModuleDiagramEquiv_representation_rootGenerator
          d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)
        (DynkinType.diagramRootGeneratorPerm d.diagramPerm).surjective d.diagramPerm
        (fun _ _ hxy => d.val.dynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero
          d.val.dynkinType_valid d.diagramPerm_mem_diagramSymmetry hxy) A) = γ := rfl
  dsimp only [scSteinberg]
  simp only [kostantToralSteinberg_pow, hsym, hp]
  exact one_mul _

end

end TauCeti.GraphTwistedIndex
