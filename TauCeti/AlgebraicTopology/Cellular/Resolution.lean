/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.AlgebraicTopology.Cellular.Covering

/-!
# The cellular chains of a contractible free cover as a projective resolution

Let `p : E → B` be the quotient covering map of a free action of a group `G` on `E`
(`IsQuotientCoveringMap p G`), let `C` be a CW complex in the Hausdorff space `B`, and give
`p ⁻¹' C` the lifted CW structure `TauCeti.cwComplexPreimage`. With coefficients in a commutative
ring `R`, the cellular chain complex of `p ⁻¹' C` is a chain complex of representations of `G`,
`TauCeti.cellularChainComplexRep`, in which `g` acts by the chain map of translation by `g`, and
each of its terms is free over `R[G]` (`TauCeti.cellularChainRepIsoFree`), hence projective
(`TauCeti.projective_cellularChainComplexRep_X`).

Translations are cellular, and the augmentation of cellular chains is natural under cellular maps,
so the augmentation is a morphism of representations to the trivial representation
(`TauCeti.cellularAugmentationRep`). If `p ⁻¹' C` is contractible, the augmented cellular chain
complex is exact (`TauCeti.quasiIso_cellularChainComplexAugmentation`), so the cellular chains of
`p ⁻¹' C` form a projective resolution of the trivial representation of `G` over `R`
(`TauCeti.cellularResolution`).

This applies to the universal cover of a `K(G, 1)` CW complex: if `B` carries a CW structure on
the whole space and is aspherical, and `E` is simply connected, then `E` is weakly contractible, and
since it has CW type, it is contractible by Whitehead's theorem
(`IsCoveringMap.contractibleSpace_preimage_univ_of_isAspherical`, in
`TauCeti.AlgebraicTopology.EilenbergMacLane.Contractible`). The group acting is `G`, acting on `E`
by the given action; Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` identifies `G` with
the opposite of the fundamental group of `B`. This resolution is the input for identifying the
cellular homology and cohomology of `B` with the group homology and cohomology of `G`.

## Main definitions

* `TauCeti.cellularAugmentationRep`: the augmentation of the lifted cellular chains in degree
  `0`, as a morphism to the trivial representation.
* `TauCeti.cellularChainComplexRepAugmentation`: the augmentation as a chain map of complexes of
  representations.
* `TauCeti.cellularResolution`: for contractible `p ⁻¹' C`, the projective resolution of the
  trivial representation by the lifted cellular chains.

## Main results

* `TauCeti.quasiIso_cellularChainComplexRepAugmentation`: for contractible `p ⁻¹' C`, the
  augmentation is a quasi-isomorphism.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4, Proposition 4.1, and
  Section II.4.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  (C : Set B) {G : Type w} [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G)
  [T2Space B] [CWComplex C] (R : Type w) [CommRing R]

/-- The **augmentation** of the cellular chains of the lift `p ⁻¹' C` of `C` in degree `0`, as a
morphism to the trivial representation. -/
def cellularAugmentationRep :
    Rep.of (cellularChainRepresentation C hG R 0) ⟶ Rep.trivial R G R :=
  letI := cwComplexPreimage C hG.isCoveringMap
  haveI := hG.isCoveringMap.t2Space
  eqToHom (congrArg Rep.of (cellularChainRepresentation_def C hG R 0)) ≫
    cellularActionAugmentation (p ⁻¹' C) (preimageSMul C hG)
      (isCellular_preimageSMul C hG) (preimageSMul_one C hG) (preimageSMul_mul C hG) R

/-- The underlying linear map of `TauCeti.cellularAugmentationRep` is the augmentation of the
cellular chains of `p ⁻¹' C`. -/
@[simp]
lemma cellularAugmentationRep_hom_toLinearMap :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    (cellularAugmentationRep C hG R).hom.toLinearMap =
      (cellularAugmentation (p ⁻¹' C) (ModuleCat.of R R)).hom := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  unfold cellularAugmentationRep
  have h := congrArg ModuleCat.Hom.hom
    ((forget₂ (Rep R G) (ModuleCat R)).map_comp
      (eqToHom (congrArg Rep.of (cellularChainRepresentation_def C hG R 0)))
      (cellularActionAugmentation (p ⁻¹' C) (preimageSMul C hG)
        (isCellular_preimageSMul C hG) (preimageSMul_one C hG) (preimageSMul_mul C hG) R))
  rw [eqToHom_map, eqToHom_refl, Category.id_comp] at h
  simp only [Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom] at h
  exact h.trans (cellularActionAugmentation_hom_toLinearMap _ _ _ _ _ _)

/-- The equivariant augmentation vanishes on the boundaries of lifted `1`-cells. -/
@[reassoc (attr := simp)]
lemma cellularDifferentialRep_comp_cellularAugmentationRep :
    cellularDifferentialRep C hG R 0 ≫ cellularAugmentationRep C hG R = 0 := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  unfold cellularAugmentationRep
  rw [cellularDifferentialRep_def, Category.assoc, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp,
    cellularActionDifferential_comp_cellularActionAugmentation, Limits.comp_zero]

/-- The **augmentation of the lifted cellular chain complex**, as a chain map of complexes of
representations to the trivial representation placed in degree `0`. -/
def cellularChainComplexRepAugmentation :
    cellularChainComplexRep C hG R ⟶
      (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  letI := cwComplexPreimage C hG.isCoveringMap
  haveI := hG.isCoveringMap.t2Space
  eqToHom (cellularChainComplexRep_def C hG R) ≫
    cellularActionComplexAugmentation (p ⁻¹' C) (preimageSMul C hG)
      (isCellular_preimageSMul C hG) (preimageSMul_one C hG) (preimageSMul_mul C hG) R

/-- In degree `0` the augmentation of the lifted cellular chain complex is
`TauCeti.cellularAugmentationRep`. -/
@[simp]
lemma cellularChainComplexRepAugmentation_f_zero :
    (cellularChainComplexRepAugmentation C hG R).f 0 =
      eqToHom (cellularChainComplexRep_X C hG R 0) ≫ cellularAugmentationRep C hG R := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  unfold cellularChainComplexRepAugmentation cellularAugmentationRep
  rw [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    cellularActionComplexAugmentation_f_zero, eqToHom_trans_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (eqToHom_trans _ _))

/-- **The augmented lifted cellular chain complex of a contractible cover is exact.** -/
theorem quasiIso_cellularChainComplexRepAugmentation [ContractibleSpace (p ⁻¹' C)] :
    QuasiIso (cellularChainComplexRepAugmentation C hG R) := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  unfold cellularChainComplexRepAugmentation
  have := quasiIso_cellularActionComplexAugmentation (p ⁻¹' C) (preimageSMul C hG)
    (isCellular_preimageSMul C hG) (preimageSMul_one C hG) (preimageSMul_mul C hG) R
  infer_instance

/-- The terms of the lifted cellular chain complex are projective representations: each is free
over the group ring, with basis one chosen lift of each cell of `C`. -/
instance projective_cellularChainComplexRep_X (n : ℕ) :
    Projective ((cellularChainComplexRep C hG R).X n) := by
  let := cwComplexPreimage C hG.isCoveringMap
  choose s hs using fun i ↦
    exists_cellPreimageEquiv_fst_eq C hG.isCoveringMap hG.surjective (n := n) i
  rw [cellularChainComplexRep_X]
  exact Projective.of_iso (cellularChainRepIsoFree C hG R s hs).symm inferInstance

/-- **The cellular chains of a contractible free cover are a projective resolution** of the
trivial representation of `G` over `R`: if the lift `p ⁻¹' C` of the CW complex `C` is
contractible, its cellular chain complex, on which `G` acts through translation of the lifted
cells, is a complex of free representations whose augmentation is a quasi-isomorphism. -/
def cellularResolution [ContractibleSpace (p ⁻¹' C)] :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellularChainComplexRep C hG R
  π := cellularChainComplexRepAugmentation C hG R
  quasiIso := quasiIso_cellularChainComplexRepAugmentation C hG R

/-- The complex of `TauCeti.cellularResolution` is the lifted cellular chain complex. -/
@[simp]
lemma cellularResolution_complex [ContractibleSpace (p ⁻¹' C)] :
    (cellularResolution C hG R).complex = cellularChainComplexRep C hG R :=
  (rfl)

-- A public statement cannot unfold the unexposed body of `TauCeti.cellularResolution`, so the
-- source of its `π` is not definitionally `cellularChainComplexRep C hG R` there, and the
-- statement transports along `cellularResolution_complex`. The proof does see the body: there the
-- transport is `eqToHom rfl`, definitionally the identity, so it is `Category.id_comp`.
/-- The augmentation of `TauCeti.cellularResolution` is that of the lifted cellular chain
complex. -/
@[simp]
lemma cellularResolution_π [ContractibleSpace (p ⁻¹' C)] :
    (cellularResolution C hG R).π =
      eqToHom (cellularResolution_complex C hG R) ≫ cellularChainComplexRepAugmentation C hG R :=
  (Category.id_comp _).symm

end TauCeti
