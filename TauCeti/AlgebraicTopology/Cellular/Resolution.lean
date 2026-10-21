/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.Cellular.Covering
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# The cellular chains of an acyclic free `G`-CW complex are a projective resolution

Let `p : E → B` be the quotient covering map of a free action of a group `G` on `E`
(`IsQuotientCoveringMap p G`), and let `C` be a CW complex in the Hausdorff space `B`. The lifted
CW structure on `p ⁻¹' C` has its cells permuted freely by `G`, so its cellular chain complex with
coefficients in a commutative ring `R` is a complex of free representations of `G`
(`TauCeti.cellularChainComplexRep`, `TauCeti.cellularChainRepIsoFree`).

The augmentation `TauCeti.cellularAugmentation` of the cellular chains of `p ⁻¹' C` is natural
under cellular maps, so it commutes with the action of `G` by translations, and it is a morphism
of representations onto the trivial representation (`TauCeti.cellularAugmentationRep`). If the
lift `p ⁻¹' C` is path connected and its singular homology vanishes in positive degrees, the
augmented cellular chain complex is exact
(`TauCeti.quasiIso_cellularChainComplexRepAugmentation`): forgetting the action, this is the
exactness of the augmented cellular chains of an acyclic CW complex
(`TauCeti.quasiIso_cellularChainComplexAugmentation`). Hence the cellular chains of `p ⁻¹' C` are a
projective resolution of the trivial representation (`TauCeti.cellularResolution`).

The hypotheses are those of the universal cover of a `K(G, 1)` CW complex `B`, with `C` the whole
space: the deck group acts freely, and the cover, all of whose homotopy groups vanish, has
vanishing singular homology in positive degrees. Milnor's classifying space is treated this way in
`TauCeti.classifyingSpaceCellularResolution`.

## Main definitions

* `TauCeti.cellularAugmentationRep`: the augmentation of the cellular chains of the lift, as a
  morphism of representations onto the trivial representation.
* `TauCeti.cellularChainComplexRepAugmentation`: the augmentation as a morphism of complexes of
  representations.
* `TauCeti.cellularResolution`: the cellular chains of an acyclic lift as a projective resolution
  of the trivial representation.

## Main results

* `TauCeti.quasiIso_cellularChainComplexRepAugmentation`: the augmentation of an acyclic lift is
  a quasi-isomorphism.
* `TauCeti.projective_cellularChainComplexRep_X`: the cellular chain groups of the lift are
  projective representations.
* `TauCeti.cellularResolution_complex` and `TauCeti.cellularResolution_π`: the complex and the
  augmentation of the resolution.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4, free `G`-complexes
  and the resolutions they give.
-/
public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex AlgebraicTopology

universe w

namespace TauCeti

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  (C : Set B) {G : Type w} [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G)

variable [T2Space B] [CWComplex C] (R : Type w) [CommRing R]

/-- **The augmentation of the cellular chains of the lift as a morphism of representations**: the
augmentation `TauCeti.cellularAugmentation` of the cellular chains of `p ⁻¹' C` is invariant under
the translations, which are cellular. -/
def cellularAugmentationRep :
    Rep.of (cellularChainRepresentation C hG R 0) ⟶ Rep.trivial R G R :=
  letI := cwComplexPreimage C hG.isCoveringMap
  haveI := hG.isCoveringMap.t2Space
  Rep.ofHom
    { toLinearMap := (cellularAugmentation (p ⁻¹' C) (ModuleCat.of R R)).hom
      isIntertwining' g := by
        ext x
        simp only [cellularChainRepresentation_apply]
        exact ConcreteCategory.congr_hom (cellularChainGroupMap_comp_cellularAugmentation
          (p ⁻¹' C) (ModuleCat.of R R) (p ⁻¹' C) (isCellular_preimageSMul C hG g)) x }

/-- The underlying linear map of `TauCeti.cellularAugmentationRep` is the augmentation of the
cellular chains of the lift. -/
@[simp]
lemma cellularAugmentationRep_hom_toLinearMap :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    (cellularAugmentationRep C hG R).hom.toLinearMap =
      (cellularAugmentation (p ⁻¹' C) (ModuleCat.of R R)).hom :=
  (rfl)

/-- Forgetting the action, `TauCeti.cellularAugmentationRep` is the augmentation of the cellular
chains of the lift. -/
lemma forget₂_map_cellularAugmentationRep :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map (cellularAugmentationRep C hG R) =
      cellularAugmentation (p ⁻¹' C) (ModuleCat.of R R) :=
  (rfl)

/-- The augmentation vanishes on the boundaries of lifted `1`-cells. -/
@[reassoc (attr := simp)]
lemma cellularDifferentialRep_comp_cellularAugmentationRep :
    cellularDifferentialRep C hG R 0 ≫ cellularAugmentationRep C hG R = 0 := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  ext x
  simp only [Rep.hom_comp_toLinearMap, cellularDifferentialRep_hom_toLinearMap,
    cellularAugmentationRep_hom_toLinearMap]
  exact ConcreteCategory.congr_hom
    (cellularDifferential_comp_cellularAugmentation (p ⁻¹' C) (ModuleCat.of R R)) x

/-- **The augmented cellular chain complex of the lift**: the augmentation as a morphism from the
cellular chain complex of representations to the trivial representation placed in degree `0`. -/
def cellularChainComplexRepAugmentation :
    cellularChainComplexRep C hG R ⟶
      (ChainComplex.single₀ (Rep.{w} R G)).obj (Rep.trivial R G R) :=
  ((cellularChainComplexRep C hG R).toSingle₀Equiv _).symm
    ⟨eqToHom (cellularChainComplexRep_X C hG R 0) ≫ cellularAugmentationRep C hG R, by
      simp⟩

/-- In degree `0` the augmentation is `TauCeti.cellularAugmentationRep`. -/
@[simp]
lemma cellularChainComplexRepAugmentation_f_zero :
    (cellularChainComplexRepAugmentation C hG R).f 0 =
      eqToHom (cellularChainComplexRep_X C hG R 0) ≫ cellularAugmentationRep C hG R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **The augmented cellular chain complex of an acyclic lift is exact**: if `p ⁻¹' C` is path
connected and its singular homology vanishes in positive degrees, the augmentation is a
quasi-isomorphism of complexes of representations. -/
theorem quasiIso_cellularChainComplexRepAugmentation [PathConnectedSpace (p ⁻¹' C)]
    (hC : ∀ n, IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj
      (ModuleCat.of R R)).obj (TopCat.of (p ⁻¹' C)))) :
    QuasiIso (cellularChainComplexRepAugmentation C hG R) := by
  let := cwComplexPreimage C hG.isCoveringMap
  have := hG.isCoveringMap.t2Space
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat R)),
    quasiIso_iff_of_arrow_mk_iso _
      (cellularChainComplexAugmentation (p ⁻¹' C) (ModuleCat.of R R)) ?_]
  · exact quasiIso_cellularChainComplexAugmentation _ _ hC
  · refine Arrow.isoMk' _ _ (cellularChainComplexRepForget₂Iso C hG R)
      ((HomologicalComplex.singleMapHomologicalComplex _ _ 0).app _) ?_
    ext : 1
    simp only [HomologicalComplex.comp_f, cellularChainComplexAugmentation_f_zero,
      Functor.mapHomologicalComplex_map_f, cellularChainComplexRepAugmentation_f_zero,
      cellularChainComplexRepForget₂Iso_hom_f]
    simp [-Rep.forget₂_moduleCat_map, Functor.map_comp, eqToHom_map,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      forget₂_map_cellularAugmentationRep]

/-- The cellular chain groups of the lift are projective representations, being free on one chosen
lift of each cell of `C`. -/
instance projective_cellularChainComplexRep_X (n : ℕ) :
    Projective ((cellularChainComplexRep C hG R).X n) := by
  let := cwComplexPreimage C hG.isCoveringMap
  choose s hs using fun i : cell C n ↦
    exists_cellPreimageEquiv_fst_eq C hG.isCoveringMap hG.surjective i
  rw [cellularChainComplexRep_X]
  exact Projective.of_iso (cellularChainRepIsoFree C hG R s hs).symm inferInstance

/-- **The cellular chains of an acyclic free `G`-CW complex are a projective resolution** of the
trivial representation: if the lift `p ⁻¹' C` is path connected and its singular homology vanishes
in positive degrees, its cellular chain complex of free representations, augmented by
`TauCeti.cellularChainComplexRepAugmentation`, resolves the trivial representation `R`. -/
-- The body is exposed, as for Mathlib's `standardResolution`, so that the complex of the
-- resolution is the cellular chain complex by definition: even stating `cellularResolution_π`
-- needs this, its augmentation having source `cellularChainComplexRep C hG R`.
@[expose]
def cellularResolution [PathConnectedSpace (p ⁻¹' C)]
    (hC : ∀ n, IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj
      (ModuleCat.of R R)).obj (TopCat.of (p ⁻¹' C)))) :
    ProjectiveResolution (Rep.trivial R G R) where
  complex := cellularChainComplexRep C hG R
  π := cellularChainComplexRepAugmentation C hG R
  quasiIso := quasiIso_cellularChainComplexRepAugmentation C hG R hC

variable [PathConnectedSpace (p ⁻¹' C)]
  (hC : ∀ n, IsZero (((singularHomologyFunctor (ModuleCat.{w} R) (n + 1)).obj
    (ModuleCat.of R R)).obj (TopCat.of (p ⁻¹' C))))

/-- The complex of the resolution is the cellular chain complex of the lift. -/
@[simp]
theorem cellularResolution_complex :
    (cellularResolution C hG R hC).complex = cellularChainComplexRep C hG R :=
  (rfl)

/-- The augmentation of the resolution is the augmentation of the cellular chains of the lift. -/
@[simp]
theorem cellularResolution_π :
    (cellularResolution C hG R hC).π = cellularChainComplexRepAugmentation C hG R :=
  (rfl)

end TauCeti
