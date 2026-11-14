/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EquivariantChains
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups

/-!
# Geometric naturality of the Milnor join resolution

The identification of cellular chains of Milnor's join with its ordered-chain resolution
intertwines the cellular maps of `MonoidHom.universalGSpaceMap` with the relabelling chain
maps. In particular this holds for noninjective homomorphisms: indices distinguish the
vertices within a simplex, so relabelling preserves dimension and orientation.

Because `MonoidHom.universalGSpaceCellularMap` intertwines the translation actions along
`φ : G →* H`, it induces an equivariant cellular chain map
`MonoidHom.universalGSpaceCellularComplexMap` in `Rep k G`, with the target complex
restricted along `φ`. Evaluating on the geometric cellular basis identifies the induced map
in each degree with simplex relabelling (`MonoidHom.universalGSpaceCellularRepIso_hom_naturality`),
lifting the cellular-to-ordered naturality square directly to `Rep k G`
(`MonoidHom.universalGSpaceCellularComplexIso_hom_naturality`), and composing with the
ordered join-to-bar comparison gives equivariant naturality in `Rep k G` of the explicit
geometric cellular-to-bar homotopy equivalence
(`MonoidHom.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality`).

Consequently, the geometric cellular projective resolution
`TauCeti.universalGSpaceCellularResolution` computes change-of-group maps in both group
homology and group cohomology via the geometric cellular chain map of Milnor joins
(`MonoidHom.groupHomologyIso_universalGSpaceCellularResolution_hom_naturality` and
`MonoidHom.groupCohomologyIso_universalGSpaceCellularResolution_inv_naturality`).

The geometric naturality square is the instance of
`SimplicialMap.cellularChainComplexRealizationIso_hom_naturality` for the relabelling
map `MonoidHom.universalGSpaceSimplicialMap`.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology AbstractSimplicialComplex TauCeti

namespace MonoidHom

universe u

attribute [local instance] universalGSpaceVertexOrder

variable {G H : Type u} [Group G] [Group H]

/-- The cellular map on Milnor joins induced by `φ : G →* H` intertwines the translation
actions of `G` and `H`. -/
@[reassoc]
theorem universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap
    (φ : G →* H) (g : G) :
    universalGSpaceCellularTranslation g ≫ φ.universalGSpaceCellularMap =
      φ.universalGSpaceCellularMap ≫ universalGSpaceCellularTranslation (φ g) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    universalGSpaceCellularMap_apply, universalGSpaceCellularTranslation_apply,
    universalGSpaceCellularTranslation_apply, universalGSpaceCellularMap_apply,
    φ.universalGSpaceMap_smul]

variable {k : Type u} [Ring k]

/-- Reading permutation coefficients intertwines relabelling join chains with the induced
map of ordered simplicial chains. -/
@[reassoc]
theorem universalGSpaceChainComplexForget₂Iso_naturality (φ : G →* H) :
    (universalGSpaceChainComplexForget₂Iso k G).hom ≫
        orderedSimplicialChainComplexMap k φ.universalGSpaceSimplicialMap =
      ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.universalGSpaceChainMap ≫
        ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom ≫
        (universalGSpaceChainComplexForget₂Iso k H).hom := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceChainComplexForget₂Iso_hom_f,
    orderedSimplicialChainComplexMap_f, Functor.mapHomologicalComplex_map_f,
    universalGSpaceChainMap_f, HomologicalComplex.repResForget₂Iso_hom_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply ModuleCat.hom_ext
  refine MonoidAlgebra.lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [universalGSpaceChainHom, universalGSpaceCellMap_def,
    OrderedSimplicialChain.map_single_of_strictMonoOn _ c
      (φ.universalGSpaceSimplicialMap_strictMonoOn c)]

/-- Cellular chains and ordered join chains are naturally identified under maps of groups.
Forgetting the restricted target action yields the usual underlying module complex. -/
@[reassoc]
theorem universalGSpaceCellularChainComplexIso_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k) ≫
        (universalGSpaceCellularChainComplexIso k H).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.universalGSpaceChainMap ≫
        ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom := by
  have h := (φ.universalGSpaceSimplicialMap).cellularChainComplexRealizationIso_hom_naturality
    (fun _ c ↦ φ.universalGSpaceSimplicialMap_strictMonoOn c) k
  apply (cancel_mono (universalGSpaceChainComplexForget₂Iso k H).hom).mp
  simp only [universalGSpaceCellularChainComplexIso_def, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← φ.universalGSpaceChainComplexForget₂Iso_naturality]
  have hcell :
      cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k) =
        cellularChainComplexMap univ univ
          (φ.universalGSpaceSimplicialMap).isCellular_realizationMap (ModuleCat.of k k) := by
    congr 1
    exact φ.universalGSpaceSimplicialMap_restrictPreimage.symm
  simpa only [Iso.inv_hom_id_assoc, hcell] using h

/-- The morphism of geometric cellular chain representations of Milnor's join induced by a
group homomorphism `φ : G →* H`. -/
def universalGSpaceCellularRepresentationHom (φ : G →* H) (n : ℕ) :
    _root_.Rep.of (universalGSpaceCellularRepresentation k G n) ⟶
      _root_.Rep.res φ (_root_.Rep.of (universalGSpaceCellularRepresentation k H n)) :=
  cellularActionRepresentationHom univ isCellular_universalGSpaceCellularTranslation
    universalGSpaceCellularTranslation_one universalGSpaceCellularTranslation_mul
    univ isCellular_universalGSpaceCellularTranslation
    universalGSpaceCellularTranslation_one universalGSpaceCellularTranslation_mul
    φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap k n

/-- Forgetting equivariance recovers the geometric cellular chain-group map of Milnor joins. -/
@[simp]
theorem universalGSpaceCellularRepresentationHom_hom_toLinearMap (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularRepresentationHom (k := k) n).hom.toLinearMap =
      (cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) n).hom :=
  cellularActionRepresentationHom_hom_toLinearMap _ _ _ _ _ _ _ _ _ _ _ _ _

/-- On geometric cellular basis vectors, `universalGSpaceCellularRepresentationHom` sends the
cell of an `n`-simplex to the cell of its relabelled `n`-simplex, even when `φ` is not
injective. -/
theorem universalGSpaceCellularRepresentationHom_hom_cellularChainBasis (φ : G →* H) {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (φ.universalGSpaceCellularRepresentationHom (k := k) n).hom
        (cellularChainBasis (univ : Set (universalGSpace G)) k n
          ((realizationCellEquiv _ n).symm c)) =
      cellularChainBasis (univ : Set (universalGSpace H)) k n
        ((realizationCellEquiv _ n).symm (φ.universalGSpaceCellMap c)) := by
  have hcell :
      cellularChainGroupMap univ univ φ.isCellular_universalGSpaceCellularMap
          (ModuleCat.of k k) n =
        cellularChainGroupMap univ univ
          (φ.universalGSpaceSimplicialMap).isCellular_realizationMap (ModuleCat.of k k) n := by
    refine congrFun ?_ n
    congr 1
    exact φ.universalGSpaceSimplicialMap_restrictPreimage.symm
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    universalGSpaceCellularRepresentationHom_hom_toLinearMap, hcell]
  simpa only [universalGSpaceCellMap_def] using
    cellularChainGroupMap_realization_cellularChainBasis k φ.universalGSpaceSimplicialMap c
      (φ.universalGSpaceSimplicialMap_strictMonoOn c)

/-- The identity homomorphism induces the identity morphism on geometric cellular chain
representations. -/
@[simp]
theorem universalGSpaceCellularRepresentationHom_id (n : ℕ) :
    (MonoidHom.id G).universalGSpaceCellularRepresentationHom (k := k) n =
      𝟙 (_root_.Rep.of (universalGSpaceCellularRepresentation k G n)) :=
  cellularActionRepresentationHom_eq_id _ _ _ _ _ _ _ universalGSpaceCellularMap_id n

/-- Geometric cellular chain-representation maps respect composition of group homomorphisms,
restricting the second map along the first homomorphism. -/
@[simp]
theorem universalGSpaceCellularRepresentationHom_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) (n : ℕ) :
    (ψ.comp φ).universalGSpaceCellularRepresentationHom (k := k) n =
      φ.universalGSpaceCellularRepresentationHom n ≫
        (_root_.Rep.resFunctor φ).map (ψ.universalGSpaceCellularRepresentationHom n) :=
  cellularActionRepresentationHom_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (universalGSpaceCellularMap_comp ψ φ) n

/-- The equivariant chain map on geometric cellular chains of Milnor's join induced by a group
homomorphism `φ : G →* H`. -/
def universalGSpaceCellularComplexMap (φ : G →* H) :
    universalGSpaceCellularComplex k G ⟶
      ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).obj
        (universalGSpaceCellularComplex k H) :=
  cellularActionComplexMap univ isCellular_universalGSpaceCellularTranslation
    universalGSpaceCellularTranslation_one universalGSpaceCellularTranslation_mul
    univ isCellular_universalGSpaceCellularTranslation
    universalGSpaceCellularTranslation_one universalGSpaceCellularTranslation_mul
    φ φ.isCellular_universalGSpaceCellularMap
    φ.universalGSpaceCellularTranslation_comp_universalGSpaceCellularMap k

/-- In each degree, `universalGSpaceCellularComplexMap` is
`universalGSpaceCellularRepresentationHom` up to the canonical term transports. -/
@[simp]
theorem universalGSpaceCellularComplexMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularComplexMap (k := k)).f n =
      eqToHom (universalGSpaceCellularComplex_X k G n) ≫
        φ.universalGSpaceCellularRepresentationHom n ≫
        eqToHom (by
          rw [Functor.mapHomologicalComplex_obj_X, universalGSpaceCellularComplex_X]) :=
  cellularActionComplexMap_f _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The identity homomorphism induces the identity chain map on the equivariant geometric
cellular complex. -/
@[simp]
theorem universalGSpaceCellularComplexMap_id :
    (MonoidHom.id G).universalGSpaceCellularComplexMap (k := k) =
      𝟙 (universalGSpaceCellularComplex k G) :=
  cellularActionComplexMap_eq_id _ _ _ _ _ _ _ universalGSpaceCellularMap_id

/-- Equivariant geometric cellular chain maps respect composition of group homomorphisms,
restricting the second map along the first homomorphism. -/
@[simp]
theorem universalGSpaceCellularComplexMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularComplexMap (k := k) =
      φ.universalGSpaceCellularComplexMap ≫
        ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularComplexMap :=
  cellularActionComplexMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (universalGSpaceCellularMap_comp ψ φ)

/-- Forgetting the group actions intertwines `universalGSpaceCellularComplexMap` with the
module-level geometric cellular chain map. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_hom_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap
        (ModuleCat.of k k) ≫
      (universalGSpaceCellularComplexForget₂Iso k H).hom =
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
      ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        φ.universalGSpaceCellularComplexMap ≫
      ((universalGSpaceCellularComplex k H).repResForget₂Iso φ).hom :=
  cellularActionComplexForget₂Iso_hom_naturality _ _ _ _ _ _ _ _ _ _ _ _

/-- In degree zero, `universalGSpaceCellularComplexMap` commutes with the equivariant cellular
augmentations. -/
@[reassoc]
theorem universalGSpaceCellularComplexMap_f_zero_comp_augmentation (φ : G →* H) :
    (φ.universalGSpaceCellularComplexMap (k := k)).f 0 ≫
        (_root_.Rep.resFunctor φ).map ((universalGSpaceCellularAugmentation k H).f 0) =
      (universalGSpaceCellularAugmentation k G).f 0 :=
  cellularActionComplexMap_f_zero_comp_augmentation _ _ _ _ _ _ _ _ _ _ _ _

/-- In each degree, the equivariant cellular-to-ordered isomorphism
`universalGSpaceCellularRepIso` intertwines `universalGSpaceCellularRepresentationHom` with
simplex relabelling. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_hom_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceCellularRepresentationHom (k := k) n ≫
        (_root_.Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).hom =
      (universalGSpaceCellularRepIso k G n).hom ≫ φ.universalGSpaceChainHom n := by
  refine _root_.Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    (cellularChainBasis (univ : Set (universalGSpace G)) k n).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv _ n).symm.surjective i
  simp only [_root_.Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, _root_.Rep.resMap_hom_toLinearMap,
    universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.coe_coe]
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    φ.universalGSpaceCellularRepresentationHom_hom_cellularChainBasis,
    Representation.IntertwiningMap.toLinearMap_apply]
  erw [universalGSpaceCellularChainLinearEquiv_cellularChainBasis,
    universalGSpaceCellularChainLinearEquiv_cellularChainBasis]
  exact (MulActionHom.toRepRes_hom_single (k := k) (φ.universalGSpaceCellMulActionHom n) c
    (realizationChainScale k n : k)).symm

/-- Inverse form of `universalGSpaceCellularRepIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_inv_naturality (φ : G →* H) (n : ℕ) :
    (universalGSpaceCellularRepIso k G n).inv ≫
        φ.universalGSpaceCellularRepresentationHom (k := k) n =
      φ.universalGSpaceChainHom n ≫
        (_root_.Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← φ.universalGSpaceCellularRepIso_hom_naturality n, Category.assoc,
    ← (_root_.Rep.resFunctor φ).map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Equivariant naturality of the cellular-to-ordered isomorphism.** The identification of
geometric cellular chains of Milnor's join with its ordered-chain complex commutes in `Rep k G`
with the chain maps induced by any group homomorphism `φ : G →* H`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap (k := k) ≫
        ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexMap_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  rw [universalGSpaceCellularComplexIso_hom_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceChainMap_f]
  change _ ≫ (_root_.Rep.resFunctor φ).map
      (eqToHom (universalGSpaceCellularComplex_X k H n) ≫
        (universalGSpaceCellularRepIso k H n).hom) = _
  rw [(_root_.Rep.resFunctor φ).map_comp, eqToHom_map]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg (eqToHom _ ≫ ·) (φ.universalGSpaceCellularRepIso_hom_naturality n)

/-- Inverse form of `universalGSpaceCellularComplexIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_inv_naturality (φ : G →* H) :
    (universalGSpaceCellularComplexIso k G).inv ≫ φ.universalGSpaceCellularComplexMap =
      φ.universalGSpaceChainMap ≫
        ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← φ.universalGSpaceCellularComplexIso_hom_naturality, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end MonoidHom

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

/-- Geometric cellular chains of Milnor's join are chain homotopy equivalent to the
underlying standard complex. The forward map is the cellular-to-ordered identification
followed by the explicit map that forgets the vertex indices. -/
def universalGSpaceCellularStandardHomotopyEquiv :
    HomotopyEquiv
      (cellularChainComplex (univ : Set (universalGSpace G)) (ModuleCat.of k k))
      (((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).obj
        (_root_.Rep.standardComplex k G)) :=
  (HomotopyEquiv.ofIso (universalGSpaceCellularChainComplexIso k G)).trans
    ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomotopyEquiv
      (universalGSpaceStandardHomotopyEquiv k G))

/-- The geometric-to-bar comparison factors through the ordered-chain comparison. -/
@[simp]
theorem universalGSpaceCellularStandardHomotopyEquiv_hom :
    (universalGSpaceCellularStandardHomotopyEquiv k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceChainComplexToStandardComplex k G) := by
  simp [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv]

/-- The inverse comparison is the abstract projective lift back to ordered join chains,
followed by the inverse cellular-chain identification. -/
@[simp]
theorem universalGSpaceCellularStandardHomotopyEquiv_inv :
    (universalGSpaceCellularStandardHomotopyEquiv k G).inv =
      ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 _) (_root_.Rep.standardResolution k G)
            (universalGSpaceResolution k G)) ≫
        (universalGSpaceCellularChainComplexIso k G).inv := by
  simp only [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv, universalGSpaceStandardHomotopyEquiv_inv]
  -- The two projective lifts carry the definitionally equal augmentation targets of the
  -- join and standard resolutions. Reflexivity identifies these implicit object arguments.
  rfl

end TauCeti

namespace MonoidHom

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The explicit geometric cellular-to-bar comparison is natural for every group
homomorphism, with the cellular map induced by its actual continuous map on Milnor joins. -/
@[reassoc]
theorem universalGSpaceCellularStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceCellularMap (ModuleCat.of k k) ≫
        (universalGSpaceCellularStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularStandardHomotopyEquiv k G).hom ≫
        ((forget₂ (_root_.Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.standardComplexMap ≫
        ((_root_.Rep.standardComplex k H).repResForget₂Iso φ).hom := by
  simp only [universalGSpaceCellularStandardHomotopyEquiv_hom, Category.assoc,
    universalGSpaceCellularChainComplexIso_naturality_assoc]
  simp only [HomologicalComplex.repResForget₂Iso_def, Iso.app_hom]
  rw [← (Functor.mapHomologicalComplexCompIso
    (F := _root_.Rep.resFunctor φ) (G := forget₂ (_root_.Rep k G) (ModuleCat k))
    (H := forget₂ (_root_.Rep k H) (ModuleCat k)) (Iso.refl _) _).hom.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality, Functor.map_comp_assoc]

/-- **Equivariant naturality of the geometric cellular-to-bar comparison.** For every group
homomorphism `φ : G →* H`, the explicit comparison from the equivariant geometric cellular
chains of Milnor's join to Mathlib's standard resolution commutes in `Rep k G` with the chain
maps induced by `φ`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap (k := k) ≫
        ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv_hom, Functor.map_comp,
    universalGSpaceCellularComplexIso_hom_naturality_assoc, Category.assoc,
    universalGSpaceChainComplexToStandardComplex_naturality]

/-- The equivariant geometric cellular chain map induced by `φ : G →* H`, typed between the
complexes of `universalGSpaceCellularResolution`. -/
def universalGSpaceCellularResolutionMap (φ : G →* H) :
    (universalGSpaceCellularResolution k G).complex ⟶
      ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).obj
        (universalGSpaceCellularResolution k H).complex :=
  eqToHom (universalGSpaceCellularResolution_complex k G) ≫
    φ.universalGSpaceCellularComplexMap ≫
    ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
      (eqToHom (universalGSpaceCellularResolution_complex k H).symm)

/-- Definition of `universalGSpaceCellularResolutionMap` in terms of
`universalGSpaceCellularComplexMap`. -/
theorem universalGSpaceCellularResolutionMap_def (φ : G →* H) :
    φ.universalGSpaceCellularResolutionMap (k := k) =
      eqToHom (universalGSpaceCellularResolution_complex k G) ≫
        φ.universalGSpaceCellularComplexMap ≫
        ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
          (eqToHom (universalGSpaceCellularResolution_complex k H).symm) :=
  (rfl)

/-- In each degree, `universalGSpaceCellularResolutionMap` is
`universalGSpaceCellularRepresentationHom` up to the canonical term transports. -/
@[simp]
theorem universalGSpaceCellularResolutionMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceCellularResolutionMap (k := k)).f n =
      eqToHom (by
          rw [universalGSpaceCellularResolution_complex, universalGSpaceCellularComplex_X]) ≫
        φ.universalGSpaceCellularRepresentationHom n ≫
        eqToHom (by
          rw [Functor.mapHomologicalComplex_obj_X,
            universalGSpaceCellularResolution_complex, universalGSpaceCellularComplex_X]) := by
  rw [universalGSpaceCellularResolutionMap_def, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.eqToHom_f, HomologicalComplex.eqToHom_f,
    eqToHom_map, universalGSpaceCellularComplexMap_f]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  simp [Category.assoc]

/-- The identity homomorphism induces the identity chain map on the cellular resolution
complex. -/
@[simp]
theorem universalGSpaceCellularResolutionMap_id :
    (MonoidHom.id G).universalGSpaceCellularResolutionMap (k := k) =
      𝟙 (universalGSpaceCellularResolution k G).complex := by
  ext n : 1
  simp

/-- Composition of group homomorphisms induces composition of cellular resolution chain maps,
restricting the second map along the first homomorphism. -/
@[reassoc]
theorem universalGSpaceCellularResolutionMap_comp {K : Type u} [Group K]
    (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceCellularResolutionMap (k := k) =
      φ.universalGSpaceCellularResolutionMap ≫
        ((_root_.Rep.resFunctor φ).mapHomologicalComplex _).map
          ψ.universalGSpaceCellularResolutionMap := by
  ext n : 1
  rw [universalGSpaceCellularResolutionMap_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularResolutionMap_f,
    universalGSpaceCellularResolutionMap_f, (_root_.Rep.resFunctor φ).map_comp,
    (_root_.Rep.resFunctor φ).map_comp, eqToHom_map, eqToHom_map,
    universalGSpaceCellularRepresentationHom_comp]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  simp [Category.assoc]

/-- In degree zero, `universalGSpaceCellularResolutionMap` commutes with the augmentations of
`universalGSpaceCellularResolution`. -/
@[reassoc]
theorem universalGSpaceCellularResolutionMap_f_zero_comp_π (φ : G →* H) :
    (φ.universalGSpaceCellularResolutionMap (k := k)).f 0 ≫
        (_root_.Rep.resFunctor φ).map ((universalGSpaceCellularResolution k H).π.f 0) =
      (universalGSpaceCellularResolution k G).π.f 0 := by
  have hπG : (universalGSpaceCellularResolution k G).π.f 0 =
      (eqToHom (universalGSpaceCellularResolution_complex k G)).f 0 ≫
        (universalGSpaceCellularAugmentation k G).f 0 := by
    rw [universalGSpaceCellularResolution_π,
      universalGSpaceCellularComplexIso_hom_comp_universalGSpaceAugmentation,
      HomologicalComplex.comp_f]
  have hπH : (universalGSpaceCellularResolution k H).π.f 0 =
      (eqToHom (universalGSpaceCellularResolution_complex k H)).f 0 ≫
        (universalGSpaceCellularAugmentation k H).f 0 := by
    rw [universalGSpaceCellularResolution_π,
      universalGSpaceCellularComplexIso_hom_comp_universalGSpaceAugmentation,
      HomologicalComplex.comp_f]
  rw [universalGSpaceCellularResolutionMap_def, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hπH,
    Category.assoc, Category.assoc, ← (_root_.Rep.resFunctor φ).map_comp,
    ← Category.assoc ((eqToHom (universalGSpaceCellularResolution_complex k H).symm).f 0),
    ← HomologicalComplex.comp_f, eqToHom_trans, eqToHom_refl, HomologicalComplex.id_f,
    Category.id_comp, φ.universalGSpaceCellularComplexMap_f_zero_comp_augmentation]
  exact hπG.symm

/-- **Change of groups for group homology via Milnor's geometric cellular resolution.** For a
group homomorphism `φ : G →* H` and a compatible coefficient map `ξ : A ⟶ Res(φ)(B)`, the
identifications `groupHomologyIso` for `universalGSpaceCellularResolution` intertwine
`groupHomology.map φ ξ n` with the map induced on tensor coinvariants by the geometric cellular
map of Milnor joins. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellularResolution_hom_naturality
    {A : _root_.Rep.{u} k G} {B : _root_.Rep.{u} k H}
    (φ : G →* H) (ξ : A ⟶ _root_.Rep.res φ B) (n : ℕ) :
    groupHomology.map φ ξ n ≫
        (groupHomologyIso B n (universalGSpaceCellularResolution k H)).hom =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).hom ≫
        HomologicalComplex.homologyMap
          (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularResolutionMap) n :=
  φ.groupHomologyIso_hom_naturality ξ
    (universalGSpaceCellularResolution k G) (universalGSpaceCellularResolution k H)
    φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- Inverse form of `groupHomologyIso_universalGSpaceCellularResolution_hom_naturality`. -/
@[reassoc]
theorem groupHomologyIso_universalGSpaceCellularResolution_inv_naturality
    {A : _root_.Rep.{u} k G} {B : _root_.Rep.{u} k H}
    (φ : G →* H) (ξ : A ⟶ _root_.Rep.res φ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.coinvariantsTensorChainMap ξ φ.universalGSpaceCellularResolutionMap) n ≫
        (groupHomologyIso B n (universalGSpaceCellularResolution k H)).inv =
      (groupHomologyIso A n (universalGSpaceCellularResolution k G)).inv ≫
        groupHomology.map φ ξ n :=
  φ.groupHomologyIso_inv_naturality ξ
    (universalGSpaceCellularResolution k G) (universalGSpaceCellularResolution k H)
    φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- **Change of groups for group cohomology via Milnor's geometric cellular resolution**,
inverse form: for `φ : G →* H` and a compatible coefficient map `ξ : Res(φ)(A) ⟶ B`, the
identifications `groupCohomologyIso` for `universalGSpaceCellularResolution` carry the cochain
map induced by the geometric cellular map of Milnor joins to `groupCohomology.map φ ξ n`. -/
@[reassoc]
theorem groupCohomologyIso_universalGSpaceCellularResolution_inv_naturality
    {A : _root_.Rep.{u} k H} {B : _root_.Rep.{u} k G}
    (φ : G →* H) (ξ : _root_.Rep.res φ A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularResolutionMap) n ≫
        (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).inv =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).inv ≫
        groupCohomology.map φ ξ n :=
  φ.groupCohomologyIso_inv_naturality ξ
    (universalGSpaceCellularResolution k G) (universalGSpaceCellularResolution k H)
    φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

/-- Forward form of `groupCohomologyIso_universalGSpaceCellularResolution_inv_naturality`. -/
@[reassoc]
theorem groupCohomologyIso_universalGSpaceCellularResolution_hom_naturality
    {A : _root_.Rep.{u} k H} {B : _root_.Rep.{u} k G}
    (φ : G →* H) (ξ : _root_.Rep.res φ A ⟶ B) (n : ℕ) :
    groupCohomology.map φ ξ n ≫
        (groupCohomologyIso B n (universalGSpaceCellularResolution k G)).hom =
      (groupCohomologyIso A n (universalGSpaceCellularResolution k H)).hom ≫
        HomologicalComplex.homologyMap
          (φ.linearYonedaObjMap ξ φ.universalGSpaceCellularResolutionMap) n :=
  φ.groupCohomologyIso_hom_naturality ξ
    (universalGSpaceCellularResolution k G) (universalGSpaceCellularResolution k H)
    φ.universalGSpaceCellularResolutionMap
    φ.universalGSpaceCellularResolutionMap_f_zero_comp_π n

end MonoidHom
