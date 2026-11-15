/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EquivariantChains
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality
import TauCeti.RepresentationTheory.Rep.Res

/-!
# Geometric naturality of the Milnor join resolution

The identification of cellular chains of Milnor's join with its ordered-chain resolution
intertwines the cellular maps of `MonoidHom.universalGSpaceMap` with the relabelling chain
maps, both on underlying module complexes and equivariantly in `Rep k G` via
`MonoidHom.universalGSpaceCellularComplexMap`. In particular this holds for noninjective
homomorphisms: indices distinguish the vertices within a simplex, so relabelling preserves
dimension and orientation.

Composing this equivariant identification with the explicit join-to-bar map gives the chain
homotopy equivalence `TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv` in `Rep k G`
from geometric cellular chains to Mathlib's standard complex, whose forward map commutes strictly
as a chain map along every group homomorphism
(`MonoidHom.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality`), with target actions
restricted along `φ`. Strict chain-map naturality is established here only for this explicit
forward comparison and is not asserted for the chosen homotopy inverse `.inv` constructed via
`ProjectiveResolution.lift` (though `Rep.resFunctor φ`, being additive, preserves the homotopy
equivalence itself via `Functor.mapHomotopyEquiv`).

The underlying module-level naturality square is the instance of
`SimplicialMap.cellularChainComplexRealizationIso_hom_naturality` for the relabelling
map `MonoidHom.universalGSpaceSimplicialMap`; faithfulness of forgetting the group action lifts
this square to `Rep k G`.

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

variable {k G H : Type u} [Ring k] [Group G] [Group H]

/-- Reading permutation coefficients intertwines relabelling join chains with the induced
map of ordered simplicial chains. -/
@[reassoc]
theorem universalGSpaceChainComplexForget₂Iso_naturality (φ : G →* H) :
    (universalGSpaceChainComplexForget₂Iso k G).hom ≫
        orderedSimplicialChainComplexMap k φ.universalGSpaceSimplicialMap =
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
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
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
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

/-- **Equivariant naturality of the geometric cellular-to-ordered chain comparison.**
For every group homomorphism `φ : G →* H` (including noninjective ones), the equivariant
cellular chain map induced by `φ.universalGSpaceCellularMap` intertwines with the relabelling
ordered-chain map `φ.universalGSpaceChainMap` in `Rep k G`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap := by
  apply ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map_injective
  rw [← cancel_epi (universalGSpaceCellularComplexForget₂Iso k G).hom,
    ← cancel_mono ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom]
  simp only [Functor.map_comp, Category.assoc,
    universalGSpaceCellularComplexForget₂Iso_hom_comp_map_cellularComplexIso_hom_assoc]
  rw [← φ.universalGSpaceCellularChainComplexIso_naturality,
    ← universalGSpaceCellularComplexForget₂Iso_hom_comp_map_cellularComplexIso_hom k H,
    φ.universalGSpaceCellularComplexForget₂Iso_naturality_assoc,
    HomologicalComplex.repResForget₂Iso_hom_naturality]

/-- Inverse form of `universalGSpaceCellularComplexIso_hom_naturality`: the inverse equivariant
ordered-to-cellular chain isomorphism is also natural along every group homomorphism. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_inv_naturality (φ : G →* H) :
    φ.universalGSpaceChainMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).inv =
      (universalGSpaceCellularComplexIso k G).inv ≫ φ.universalGSpaceCellularComplexMap :=
  (CommSq.vert_inv (g := universalGSpaceCellularComplexIso k G)
    (h := ((Rep.resFunctor φ).mapHomologicalComplex _).mapIso
      (universalGSpaceCellularComplexIso k H))
    ⟨φ.universalGSpaceCellularComplexIso_hom_naturality (k := k)⟩).w

/-- Degreewise equivariant naturality of the cellular-to-ordered representation isomorphism. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_hom_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceCellularRepresentationMap (k := k) n ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).hom =
      (universalGSpaceCellularRepIso k G n).hom ≫ φ.universalGSpaceChainHom n := by
  have h := HomologicalComplex.congr_hom
    (φ.universalGSpaceCellularComplexIso_hom_naturality (k := k)) n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    universalGSpaceCellularComplexMap_f, Functor.mapHomologicalComplex_map_f,
    universalGSpaceCellularComplexIso_hom_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceChainMap_f] at h
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X] at h
  rw [Category.assoc, Category.assoc, ← Rep.resMap_comp, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.assoc] at h
  exact (cancel_epi (eqToHom (universalGSpaceCellularComplex_X k G n))).mp h

/-- Inverse form of `universalGSpaceCellularRepIso_hom_naturality` in each degree. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_inv_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceChainHom (k := k) n ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).inv =
      (universalGSpaceCellularRepIso k G n).inv ≫
        φ.universalGSpaceCellularRepresentationMap n :=
  (CommSq.vert_inv (g := universalGSpaceCellularRepIso k G n)
    (h := (Rep.resFunctor φ).mapIso (universalGSpaceCellularRepIso k H n))
    ⟨φ.universalGSpaceCellularRepIso_hom_naturality (k := k) n⟩).w

/-- The equivariant geometric cellular chain map preserves augmentation onto the trivial
representation. -/
@[reassoc]
theorem universalGSpaceCellularComplexMap_comp_augmentation (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          ((universalGSpaceCellularComplexIso k H).hom ≫ universalGSpaceAugmentation k H) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Rep.resFunctor φ) _ 0).hom.app
          (Rep.trivial k H k) =
      (universalGSpaceCellularComplexIso k G).hom ≫ universalGSpaceAugmentation k G := by
  rw [Functor.map_comp, Category.assoc,
    φ.universalGSpaceCellularComplexIso_hom_naturality_assoc]
  exact congrArg ((universalGSpaceCellularComplexIso k G).hom ≫ ·)
    φ.universalGSpaceChainMap_comp_augmentation

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
      (((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).obj
        (Rep.standardComplex k G)) :=
  (HomotopyEquiv.ofIso (universalGSpaceCellularChainComplexIso k G)).trans
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomotopyEquiv
      (universalGSpaceStandardHomotopyEquiv k G))

/-- The geometric-to-bar comparison factors through the ordered-chain comparison. -/
@[simp]
theorem universalGSpaceCellularStandardHomotopyEquiv_hom :
    (universalGSpaceCellularStandardHomotopyEquiv k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceChainComplexToStandardComplex k G) := by
  simp [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv]

/-- The inverse comparison is the abstract projective lift back to ordered join chains,
followed by the inverse cellular-chain identification. -/
@[simp]
theorem universalGSpaceCellularStandardHomotopyEquiv_inv :
    (universalGSpaceCellularStandardHomotopyEquiv k G).inv =
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 _) (Rep.standardResolution k G)
            (universalGSpaceResolution k G)) ≫
        (universalGSpaceCellularChainComplexIso k G).inv := by
  simp only [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv, universalGSpaceStandardHomotopyEquiv_inv]
  -- The two projective lifts carry the definitionally equal augmentation targets of the
  -- join and standard resolutions. Reflexivity identifies these implicit object arguments.
  rfl

/-- Forgetting the translation action intertwines the forward equivariant cellular-to-bar
comparison with the underlying module-level comparison. -/
@[reassoc]
theorem universalGSpaceCellularComplexForget₂Iso_hom_comp_map_repStandardHomotopyEquiv_hom :
    (universalGSpaceCellularComplexForget₂Iso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom =
      (universalGSpaceCellularStandardHomotopyEquiv k G).hom := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv_hom, Functor.map_comp,
    universalGSpaceCellularComplexForget₂Iso_hom_comp_map_cellularComplexIso_hom_assoc,
    universalGSpaceCellularStandardHomotopyEquiv_hom]

/-- Forgetting the translation action intertwines the inverse equivariant bar-to-cellular
comparison with the underlying module-level inverse comparison. -/
@[reassoc]
theorem map_universalGSpaceCellularRepStandardHomotopyEquiv_inv_comp_forget₂Iso_inv :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
        (universalGSpaceCellularRepStandardHomotopyEquiv k G).inv ≫
      (universalGSpaceCellularComplexForget₂Iso k G).inv =
      (universalGSpaceCellularStandardHomotopyEquiv k G).inv := by
  let F := (forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex (ComplexShape.down ℕ)
  have hinv := congrArg Iso.inv
    (universalGSpaceCellularComplexForget₂Iso_trans_mapIso_cellularComplexIso k G)
  simp only [Iso.trans_inv, Functor.mapIso_inv] at hinv
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_inv,
    universalGSpaceCellularStandardHomotopyEquiv_inv]
  exact (F.map_comp_assoc _ _ _).trans (congrArg (F.map _ ≫ ·) hinv)

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
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.standardComplexMap ≫
        ((Rep.standardComplex k H).repResForget₂Iso φ).hom := by
  simp only [universalGSpaceCellularStandardHomotopyEquiv_hom, Category.assoc,
    universalGSpaceCellularChainComplexIso_naturality_assoc]
  rw [← HomologicalComplex.repResForget₂Iso_hom_naturality, ← Functor.map_comp_assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality, Functor.map_comp_assoc]

/-- **Change-of-group naturality of the equivariant geometric cellular-to-bar comparison.**
For every group homomorphism `φ : G →* H` (including noninjective ones), the forward map of
`universalGSpaceCellularRepStandardHomotopyEquiv` intertwines the geometric cellular chain map
induced by `φ.universalGSpaceCellularMap` with `φ.standardComplexMap` as chain maps in
`Rep k G`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv_hom, Functor.map_comp,
    φ.universalGSpaceCellularComplexIso_hom_naturality_assoc, Category.assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality]

/-- The equivariant geometric cellular chain map commutes with the projective-resolution
augmentations `universalGSpaceCellularResolution.π`, up to the canonical complex transports. -/
@[reassoc]
theorem universalGSpaceCellularComplexMap_comp_π (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (eqToHom (universalGSpaceCellularResolution_complex k H).symm ≫
            (universalGSpaceCellularResolution k H).π) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Rep.resFunctor φ) _ 0).hom.app
          (Rep.trivial k H k) =
      eqToHom (universalGSpaceCellularResolution_complex k G).symm ≫
        (universalGSpaceCellularResolution k G).π := by
  simp only [universalGSpaceCellularResolution_π, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  exact φ.universalGSpaceCellularComplexMap_comp_augmentation

end MonoidHom
