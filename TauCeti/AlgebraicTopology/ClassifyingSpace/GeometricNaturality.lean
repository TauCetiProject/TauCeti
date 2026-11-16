/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EquivariantChains
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality

/-!
# Geometric naturality of the Milnor join resolution

The identification of cellular chains of Milnor's join with its ordered-chain resolution
intertwines the cellular maps of `MonoidHom.universalGSpaceMap` with the relabelling chain
maps, both on underlying module complexes (`universalGSpaceCellularChainComplexIso_naturality`)
and as chain maps of representations (`universalGSpaceCellularComplexIso_naturality`).
In particular this holds for noninjective homomorphisms: indices distinguish the
vertices within a simplex, so relabelling preserves dimension and orientation.

Composing this identification with the explicit join-to-standard and join-to-bar maps gives
equivariant chain homotopy equivalences from geometric cellular chains to Mathlib's homogeneous
standard complex and inhomogeneous bar complex whose forward maps are natural in group
homomorphisms (`universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality` and
`universalGSpaceCellularBarHomotopyEquiv_hom_naturality`).

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

/-- **Equivariant naturality of the cellular-to-ordered join comparison.** As chain maps in
`Rep k G`, the equivariant cellular chain map induced by `MonoidHom.universalGSpaceMap` intertwines
`universalGSpaceCellularComplexIso` with the ordered-chain relabelling map
`MonoidHom.universalGSpaceChainMap`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap := by
  apply ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map_injective
  apply (cancel_epi (universalGSpaceCellularComplexForget₂Iso k G).hom).mp
  apply (cancel_mono ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [HomologicalComplex.repResForget₂Iso_hom_naturality,
    ← φ.universalGSpaceCellularComplexForget₂Iso_naturality_assoc,
    universalGSpaceCellularComplexForget₂Iso_comp_map_universalGSpaceCellularComplexIso,
    universalGSpaceCellularComplexForget₂Iso_comp_map_universalGSpaceCellularComplexIso_assoc,
    ← φ.universalGSpaceCellularChainComplexIso_naturality]

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

/-- The geometric-to-standard comparison factors through the ordered-chain comparison. -/
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

end TauCeti

namespace MonoidHom

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The explicit geometric cellular-to-standard comparison is natural for every group
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

/-- **Equivariant naturality of the geometric cellular-to-standard comparison.** As chain maps in
`Rep k G`, the cellular chain map induced by `MonoidHom.universalGSpaceMap` intertwines
`universalGSpaceCellularRepStandardHomotopyEquiv` with `MonoidHom.standardComplexMap`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap := by
  simp only [universalGSpaceCellularRepStandardHomotopyEquiv_hom, Functor.map_comp,
    universalGSpaceCellularComplexIso_naturality_assoc,
    universalGSpaceChainComplexToStandardComplex_naturality, Category.assoc]

/-- **Equivariant naturality of the geometric cellular-to-bar comparison.** As chain maps in
`Rep k G`, the cellular chain map induced by `MonoidHom.universalGSpaceMap` intertwines
`universalGSpaceCellularBarHomotopyEquiv` with the bar relabelling map
`TauCeti.Rep.barComplex.resChainMap`. -/
@[reassoc]
theorem universalGSpaceCellularBarHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularBarHomotopyEquiv k H).hom =
      (universalGSpaceCellularBarHomotopyEquiv k G).hom ≫
        TauCeti.Rep.barComplex.resChainMap φ := by
  rw [universalGSpaceCellularBarHomotopyEquiv_hom,
    universalGSpaceCellularBarHomotopyEquiv_hom, Functor.map_comp,
    universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality_assoc,
    φ.barComplex_isoStandardComplex_inv_naturality, Category.assoc]

end MonoidHom
