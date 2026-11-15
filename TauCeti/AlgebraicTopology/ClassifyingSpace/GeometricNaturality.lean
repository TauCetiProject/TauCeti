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
maps, both on underlying module complexes and equivariantly in `Rep k G`
(`MonoidHom.universalGSpaceCellularComplexIso_hom_naturality`). In particular this holds for
noninjective homomorphisms: indices distinguish the vertices within a simplex, so relabelling
preserves dimension and orientation.

Composing this identification with the explicit join-to-bar map gives chain homotopy
equivalences from geometric cellular chains to Mathlib's standard complex, both in `Rep k G`
(`TauCeti.universalGSpaceCellularRepStandardHomotopyEquiv`) and after forgetting the action
(`TauCeti.universalGSpaceCellularStandardHomotopyEquiv`). Their forward maps are strictly natural
in group homomorphisms (`MonoidHom.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality`,
`MonoidHom.universalGSpaceCellularStandardHomotopyEquiv_hom_naturality`), while the homotopy
inverses commute with group homomorphisms up to equivariant chain homotopy
(`MonoidHom.universalGSpaceCellularRepStandardHomotopyEquivInvHomotopy`). For a nontrivial
coefficient ring, the module-level forward comparison is likewise a homotopy equivalence and not an
isomorphism (`TauCeti.not_isIso_universalGSpaceCellularStandardHomotopyEquiv_hom`).

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex AbstractSimplicialComplex TauCeti

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

/-- In each degree, the equivariant scaled cellular-basis isomorphism intertwines the geometric
cellular chain-group map with relabelling of ordered simplices. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_hom_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceCellularGroupMap n ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).hom =
      (universalGSpaceCellularRepIso k G n).hom ≫ φ.universalGSpaceChainHom n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine (cellularChainBasis (univ : Set (universalGSpace G)) k n).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv _ n).symm.surjective i
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Rep.resMap_hom_toLinearMap, universalGSpaceCellularRepIso_hom_toLinearMap, LinearEquiv.coe_coe,
    MulActionHom.toRepRes_hom_toLinearMap]
  rw [universalGSpaceCellularGroupMap_hom_toLinearMap,
    φ.cellularChainGroupMap_universalGSpaceCellularMap_cellularChainBasis c,
    universalGSpaceCellularChainLinearEquiv_cellularChainBasis,
    universalGSpaceCellularChainLinearEquiv_cellularChainBasis]
  simp

/-- Inverse form of `universalGSpaceCellularRepIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularRepIso_inv_naturality (φ : G →* H) (n : ℕ) :
    φ.universalGSpaceChainHom n ≫
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).inv =
      (universalGSpaceCellularRepIso k G n).inv ≫ φ.universalGSpaceCellularGroupMap n := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← φ.universalGSpaceCellularRepIso_hom_naturality,
    Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Equivariant geometric and ordered cellular chains are naturally isomorphic.** Along any group
homomorphism `φ : G →* H`, the equivariant cellular chain map induced by `φ.universalGSpaceMap`
commutes with `universalGSpaceCellularComplexIso` and the relabelling map on ordered simplices. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).hom =
      (universalGSpaceCellularComplexIso k G).hom ≫ φ.universalGSpaceChainMap := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularComplexMap_f,
    Functor.mapHomologicalComplex_map_f, universalGSpaceCellularComplexIso_hom_f,
    universalGSpaceChainMap_f, Category.assoc]
  -- Normalize the exposed ordered-chain target carriers so the cellular `eqToHom` transports
  -- compose and cancel.
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  have hres :
      Rep.resMap φ (eqToHom (universalGSpaceCellularComplex_X k H n).symm) ≫
        Rep.resMap φ (eqToHom (universalGSpaceCellularComplex_X k H n) ≫
          (universalGSpaceCellularRepIso k H n).hom) =
        (Rep.resFunctor φ).map (universalGSpaceCellularRepIso k H n).hom := by
    rw [← (Rep.resFunctor φ).map_comp, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hres]
  exact congrArg (_ ≫ ·) (φ.universalGSpaceCellularRepIso_hom_naturality n)

/-- Inverse form of `universalGSpaceCellularComplexIso_hom_naturality`. -/
@[reassoc]
theorem universalGSpaceCellularComplexIso_inv_naturality (φ : G →* H) :
    φ.universalGSpaceChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularComplexIso k H).inv =
      (universalGSpaceCellularComplexIso k G).inv ≫ φ.universalGSpaceCellularComplexMap := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← φ.universalGSpaceCellularComplexIso_hom_naturality,
    Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

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

/-- For any group `G` and nontrivial coefficient ring `k`, the forward map of the module-level
chain homotopy equivalence `universalGSpaceCellularStandardHomotopyEquiv` is **not** an
isomorphism of chain complexes. -/
theorem not_isIso_universalGSpaceCellularStandardHomotopyEquiv_hom [Nontrivial k] :
    ¬ IsIso (universalGSpaceCellularStandardHomotopyEquiv k G).hom := by
  rw [universalGSpaceCellularStandardHomotopyEquiv_hom, isIso_comp_left_iff]
  exact not_isIso_forget₂_mapHomologicalComplex_map_universalGSpaceChainComplexToStandardComplex k G

end TauCeti

namespace MonoidHom

universe u

attribute [local instance] universalGSpaceVertexOrder

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
  simp only [HomologicalComplex.repResForget₂Iso_def, Iso.app_hom]
  rw [← (Functor.mapHomologicalComplexCompIso
    (F := Rep.resFunctor φ) (G := forget₂ (Rep k G) (ModuleCat k))
    (H := forget₂ (Rep k H) (ModuleCat k)) (Iso.refl _) _).hom.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality, Functor.map_comp_assoc]

/-- **The equivariant geometric cellular-to-bar comparison is strictly natural in the group.**
For any group homomorphism `φ : G →* H` (with no injectivity assumption), the equivariant cellular
chain map induced by `φ.universalGSpaceMap` intertwines
`universalGSpaceCellularRepStandardHomotopyEquiv` with `φ.standardComplexMap` in `Rep k G`. -/
@[reassoc]
theorem universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality (φ : G →* H) :
    φ.universalGSpaceCellularComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularRepStandardHomotopyEquiv k G).hom ≫ φ.standardComplexMap := by
  rw [universalGSpaceCellularRepStandardHomotopyEquiv_hom,
    universalGSpaceCellularRepStandardHomotopyEquiv_hom, CategoryTheory.Functor.map_comp,
    φ.universalGSpaceCellularComplexIso_hom_naturality_assoc,
    φ.universalGSpaceChainComplexToStandardComplex_naturality, Category.assoc]

/-- **The equivariant homotopy inverses from the standard complex to geometric cellular chains
commute with group homomorphisms up to equivariant chain homotopy.** For any group homomorphism
`φ : G →* H` (without assuming that restriction preserves projective objects), the inverse
comparison on `G` followed by `φ.universalGSpaceCellularComplexMap` is chain homotopic in `Rep k G`
to `φ.standardComplexMap` followed by the restricted inverse comparison on `H`. -/
def universalGSpaceCellularRepStandardHomotopyEquivInvHomotopy (φ : G →* H) :
    Homotopy
      ((universalGSpaceCellularRepStandardHomotopyEquiv k G).inv ≫
        φ.universalGSpaceCellularComplexMap)
      (φ.standardComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceCellularRepStandardHomotopyEquiv k H).inv) := by
  let eG := universalGSpaceCellularRepStandardHomotopyEquiv k G
  let eH := (Rep.resFunctor φ).mapHomotopyEquiv
    (universalGSpaceCellularRepStandardHomotopyEquiv k H)
  have hnat : φ.universalGSpaceCellularComplexMap ≫ eH.hom =
      eG.hom ≫ φ.standardComplexMap :=
    φ.universalGSpaceCellularRepStandardHomotopyEquiv_hom_naturality
  exact (eH.homotopyHomInvId.compLeftId
      (eG.inv ≫ φ.universalGSpaceCellularComplexMap)).symm.trans <|
    (Homotopy.ofEq (by simp only [Category.assoc, ← Category.assoc _ eH.hom, hnat])).trans
      (eG.homotopyInvHomId.compRightId (φ.standardComplexMap ≫ eH.inv))

end MonoidHom
