/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.ChainComparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Naturality
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Naturality

/-!
# Geometric naturality of the Milnor join resolution

The identification of cellular chains of Milnor's join with its ordered-chain resolution
intertwines the cellular maps of `MonoidHom.universalGSpaceMap` with the relabelling chain
maps. In particular this holds for noninjective homomorphisms: indices distinguish the
vertices within a simplex, so relabelling preserves dimension and orientation.

Composing this identification with the explicit join-to-bar map gives a natural chain
homotopy equivalence from geometric cellular chains to Mathlib's standard complex.
The cellular basis of a simplex maps to its increasing-index tuple of group labels,
multiplied by the orientation unit `realizationChainScale` in that dimension.

The geometric comparison uses the general naturality theorem
`SimplicialMap.cellularChainComplexRealizationIso_hom_naturality`, rather than a new
calculation on relative homology.

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

section MulOne

variable {G H : Type u} [MulOne G] [MulOne H]

/-- The map of Milnor joins on the universal subsets used by cellular chains. -/
def universalGSpaceCellularMap (φ : G →* H) :
    TopCat.of (univ : Set (universalGSpace G)) ⟶
      TopCat.of (univ : Set (universalGSpace H)) :=
  TopCat.ofHom ⟨fun x ↦ ⟨φ.universalGSpaceMap x.1, mem_univ _⟩,
    (φ.universalGSpaceMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The universal-subset map agrees with the continuous map on underlying points. -/
@[simp]
theorem universalGSpaceCellularMap_apply (φ : G →* H)
    (x : (univ : Set (universalGSpace G))) :
    (φ.universalGSpaceCellularMap x).1 = φ.universalGSpaceMap x.1 := (rfl)

private theorem universalGSpaceSimplicialMap_restrictPreimage (φ : G →* H) :
    TopCat.ofHom ((φ.universalGSpaceSimplicialMap).realizationMap.restrictPreimage univ) =
      φ.universalGSpaceCellularMap := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f : C(universalGSpace G, universalGSpace H) ↦ f x.1)
    φ.universalGSpaceSimplicialMap_realizationMap

/-- The continuous map on Milnor joins preserves the simplicial CW filtrations.
The map is restricted to the universal subsets used by cellular chains. -/
theorem isCellular_universalGSpaceMap (φ : G →* H) :
    IsCellular (univ : Set (universalGSpace G)) (univ : Set (universalGSpace H))
      φ.universalGSpaceCellularMap := by
  convert (φ.universalGSpaceSimplicialMap).isCellular_realizationMap using 1
  exact φ.universalGSpaceSimplicialMap_restrictPreimage.symm

end MulOne

variable {k G H : Type u} [Ring k] [Group G] [Group H]

/-- Cellular chains and ordered join chains are naturally identified under maps of groups.
Forgetting the restricted target action yields the usual underlying module complex. -/
@[reassoc]
theorem universalGSpaceCellularChainComplexIso_naturality (φ : G →* H) :
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceMap (ModuleCat.of k k) ≫
        (universalGSpaceCellularChainComplexIso k H).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.universalGSpaceChainMap ≫
        ((universalGSpaceChainComplex k H).repResForget₂Iso φ).hom := by
  have h := (φ.universalGSpaceSimplicialMap).cellularChainComplexRealizationIso_hom_naturality
    (fun _ c ↦ φ.universalGSpaceMap_strictMonoOn c) k
  have hcell :
      cellularChainComplexMap univ univ φ.isCellular_universalGSpaceMap (ModuleCat.of k k) =
        cellularChainComplexMap univ univ
          (φ.universalGSpaceSimplicialMap).isCellular_realizationMap (ModuleCat.of k k) := by
    congr 1
    exact φ.universalGSpaceSimplicialMap_restrictPreimage.symm
  ext n : 1
  apply (cancel_mono ((universalGSpaceChainComplexForget₂Iso k H).hom.f n)).mp
  simp only [universalGSpaceCellularChainComplexIso_def, Iso.trans_hom, Iso.symm_hom,
    ← HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    universalGSpaceChainMap_f, universalGSpaceChainComplexForget₂Iso_inv_f,
    universalGSpaceChainComplexForget₂Iso_hom_f,
    HomologicalComplex.repResForget₂Iso_hom_f]
  -- Restriction changes only the action. Normalize the underlying module terms before
  -- reassociating compositions in ModuleCat.
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  simp only [Category.assoc]
  have hn := congrArg (fun f ↦ HomologicalComplex.Hom.f f n) h
  rw [← hcell] at hn
  simp only [HomologicalComplex.comp_f] at hn
  rw [hn]
  congr 1
  simp only [orderedSimplicialChainComplexMap_f]
  congr 1
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply ModuleCat.hom_ext
  refine Finsupp.lhom_ext fun c r ↦ ?_
  simp [universalGSpaceChainHom, ← universalGSpaceCellMap_def]

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
  simp [universalGSpaceCellularStandardHomotopyEquiv, HomotopyEquiv.trans,
    HomotopyEquiv.ofIso, Functor.mapHomotopyEquiv]
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
    cellularChainComplexMap univ univ φ.isCellular_universalGSpaceMap (ModuleCat.of k k) ≫
        (universalGSpaceCellularStandardHomotopyEquiv k H).hom =
      (universalGSpaceCellularStandardHomotopyEquiv k G).hom ≫
        ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map
          φ.standardComplexMap ≫
        ((Rep.standardComplex k H).repResForget₂Iso φ).hom := by
  have h := congrArg
    (((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).map)
    (φ.universalGSpaceChainComplexToStandardComplex_naturality (k := k))
  simp only [Functor.map_comp] at h
  simp only [universalGSpaceCellularStandardHomotopyEquiv_hom, Category.assoc,
    universalGSpaceCellularChainComplexIso_naturality_assoc]
  rw [← HomologicalComplex.repResForget₂Iso_hom_naturality]
  have h' := congrArg (fun f ↦ f ≫ ((Rep.standardComplex k H).repResForget₂Iso φ).hom) h
  simp only [Category.assoc] at h'
  exact congrArg (fun f ↦ (universalGSpaceCellularChainComplexIso k G).hom ≫ f) h'

end MonoidHom
