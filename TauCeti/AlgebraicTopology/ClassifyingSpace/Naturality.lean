/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CellMap
public import TauCeti.AlgebraicTopology.ClassifyingSpace.StandardResolution
public import TauCeti.RepresentationTheory.Homological.ChangeOfGroups

/-!
# Naturality of the join-to-standard comparison

A group homomorphism induces an equivariant chain map on the ordered chains of Milnor's
countable join. In every degree it relabels each simplex, preserving its increasing-index
orientation. The cell maps are those of the continuous maps `MonoidHom.universalGSpaceMap`,
as witnessed by `MonoidHom.universalGSpaceMap_characteristicMap`.

`MonoidHom.universalGSpaceChainComplexToStandardComplex_naturality` proves that the explicit
comparison with Mathlib's standard complex commutes with these induced maps, as an equality
of chain maps of representations. Both routes send a simplex to the tuple of images of its
labels. Thus the forward map of `TauCeti.universalGSpaceStandardHomotopyEquiv` is natural
in the group, and its homotopy inverse commutes with the induced chain maps up to homotopy
(`MonoidHom.universalGSpaceStandardHomotopyEquivInvNaturalityHomotopy`). Restriction of the
target action makes the square a square in `Rep k G`, without any injectivity assumption on
the homomorphism.

The join chain maps preserve augmentation
(`MonoidHom.universalGSpaceChainMap_f_zero_comp_augmentation` and
`MonoidHom.universalGSpaceChainMap_comp_augmentation`).

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I and III.
-/

public section

noncomputable section

open CategoryTheory TauCeti

namespace MonoidHom

universe u

attribute [local instance] universalGSpaceVertexOrder

variable {k G H : Type u} [Group G] [Group H]

section Ring

variable [Ring k]

/-- Linear extension of relabelling simplices, equivariant along the group homomorphism. -/
abbrev universalGSpaceChainHom (φ : G →* H) (n : ℕ) :
    Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) ⟶
      Rep.res φ (Rep.ofMulAction k H ((indexedJoin fun _ : ℕ => H).RealizationCell n)) :=
  (φ.universalGSpaceCellMulActionHom n).toRepRes

/-- The chain map on Milnor join chains induced by a group homomorphism. -/
def universalGSpaceChainMap (φ : G →* H) :
    universalGSpaceChainComplex k G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj (universalGSpaceChainComplex k H) where
  f n := φ.universalGSpaceChainHom n
  comm' i j h := by
    subst i
    rw [Functor.mapHomologicalComplex_obj_d, universalGSpaceChainComplex_d,
      universalGSpaceChainComplex_d]
    apply Rep.ofMulAction_hom_ext
    intro c
    -- The restricted boundary carries the chain complex's implicit object arguments.
    -- Evaluate on permutation coordinates so the representation lemmas can match.
    change (universalGSpaceBoundary k H j).hom
        ((φ.universalGSpaceChainHom (j + 1)).hom (MonoidAlgebra.single c 1)) =
      (φ.universalGSpaceChainHom j).hom
        ((universalGSpaceBoundary k G j).hom (MonoidAlgebra.single c 1))
    simp only [Rep.res_obj_ρ, MulActionHom.toRepRes_hom_single,
      universalGSpaceBoundary_hom_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one, map_sum]
    exact Finset.sum_congr rfl fun i _ => congrArg
      (fun c => MonoidAlgebra.single c ((-1 : k) ^ (i : ℕ)))
      (universalGSpaceCellMap_face φ c i).symm

/-- The components of the induced join chain map are the linear extensions of the cell maps. -/
@[simp]
theorem universalGSpaceChainMap_f (φ : G →* H) (n : ℕ) :
    (φ.universalGSpaceChainMap (k := k)).f n = φ.universalGSpaceChainHom n :=
  (rfl)

/-- The identity homomorphism induces the identity map on join chains. -/
@[simp]
theorem universalGSpaceChainMap_id :
    (MonoidHom.id G).universalGSpaceChainMap (k := k) = 𝟙 (universalGSpaceChainComplex k G) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (congrArg (MulActionHom.toRepRes (k := k) (φ := MonoidHom.id G))
    (universalGSpaceCellMulActionHom_id (G := G) n)).trans MulActionHom.toRepRes_id

/-- Join chain maps respect composition, restricting the second map along the first
homomorphism. -/
@[simp]
theorem universalGSpaceChainMap_comp {K : Type u} [Group K] (ψ : H →* K) (φ : G →* H) :
    (ψ.comp φ).universalGSpaceChainMap (k := k) =
      φ.universalGSpaceChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map ψ.universalGSpaceChainMap := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (congrArg (MulActionHom.toRepRes (k := k) (φ := ψ.comp φ))
    (universalGSpaceCellMulActionHom_comp ψ φ n)).trans
    (MulActionHom.toRepRes_comp (ψ.universalGSpaceCellMulActionHom n)
      (φ.universalGSpaceCellMulActionHom n))

/-- In degree `0`, the induced join chain map preserves the coefficient-sum augmentation. -/
@[reassoc]
theorem universalGSpaceChainMap_f_zero_comp_augmentation (φ : G →* H) :
    (φ.universalGSpaceChainMap (k := k)).f 0 ≫
        (Rep.resFunctor φ).map ((universalGSpaceAugmentation k H).f 0) =
      (universalGSpaceAugmentation k G).f 0 := by
  rw [universalGSpaceChainMap_f, universalGSpaceAugmentation_f_zero,
    universalGSpaceAugmentation_f_zero]
  exact (φ.universalGSpaceCellMulActionHom 0).toRepRes_comp_permutationAugmentation

/-- The induced join chain map commutes with the augmentations into the degree-`0` trivial
complexes. -/
@[reassoc]
theorem universalGSpaceChainMap_comp_augmentation (φ : G →* H) :
    φ.universalGSpaceChainMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map (universalGSpaceAugmentation k H) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Rep.resFunctor φ) _ 0).hom.app
          (Rep.trivial k H k) =
      universalGSpaceAugmentation k G := by
  refine HomologicalComplex.to_single_hom_ext ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  -- `singleObjXSelf _ 0 _` is `Iso.refl _`, so the restricted degree-`0` augmentation agrees
  -- definitionally with `(universalGSpaceAugmentation k H).f 0`.
  exact φ.universalGSpaceChainMap_f_zero_comp_augmentation

end Ring

variable [CommRing k]

/-- In degree `0`, the induced join chain map commutes with the projective-resolution
augmentations. -/
@[reassoc]
theorem universalGSpaceChainMap_f_zero_comp_π (φ : G →* H) :
    (φ.universalGSpaceChainMap (k := k)).f 0 ≫
        (Rep.resFunctor φ).map ((universalGSpaceResolution k H).π.f 0) =
      (universalGSpaceResolution k G).π.f 0 :=
  φ.universalGSpaceChainMap_f_zero_comp_augmentation

/-- **The join-to-standard comparison is natural in the group.** Relabelling simplices before
forgetting their indices agrees with first forgetting indices and then relabelling the tuples.
This is an equality of chain maps in `Rep k G`, with target actions restricted along `φ`. -/
@[reassoc]
theorem universalGSpaceChainComplexToStandardComplex_naturality (φ : G →* H) :
    φ.universalGSpaceChainMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceChainComplexToStandardComplex k H) =
      universalGSpaceChainComplexToStandardComplex k G ≫ φ.standardComplexMap := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Rep.ofMulAction_hom_ext
  intro c
  -- Remove the chain complexes' implicit object arguments before evaluating the maps;
  -- hom_comp and resMap_hom_apply cannot rewrite the transported morphisms directly.
  change ((universalGSpaceChainComplexToStandardComplex k H).f n).hom
      ((φ.universalGSpaceChainHom n).hom (MonoidAlgebra.single c 1)) =
    ((φ.standardComplexMap).f n).hom
      (((universalGSpaceChainComplexToStandardComplex k G).f n).hom
        (MonoidAlgebra.single c 1))
  simp only [universalGSpaceChainComplex_X, Rep.res_obj_ρ, MulActionHom.toRepRes_hom_single,
    universalGSpaceChainComplexToStandardComplex_f_hom_single,
    Functor.mapHomologicalComplex_obj_X, standardComplexMap_f]
  exact (congrArg (fun x => MonoidAlgebra.single x (1 : k))
    (universalGSpaceCellLabels_universalGSpaceCellMap φ c)).trans
    (MulActionHom.toRepRes_hom_single (k := k) (φ.standardComplexMulActionHom n)
      (universalGSpaceCellLabels c) 1).symm

/-- The homotopy inverse of `TauCeti.universalGSpaceStandardHomotopyEquiv` commutes with the
induced chain maps on the standard and Milnor join complexes up to chain homotopy. -/
def universalGSpaceStandardHomotopyEquivInvNaturalityHomotopy (φ : G →* H) :
    Homotopy
      ((universalGSpaceStandardHomotopyEquiv k G).inv ≫ φ.universalGSpaceChainMap)
      (φ.standardComplexMap ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (universalGSpaceStandardHomotopyEquiv k H).inv) := by
  apply φ.homotopyOfCompResAugmentationEq (universalGSpaceResolution k H)
  -- Unfold the degree-`0` components of the restricted complexes so the augmentation identities
  -- rewrite directly without carrier-object transports.
  change ((universalGSpaceStandardHomotopyEquiv k G).inv).f 0 ≫
      (φ.universalGSpaceChainMap).f 0 ≫
        (Rep.resFunctor φ).map ((universalGSpaceResolution k H).π.f 0) =
    (φ.standardComplexMap).f 0 ≫
      (Rep.resFunctor φ).map (((universalGSpaceStandardHomotopyEquiv k H).inv).f 0) ≫
        (Rep.resFunctor φ).map ((universalGSpaceResolution k H).π.f 0)
  rw [universalGSpaceStandardHomotopyEquiv_inv, universalGSpaceStandardHomotopyEquiv_inv,
    φ.universalGSpaceChainMap_f_zero_comp_π]
  have hG := (ProjectiveResolution.lift_commutes_zero (𝟙 _)
    (Rep.standardResolution k G) (universalGSpaceResolution k G)).trans (Category.comp_id _)
  have hH := (ProjectiveResolution.lift_commutes_zero (𝟙 _)
    (Rep.standardResolution k H) (universalGSpaceResolution k H)).trans (Category.comp_id _)
  have hr := (congrArg ((φ.standardComplexMap).f 0 ≫ ·)
    ((Rep.resFunctor φ).map_comp _ _)).symm.trans
      (congrArg (fun t ↦ (φ.standardComplexMap).f 0 ≫ (Rep.resFunctor φ).map t) hH)
  have hstd : (φ.standardComplexMap (k := k)).f 0 ≫
      (Rep.resFunctor φ).map ((Rep.standardResolution k H).π.f 0) =
        (Rep.standardResolution k G).π.f 0 := by
    dsimp only [Rep.standardResolution]
    rw [standardComplexMap_f, TauCeti.Rep.standardComplex.εToSingle₀_f_zero,
      TauCeti.Rep.standardComplex.εToSingle₀_f_zero]
    exact ((congrArg (φ.standardComplexHom 0 ≫ ·)
      (congrArg (Rep.resFunctor φ).map (Category.id_comp _))).trans
        (φ.standardComplexHom_comp_ε (k := k))).trans (Category.id_comp _).symm
  exact hG.trans (hr.trans hstd).symm

end MonoidHom
