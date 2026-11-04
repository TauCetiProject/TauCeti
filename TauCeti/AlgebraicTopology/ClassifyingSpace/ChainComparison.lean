/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Resolution
public import TauCeti.RepresentationTheory.Rep.HomologicalComplex
public import TauCeti.AlgebraicTopology.Cellular.Permutation
public import TauCeti.AlgebraicTopology.Cellular.Augmentation
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedChainComplex

/-!
# Cellular and ordered chains of Milnor's join

The cellular chains of `universalGSpace G`, with its simplicial CW structure, are the
underlying complex of the ordered-chain resolution `universalGSpaceResolution`. The comparison
sends the cellular basis vector of an `n`-simplex to that simplex multiplied by the unit
`realizationChainScale k n`. These dimension-dependent units account for the orientations of
the disks used in the cellular construction.

The comparison intertwines actual translations of the space, acting on relative homology of
successive skeleta, with the permutation action on ordered simplices. Thus the ordered-chain
resolution uses the geometric deck action, not merely an abstract action on an isomorphic
complex of modules. In degree zero it also preserves the cellular augmentation.

The chain isomorphism composes the general simplicial comparison
`cellularChainComplexRealizationIso` with the permutation-coordinate identification
`universalGSpaceChainComplexForget₂Iso`; no cellular incidence calculation is repeated here.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Section I.4.
* A. Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex AbstractSimplicialComplex

namespace TauCeti

universe u

attribute [local instance] universalGSpaceVertexOrder

variable (k : Type u) [Ring k] (G : Type u) [Group G]

/-- Cellular chains in degree `n` of Milnor's join, expressed in permutation coordinates.
A cellular basis vector is multiplied by `realizationChainScale k n`. -/
def universalGSpaceCellularChainLinearEquiv (n : ℕ) :
    (cellularChainGroup (univ : Set (universalGSpace G)) (ModuleCat.of k k) n : ModuleCat k) ≃ₗ[k]
      Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  (cellularChainRealizationLinearEquiv (indexedJoin fun _ : ℕ => G) k n).trans
    (MonoidAlgebra.coeffLinearEquiv k).symm

/-- The comparison sends a cellular basis vector to the corresponding simplex, scaled by the
orientation unit in its dimension. This is not a simp lemma because
`cellularChainBasis_apply` unfolds its left-hand side first. -/
theorem universalGSpaceCellularChainLinearEquiv_cellularChainBasis {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    universalGSpaceCellularChainLinearEquiv k G n
        (cellularChainBasis (univ : Set (universalGSpace G)) k n
          ((realizationCellEquiv _ n).symm c)) =
      MonoidAlgebra.single c (realizationChainScale k n : k) := by
  simp only [universalGSpaceCellularChainLinearEquiv, LinearEquiv.trans_apply,
    cellularChainRealizationLinearEquiv_cellularChainBasis,
    MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.ofCoeff_single]

/-- The inverse comparison sends a simplex with coefficient `r` to `r * sₙ⁻¹` times its
cellular basis vector, where `sₙ = realizationChainScale k n`. -/
@[simp]
theorem universalGSpaceCellularChainLinearEquiv_symm_single {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (r : k) :
    (universalGSpaceCellularChainLinearEquiv k G n).symm (MonoidAlgebra.single c r) =
      (r * ↑(realizationChainScale k n)⁻¹) •
        cellularChainBasis (univ : Set (universalGSpace G)) k n
          ((realizationCellEquiv _ n).symm c) := by
  simp only [universalGSpaceCellularChainLinearEquiv, LinearEquiv.symm_trans_apply]
  rw [LinearEquiv.symm_symm, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single]
  exact cellularChainRealizationLinearEquiv_symm_single c r

/-- The actual cellular chain complex of Milnor's join is the underlying complex of its
ordered-chain resolution. -/
def universalGSpaceCellularChainComplexIso :
    cellularChainComplex (univ : Set (universalGSpace G)) (ModuleCat.of k k) ≅
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _).obj
        (universalGSpaceChainComplex k G) :=
  cellularChainComplexRealizationIso (indexedJoin fun _ : ℕ => G) k ≪≫
    (universalGSpaceChainComplexForget₂Iso k G).symm

/-- In each degree the chain comparison is the scaled cellular-basis comparison, up to the
canonical identification of the cellular chain group. -/
theorem universalGSpaceCellularChainComplexIso_hom_f (n : ℕ) :
    (universalGSpaceCellularChainComplexIso k G).hom.f n =
      eqToHom (cellularChainComplex_X _ _ n) ≫
        (universalGSpaceCellularChainLinearEquiv k G n).toModuleIso.hom := by
  -- The exposed ordered-chain terms are permutation modules, so only the cellular source
  -- needs a transport. Cancel the coefficient comparison before simplifying its components.
  apply (cancel_mono ((universalGSpaceChainComplexForget₂Iso k G).hom.f n)).mp
  simp only [universalGSpaceCellularChainComplexIso, Iso.trans_hom, Iso.symm_hom,
    ← HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [cellularChainComplexRealizationIso_hom_f,
    universalGSpaceChainComplexForget₂Iso_hom_f, universalGSpaceCellularChainLinearEquiv]
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  apply ModuleCat.hom_ext
  ext x
  simp [LinearEquiv.trans_apply]

/-- Evaluating the chain comparison gives the linear comparison after identifying the cellular
chain group. The target is the underlying permutation module of the ordered-chain complex. -/
-- Specify the target of `Hom.hom` to keep the implicit codomain in simp normal form.
@[simp]
theorem universalGSpaceCellularChainComplexIso_hom_f_apply (n : ℕ)
    (x : (cellularChainComplex (univ : Set (universalGSpace G))
      (ModuleCat.of k k)).X n) :
    ModuleCat.Hom.hom (B := ModuleCat.of k
      (MonoidAlgebra k ((indexedJoin fun _ : ℕ => G).RealizationCell n)))
      ((universalGSpaceCellularChainComplexIso k G).hom.f n) x =
      universalGSpaceCellularChainLinearEquiv k G n
        (eqToHom (cellularChainComplex_X univ (ModuleCat.of k k) n) x) := by
  exact ConcreteCategory.congr_hom (universalGSpaceCellularChainComplexIso_hom_f k G n) x

/-- The cellular comparison preserves augmentation: in degree zero both augmentations send
each vertex to `1`. -/
@[reassoc]
theorem universalGSpaceCellularChainLinearEquiv_comp_permutationAugmentation :
    (universalGSpaceCellularChainLinearEquiv k G 0).toModuleIso.hom ≫
        (forget₂ (Rep k G) (ModuleCat k)).map
          (permutationAugmentation k G ((indexedJoin fun _ : ℕ => G).RealizationCell 0)) =
      cellularAugmentation (univ : Set (universalGSpace G)) (ModuleCat.of k k) := by
  apply ModuleCat.hom_ext
  refine (cellularChainBasis (univ : Set (universalGSpace G)) k 0).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv _ 0).symm.surjective i
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  rw [universalGSpaceCellularChainLinearEquiv_cellularChainBasis,
    forget₂_map_permutationAugmentation]
  simp only [cellularChainBasis_apply, ← ConcreteCategory.comp_apply,
    Category.assoc, ι_cellularChainGroupIso_inv_comp_cellularAugmentation]
  simp

/-- In degree zero the chain comparison intertwines the cellular augmentation with the
augmentation of the ordered-chain resolution. -/
@[reassoc]
theorem universalGSpaceCellularChainComplexIso_comp_augmentation :
    (universalGSpaceCellularChainComplexIso k G).hom.f 0 ≫
        (forget₂ (Rep k G) (ModuleCat k)).map ((universalGSpaceAugmentation k G).f 0) =
      eqToHom (cellularChainComplex_X _ _ 0) ≫
        cellularAugmentation (univ : Set (universalGSpace G)) (ModuleCat.of k k) := by
  rw [universalGSpaceAugmentation_f_zero, universalGSpaceCellularChainComplexIso_hom_f]
  -- Normalize the source and target terms before rewriting composition in `ModuleCat`.
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X,
    ChainComplex.single₀_obj_zero]
  rw [Category.assoc, universalGSpaceCellularChainLinearEquiv_comp_permutationAugmentation]

variable {G}

/-- Translation of Milnor's join, restricted to the universal subset used by cellular chains. -/
def universalGSpaceCellularTranslation (g : G) :
    TopCat.of (univ : Set (universalGSpace G)) ⟶ TopCat.of (univ : Set (universalGSpace G)) :=
  TopCat.ofHom ⟨fun x ↦ ⟨g • x.1, mem_univ _⟩,
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

/-- Translation on the universal subset is ordinary translation on the underlying point. -/
@[simp]
theorem universalGSpaceCellularTranslation_apply (g : G)
    (x : (univ : Set (universalGSpace G))) :
    (universalGSpaceCellularTranslation g x).1 = g • x.1 := (rfl)

/-- Translation by the identity is the identity map of the universal subset. -/
@[simp]
theorem universalGSpaceCellularTranslation_one :
    universalGSpaceCellularTranslation (1 : G) = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  -- The concrete hom of `TopCat.ofHom` evaluates its stored continuous map; the subtype
  -- projection and the `TopCat` identity reduce to the underlying point and its translation.
  exact one_smul G x.1

/-- Translation by a product is successive translation on the universal subset. -/
theorem universalGSpaceCellularTranslation_mul (g h : G) :
    universalGSpaceCellularTranslation (g * h) =
      universalGSpaceCellularTranslation h ≫ universalGSpaceCellularTranslation g := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  -- Concrete `TopCat` composition evaluates the two stored continuous maps successively;
  -- projecting the subtype constructors gives the nested translations of the underlying point.
  exact mul_smul g h x.1

/-- Translation preserves the skeletal filtration of the simplicial CW structure. -/
theorem isCellular_universalGSpaceCellularTranslation (g : G) :
    IsCellular univ univ (universalGSpaceCellularTranslation g) := by
  apply isCellular_of_map_eq
  · intro x hx
    exact hx.elim
  · intro n i
    exact ⟨g • i, fun x _ _ ↦ (universalGSpaceCellularTranslation_apply g _).trans
      (smul_map_universalGSpace g i x)⟩

/-- The cellular chain maps induced by translation respect multiplication. -/
theorem cellularChainComplexMap_universalGSpaceCellularTranslation_mul (g h : G) :
    cellularChainComplexMap univ univ (isCellular_universalGSpaceCellularTranslation (g * h))
        (ModuleCat.of k k) =
      cellularChainComplexMap univ univ (isCellular_universalGSpaceCellularTranslation h)
          (ModuleCat.of k k) ≫
        cellularChainComplexMap univ univ (isCellular_universalGSpaceCellularTranslation g)
          (ModuleCat.of k k) := by
  simpa only [universalGSpaceCellularTranslation_mul] using
    (cellularChainComplexMap_comp univ univ (isCellular_universalGSpaceCellularTranslation h)
      univ (isCellular_universalGSpaceCellularTranslation g) (ModuleCat.of k k))

/-- Geometric translation sends a cellular basis vector to the basis vector of the translated
cell, without an orientation sign. -/
theorem cellularChainGroupMap_universalGSpaceCellularTranslation_cellularChainBasis
    (g : G) {n : ℕ} (i : cell (univ : Set (universalGSpace G)) n) :
    cellularChainGroupMap univ univ (isCellular_universalGSpaceCellularTranslation g)
        (ModuleCat.of k k) n (cellularChainBasis univ k n i) =
      cellularChainBasis univ k n (g • i) :=
  cellularChainGroupMap_cellularChainBasis _ _ _ k
    (fun x _ _ ↦ (universalGSpaceCellularTranslation_apply g _).trans
      (smul_map_universalGSpace g i x))

/-- The cellular-to-ordered comparison intertwines the action induced by actual translation on
the space with the permutation representation on simplices. -/
theorem universalGSpaceCellularChainLinearEquiv_translation (g : G) (n : ℕ)
    (x : (cellularChainGroup (univ : Set (universalGSpace G)) (ModuleCat.of k k) n : ModuleCat k)) :
    universalGSpaceCellularChainLinearEquiv k G n
        (cellularChainGroupMap univ univ (isCellular_universalGSpaceCellularTranslation g)
          (ModuleCat.of k k) n x) =
      (Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n)).ρ g
        (universalGSpaceCellularChainLinearEquiv k G n x) := by
  suffices h : (universalGSpaceCellularChainLinearEquiv k G n).toLinearMap ∘ₗ
        (cellularChainGroupMap univ univ (isCellular_universalGSpaceCellularTranslation g)
          (ModuleCat.of k k) n).hom =
      (Rep.ofMulAction k G ((indexedJoin fun _ : ℕ => G).RealizationCell n)).ρ g ∘ₗ
        (universalGSpaceCellularChainLinearEquiv k G n).toLinearMap from
    LinearMap.congr_fun h x
  refine (cellularChainBasis (univ : Set (universalGSpace G)) k n).ext fun i ↦ ?_
  obtain ⟨c, rfl⟩ := (realizationCellEquiv _ n).symm.surjective i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cellularChainGroupMap_universalGSpaceCellularTranslation_cellularChainBasis,
    ← realizationCellEquiv_symm_smul]
  rw [universalGSpaceCellularChainLinearEquiv_cellularChainBasis,
    universalGSpaceCellularChainLinearEquiv_cellularChainBasis]
  simp only [Representation.ofMulAction_single]

/-- The chain comparison intertwines geometric translation with the permutation action on
ordered chains. -/
@[reassoc]
theorem universalGSpaceCellularChainComplexIso_translation (g : G) :
    cellularChainComplexMap univ univ (isCellular_universalGSpaceCellularTranslation g)
        (ModuleCat.of k k) ≫ (universalGSpaceCellularChainComplexIso k G).hom =
      (universalGSpaceCellularChainComplexIso k G).hom ≫
        (universalGSpaceChainComplex k G).repTranslation g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [HomologicalComplex.comp_f, universalGSpaceCellularChainComplexIso_hom_f,
    cellularChainComplexMap_f, HomologicalComplex.repTranslation_f]
  -- Normalize the forgotten permutation-module terms before canceling the cellular transports.
  dsimp only [Functor.mapHomologicalComplex_obj_X, universalGSpaceChainComplex_X]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ModuleCat.hom_comp]
  exact universalGSpaceCellularChainLinearEquiv_translation k g n _

end TauCeti
