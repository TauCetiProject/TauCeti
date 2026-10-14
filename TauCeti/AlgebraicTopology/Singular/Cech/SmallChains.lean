/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.CechNerve
public import TauCeti.AlgebraicTopology.Singular.Cech.DoubleComplex
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains

/-!
# The rows of the Čech--singular bicomplex resolve small chains

Let `U` be a family of open subsets of `X`. A singular simplex of a term of the Čech nerve of `U`
projects to a singular simplex of `X` lying in one member of `U`, because a standard simplex is
connected. So the singular simplicial sets of the Čech nerve are augmented over the subcomplex of
small singular simplices, not merely over the singular simplicial set of `X`.

Fix a singular degree `q`. Over a small `q`-simplex `σ`, the `q`-simplices of the Čech nerve form
the Čech nerve of the nonempty set of members of `U` containing the image of `σ`. Choosing one of
them gives an extra degeneracy. Applying chains with coefficients in `R`, the `q`-th row of the
Čech--singular bicomplex is chain homotopy equivalent to the small singular `q`-chains, through the
augmentation. The augmentation onto small chains refines the augmentation of the bicomplex onto
all singular chains. These rows are the input for comparing the total complex with singular chains
via the small-chain theorem.

No covering hypothesis is needed: the small simplices are those subordinate to the family, whether
or not it covers `X`.

## Main definitions and results

* `TauCeti.TopCat.openCoverSmallAugmentedSingularNerve`: the singular simplicial sets of the Čech
  nerve, augmented over the small singular simplices.
* `TauCeti.TopCat.openCoverSmallAugmentedSingularNerveExtraDegeneracy`: its extra degeneracy in each
  simplicial degree.
* `TauCeti.TopCat.openCoverSmallSingularAugmentation`: the augmentation of the Čech--singular
  bicomplex onto the small singular chains, refining `TauCeti.TopCat.openCoverSingularAugmentation`
  (`TauCeti.TopCat.openCoverSmallSingularAugmentation_comp_single₀_map`).
* `TauCeti.TopCat.openCoverSmallSingularAugmentationRowHomotopyEquiv`: in each singular degree, the
  row of the augmentation is a chain homotopy equivalence.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982: §8 for the exactness of the rows of the Čech--de Rham complex, and §15 for
  the Čech--singular double complex of an open cover.
-/
public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TopologicalSpace Opposite Convexity
open scoped Simplicial

universe v u

namespace TauCeti.TopCat

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The singular simplices of the Čech nerve of a family of open sets, augmented over the singular
simplices which are small for the family. Every simplex of the Čech nerve projects to a small
simplex, because a standard simplex is connected. -/
@[expose] def openCoverSmallAugmentedSingularNerve : SimplicialObject.Augmented SSet.{u} where
  left := ((SimplicialObject.whiskering _ _).obj TopCat.toSSet).obj (openCoverArrow U).cechNerve
  right := X.smallSingularSubcomplex (fun i ↦ (U i : Set X))
  hom :=
    { app n := SSet.Subcomplex.lift
        (TopCat.toSSet.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ openCoverMap U))) (by
          rintro m _ ⟨σ, rfl⟩
          refine (TopCat.mem_smallSingularSubcomplex_iff _ _ _).2 ?_
          rw [toSSetObjEquiv_toSSet_map_app, ← exists_openCoverMap_comp_eq_iff]
          refine ⟨(WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ openCoverMap U) 0).hom.comp
            (TopCat.toSSetObjEquiv _ _ σ), ?_⟩
          rw [← ContinuousMap.comp_assoc, ← TopCat.hom_comp]
          simp)
      naturality n m θ := by
        rw [← cancel_mono (X.smallSingularSubcomplex _).ι]
        simp [← Functor.map_comp] }

/-- The augmentation of the small augmented singular nerve, followed by the inclusion of the small
simplices, is the map induced by the projection of the Čech nerve onto the ambient space. -/
-- No `reassoc` form: the augmentation's target `.right` matches the source of `ι` only after
-- unfolding `openCoverSmallAugmentedSingularNerve`, so `Category.assoc` cannot fire and the
-- generated `_assoc` lemma would be this one composed on the right, not in simp normal form.
@[simp]
theorem openCoverSmallAugmentedSingularNerve_hom_app_ι (n : SimplexCategoryᵒᵖ) :
    (openCoverSmallAugmentedSingularNerve U).hom.app n ≫
        (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι =
      TopCat.toSSet.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ openCoverMap U)) := by
  simp [openCoverSmallAugmentedSingularNerve]

/-- A singular simplex is small for a family of open subsets exactly when, as a map out of the
topological simplex, it lifts along the map from the disjoint union of the family. -/
theorem mem_smallSingularSubcomplex_iff_exists_comp_openCoverMap {q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋q⦌)) :
    σ ∈ (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).obj (op ⦋q⦌) ↔
      ∃ l : SimplexCategory.toTop.obj ⦋q⦌ ⟶ TopCat.of (Σ i, U i),
        l ≫ openCoverMap U = Equiv.ulift σ := by
  -- `TopCat.toSSetObjEquiv` is the composite of `Equiv.ulift` with precomposition by `ULift.up`.
  have h : Set.range (X.toSSetObjEquiv _ σ) =
      Set.range (ConcreteCategory.hom (Equiv.ulift σ : SimplexCategory.toTop.obj ⦋q⦌ ⟶ X)) :=
    ULift.up_surjective.range_comp _
  rw [TopCat.mem_smallSingularSubcomplex_iff, h, ← exists_openCoverMap_comp_eq_iff]
  exact ⟨fun ⟨l, hl⟩ ↦ ⟨TopCat.ofHom l, TopCat.hom_ext hl⟩,
    fun ⟨l, hl⟩ ↦ ⟨l.hom, by rw [← TopCat.hom_comp, hl]⟩⟩

/-- In each simplicial degree `q`, the small augmented singular nerve is the augmented object of
maps from the topological `q`-simplex into the Čech nerve, over the maps that lift to the disjoint
union of the family. -/
def openCoverSmallAugmentedSingularNerveEvaluationIso (q : ℕ) :
    (openCoverArrow U).augmentedCechNerveMapsFrom (SimplexCategory.toTop.obj ⦋q⦌) ≅
      ((SimplicialObject.Augmented.whiskering SSet.{u} (Type u)).obj
        ((evaluation _ _).obj (op ⦋q⦌))).obj (openCoverSmallAugmentedSingularNerve U) :=
  -- `TopCat.toSSet` is `Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop`, so its
  -- `q`-simplices are by definition `ULift` of the maps out of `SimplexCategory.toTop.obj ⦋q⦌`,
  -- with `Equiv.ulift` the identification (it is also the first step of `TopCat.toSSetObjEquiv`).
  -- On both sides the simplicial operators act by postcomposition with the Čech nerve maps and the
  -- augmentations by postcomposition with `WidePullback.base`, so all squares hold by `rfl`.
  Comma.isoMk
    (NatIso.ofComponents (fun n ↦ Equiv.toIso Equiv.ulift.symm) (by
        intro n m θ
        rfl))
    (Equiv.toIso
      { toFun g := ⟨Equiv.ulift.symm g.1,
          (mem_smallSingularSubcomplex_iff_exists_comp_openCoverMap U _).2 g.2⟩
        invFun σ := ⟨Equiv.ulift σ.1,
          (mem_smallSingularSubcomplex_iff_exists_comp_openCoverMap U σ.1).1 σ.2⟩
        left_inv g := rfl
        right_inv σ := rfl })
    (by
      ext n σ
      rfl)

/-- **The singular `q`-simplices of the Čech nerve over the small `q`-simplices have an extra
degeneracy.** In each simplicial degree `q`, the small augmented singular nerve of a family of open
sets, as an augmented simplicial set in the Čech direction, has an extra degeneracy. It inserts a
chosen lift of the underlying small simplex to the disjoint union of the family. -/
noncomputable def openCoverSmallAugmentedSingularNerveExtraDegeneracy (q : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering SSet.{u} (Type u)).obj
        ((evaluation _ _).obj (op ⦋q⦌))).obj (openCoverSmallAugmentedSingularNerve U)) :=
  .ofIso (openCoverSmallAugmentedSingularNerveEvaluationIso U q)
    (Arrow.AugmentedCechNerveMapsFrom.extraDegeneracy (openCoverArrow U) _)

variable {C : Type v} [Category C] [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C]
  (R : C)

/-- The augmentation of the Čech--singular bicomplex of a family of open sets onto the singular
chains which are small for the family, placed in Čech degree zero. -/
def openCoverSmallSingularAugmentation :
    openCoverSingularBicomplex U R ⟶
      (ChainComplex.single₀ (ChainComplex C ℕ)).obj
        ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R) :=
  AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering SSet.{u} (ChainComplex C ℕ)).obj
      ((SSet.chainComplexFunctor C).obj R)).obj (openCoverSmallAugmentedSingularNerve U))

/-- In Čech degree zero, the augmentation onto small chains is the chain map induced by the
augmentation of the small augmented singular nerve. -/
@[simp]
theorem openCoverSmallSingularAugmentation_f_zero :
    (openCoverSmallSingularAugmentation U R).f 0 =
      ((SSet.chainComplexFunctor C).obj R).map
        ((openCoverSmallAugmentedSingularNerve U).hom.app (op ⦋0⦌)) := by
  rw [openCoverSmallSingularAugmentation, AlternatingFaceMapComplex.ε_app_f_zero]
  dsimp [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj]
  -- The whiskered augmentation ends with the component of `Functor.constComp`, an identity.
  exact Category.comp_id _

/-- The augmentation onto small chains followed by their inclusion is the augmentation onto all
singular chains. -/
@[reassoc (attr := simp)]
theorem openCoverSmallSingularAugmentation_comp_single₀_map :
    openCoverSmallSingularAugmentation U R ≫ (ChainComplex.single₀ _).map
        (SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R) =
      openCoverSingularAugmentation U R := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, openCoverSmallSingularAugmentation_f_zero,
    ChainComplex.single₀_map_f_zero, openCoverSingularAugmentation_f_zero]
  -- The image of `openCoverSmallAugmentedSingularNerve_hom_app_ι` under the chain complex functor.
  exact (((SSet.chainComplexFunctor C).obj R).map_comp _ _).symm.trans
    (congrArg _ (openCoverSmallAugmentedSingularNerve_hom_app_ι U _))

/-- **The rows of the Čech--singular bicomplex resolve the small singular chains.** In each
singular degree `q`, the augmentation of the `q`-th row of the bicomplex onto the small singular
`q`-chains is a chain homotopy equivalence. -/
noncomputable def openCoverSmallSingularAugmentationRowHomotopyEquiv (q : ℕ) :
    HomotopyEquiv
      (((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).obj
        (openCoverSingularBicomplex U R))
      (((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).obj
        ((ChainComplex.single₀ (ChainComplex C ℕ)).obj
          ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R))) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (HomologicalComplex.eval C (ComplexShape.down ℕ) q)).app (openCoverSingularNerve U R))).trans
    ((((openCoverSmallAugmentedSingularNerveExtraDegeneracy U q).map
      (sigmaConst.obj R)).homotopyEquiv).trans
      (HomotopyEquiv.ofIso (HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ match i with
          | 0 => Iso.refl _
          | _ + 1 => (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)).iso
              ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero
                (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp))))
        (fun i j _ ↦ (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by
          simp only [ComplexShape.down_Rel] at *; omega)).eq_of_src _ _))))

/-- The homotopy equivalence of a row is the row of the augmentation onto small chains. -/
@[simp]
theorem openCoverSmallSingularAugmentationRowHomotopyEquiv_hom (q : ℕ) :
    (openCoverSmallSingularAugmentationRowHomotopyEquiv U R q).hom =
      ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).map
        (openCoverSmallSingularAugmentation U R) := by
  ext (_ | _)
  · -- Unfold the composite: its middle stage is, by the definition of
    -- `ExtraDegeneracy.homotopyEquiv`, the augmentation `AlternatingFaceMapComplex.ε.app` of the
    -- evaluated nerve, which in degree `0` is the row of the augmentation onto small chains. The
    -- outer stages are identities in degree `0`. Rewriting with `HomotopyEquiv.trans_hom` or
    -- `HomologicalComplex.comp_f` fails here: the stages compose only up to definitional equality.
    dsimp only [openCoverSmallSingularAugmentationRowHomotopyEquiv, HomotopyEquiv.trans,
      HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
    exact (Category.id_comp (obj := C) _).trans (Category.comp_id _)
  · exact ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp))).eq_of_tgt _ _

end TauCeti.TopCat
