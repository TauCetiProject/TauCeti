/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Augmentation
public import TauCeti.Topology.Sheaves.Cech.Hypercohomology

/-!
# Global-section comparison for Čech hypercohomology

The comparison from the cohomology of global sections to cover-colimit Čech
hypercohomology respects every point-cover structure map. On compact spaces,
it is an isomorphism whenever finite covers compute global sections.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory

universe u u' v'

namespace TauCeti.Topology

variable {X : TopCat.{u}} {A : Type u'} [Category.{v'} A] [Preadditive A]
  [HasZeroObject A] [HasProducts.{u} A] [HasCoproducts.{0} A] [CategoryWithHomology A]
  [HasColimitsOfShape (PointOpenCover X) A]
  (P : (Opens X)ᵒᵖ ⥤ CochainComplex A ℤ) (n : ℤ)

private lemma augmentation_comp_structure_eq (U V : PointOpenCover X) :
    HomologicalComplex.homologyMap
        (cechTotalComplexAugmentation U.opens isTerminalTop P) n ≫
      (cechHypercohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n U).app P =
    HomologicalComplex.homologyMap
        (cechTotalComplexAugmentation V.opens isTerminalTop P) n ≫
      (cechHypercohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n V).app P := by
  suffices ∀ U W : PointOpenCover X, U ≤ W →
      HomologicalComplex.homologyMap
          (cechTotalComplexAugmentation U.opens isTerminalTop P) n ≫
        (cechHypercohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n U).app P =
      HomologicalComplex.homologyMap
          (cechTotalComplexAugmentation W.opens isTerminalTop P) n ≫
        (cechHypercohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n W).app P by
    exact (this U (U.inter V) (U.le_inter_left V)).trans
      (this V (U.inter V) (U.le_inter_right V)).symm
  intro U W h
  rw [← cechTotalComplexAugmentation_refinement W.opens isTerminalTop P h.some,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    homologyMap_cechTotalComplexMap_comp_cechHypercohomologyι_app _ _ _ h h.some P]

/-- Global-section cohomology maps canonically to the existing cover-colimit
Čech hypercohomology. No boundedness or sheaf condition is required. -/
def cechHypercohomologyAugmentation :
    (P.obj (op ⊤)).homology n ⟶ (cechHypercohomology X A n).obj P :=
  HomologicalComplex.homologyMap
      (cechTotalComplexAugmentation (default : PointOpenCover X).opens isTerminalTop P) n ≫
    (cechHypercohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n default).app P

/-- The comparison is the augmentation followed by the structure map of every
point-neighborhood cover, including covers with infinitely many distinct members. -/
@[reassoc]
lemma homologyMap_cechTotalComplexAugmentation_comp_ι (W : PointOpenCover X) :
    HomologicalComplex.homologyMap
        (cechTotalComplexAugmentation W.opens isTerminalTop P) n ≫
      (cechHypercohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n W).app P =
    cechHypercohomologyAugmentation P n :=
  augmentation_comp_structure_eq P n W default

/-- The global-section comparison is natural in the presheaf of complexes. -/
@[reassoc]
lemma cechHypercohomologyAugmentation_naturality
    {Q : (Opens X)ᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    cechHypercohomologyAugmentation P n ≫ (cechHypercohomology X A n).map α =
      HomologicalComplex.homologyMap (α.app (op ⊤)) n ≫
        cechHypercohomologyAugmentation Q n := by
  unfold cechHypercohomologyAugmentation
  rw [Category.assoc, cechHypercohomologyι_naturality, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, cechTotalComplexAugmentation_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc]

omit [HasColimitsOfShape (PointOpenCover X) A] in
private lemma isIso_augmentation_finiteRange
    (hfinite : ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), IsOpenCover U →
      IsIso (HomologicalComplex.homologyMap
        (cechTotalComplexAugmentation U isTerminalTop P) n))
    (W : finiteRangePointCover X) :
    IsIso (HomologicalComplex.homologyMap
      (cechTotalComplexAugmentation W.val.opens isTerminalTop P) n) := by
  classical
  let ι := Set.range W.val.opens
  let : Finite ι := W.property.to_subtype
  let U : ι → Opens X := Subtype.val
  have hU : IsOpenCover U := top_unique fun x _ ↦
    Opens.mem_iSup.mpr ⟨⟨W.val.opens x, ⟨x, rfl⟩⟩, W.val.mem_opens x⟩
  let φ : W.val.toFormalCoproduct ⟶ FormalCoproduct.mk ι U :=
    ⟨fun x ↦ ⟨W.val.opens x, ⟨x, rfl⟩⟩, fun _ ↦ 𝟙 _⟩
  let ψ : FormalCoproduct.mk ι U ⟶ W.val.toFormalCoproduct :=
    ⟨fun i ↦ i.property.choose, fun i ↦ homOfLE (by
      -- Expose the range-subtype member and the chosen original index.
      change i.val ≤ W.val.opens i.property.choose
      exact le_of_eq i.property.choose_spec.symm)⟩
  have := hfinite ι U hU
  have := isIso_cechTotalComplexHomologyMap_of_reverse A n φ ψ
  have hφ : IsIso (HomologicalComplex.homologyMap (cechTotalComplexMap P φ) n) := by
    rw [← cechTotalComplexHomologyMap_app]
    infer_instance
  rw [← cechTotalComplexAugmentation_refinement W.val.opens isTerminalTop P φ,
    HomologicalComplex.homologyMap_comp]
  infer_instance

/-- On a compact space, if every finite cover computes the cohomology of global
sections in degree `n`, then so does the colimit over all point-neighborhood covers. -/
theorem isIso_cechHypercohomologyAugmentation_of_finite [CompactSpace X]
    (hfinite : ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), IsOpenCover U →
      IsIso (HomologicalComplex.homologyMap
        (cechTotalComplexAugmentation U isTerminalTop P) n)) :
    IsIso (cechHypercohomologyAugmentation P n) := by
  let F := finiteRangePointCover.inclusion (X := X)
  let D := (cechHypercohomologyDiagram A
    PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n).flip.obj P
  let W : finiteRangePointCover X := Classical.arbitrary _
  have haug (V : finiteRangePointCover X) := isIso_augmentation_finiteRange P n hfinite V
  have heventual : (F ⋙ D).IsEventuallyConstantFrom W := by
    intro V f
    dsimp only [Functor.comp_map, D, Functor.flip_obj_map]
    rw [cechHypercohomologyDiagram_map _ _ _ _ (F.map f) (leOfHom f).some,
      cechTotalComplexHomologyMap_app]
    have h := cechTotalComplexAugmentation_refinement V.val.opens isTerminalTop P
      (leOfHom f).some
    have hf := congrArg (fun a ↦ HomologicalComplex.homologyMap a n) h
    rw [HomologicalComplex.homologyMap_comp] at hf
    have := haug V
    have := haug W
    exact IsIso.of_isIso_fac_left hf
  have hi : IsIso (colimit.ι (F ⋙ D) W) :=
    heventual.isIso_ι_of_isColimit (colimit.isColimit (F ⋙ D))
  have hι : IsIso (colimit.ι D W.val) := by
    have hi' := IsIso.comp_isIso' hi (inferInstance : IsIso (colimit.pre D F))
    rw [colimit.ι_pre] at hi'
    simpa only [F, finiteRangePointCover.inclusion, Monotone.functor_obj] using hi'
  rw [← homologyMap_cechTotalComplexAugmentation_comp_ι P n W.val]
  rw [cechHypercohomologyι_app]
  have := haug W
  exact IsIso.comp_isIso' (haug W) hι

end TauCeti.Topology
