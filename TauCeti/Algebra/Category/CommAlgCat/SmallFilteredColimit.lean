/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Final
public import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-!
# Small filtered colimits of commutative algebras

An essentially small algebra-valued diagram has a colimit algebra with canonical stage maps and
a descent map for each cocone. When the indexing category is also filtered, every element of the
colimit comes from some stage, and algebra maps into a target in any universe are determined
stagewise. A compatible family of stage maps into a target in any universe descends to the colimit
algebra. These interfaces are shared by the henselization and strict-henselization
constructions.
-/

public section

open CategoryTheory Limits

universe u v v' w

namespace TauCeti.SmallFilteredAlgebraColimit

variable {Base : Type u} [CommRing Base]
variable {Index : Type v} [Category.{v'} Index]
variable [EssentiallySmall.{u} Index]
variable (functor : Index ⥤ CommAlgCat.{u} Base)

/-- Essentially small diagrams of commutative algebras have colimits. -/
noncomputable instance : HasColimit functor :=
  have := hasColimitsOfShape_of_essentiallySmall.{u} Index (CommAlgCat.{u} Base)
  inferInstance

/-- The colimit algebra of an essentially small diagram. -/
noncomputable def algebra : CommAlgCat.{u} Base := colimit functor

/-- The canonical algebra map from the value of the diagram at an index object to the colimit
algebra. -/
noncomputable def stage (object : Index) :
    functor.obj object →ₐ[Base] algebra functor :=
  (colimit.ι functor object).hom

/-- Stage maps commute with morphisms of the indexing category. -/
@[simp]
theorem stage_naturality {first second : Index} (morphism : first ⟶ second) :
    (stage functor second).comp (functor.map morphism).hom = stage functor first := by
  have hleg := congrArg CommAlgCat.Hom.hom (colimit.w functor morphism)
  rw [CommAlgCat.hom_comp] at hleg
  exact hleg

/-- Elementwise form of `stage_naturality`. -/
@[simp]
theorem stage_map_apply {first second : Index} (morphism : first ⟶ second)
    (element : functor.obj first) :
    stage functor second (functor.map morphism element) = stage functor first element :=
  DFunLike.congr_fun (stage_naturality functor morphism) element

/-- A cocone on the indexing category descends to the colimit. -/
noncomputable def desc (cocone : Cocone functor) :
    algebra functor →ₐ[Base] cocone.pt :=
  (colimit.desc functor cocone).hom

/-- Descending a cocone agrees with its map at every stage. -/
@[simp]
theorem desc_comp_stage (cocone : Cocone functor) (object : Index) :
    (desc functor cocone).comp (stage functor object) = (cocone.ι.app object).hom := by
  have hleg := congrArg CommAlgCat.Hom.hom (colimit.ι_desc cocone object)
  rw [CommAlgCat.hom_comp] at hleg
  exact hleg

/-- Elementwise form of `desc_comp_stage`. -/
@[simp]
theorem desc_stage_apply (cocone : Cocone functor) (object : Index)
    (element : functor.obj object) :
    desc functor cocone (stage functor object element) = (cocone.ι.app object).hom element :=
  DFunLike.congr_fun (desc_comp_stage functor cocone object) element

/-- The restriction of the diagram to a small model of the indexing category. -/
noncomputable abbrev diagram : SmallModel.{u} Index ⥤ CommAlgCat.{u} Base :=
  (equivSmallModel.{u} Index).inverse ⋙ functor

/-- The colimit over the whole indexing category is the colimit over its small model. -/
noncomputable def algebraIsoColimitDiagram : algebra functor ≅ colimit (diagram functor) :=
  (Functor.Final.colimitIso (equivSmallModel.{u} Index).inverse functor).symm

/-- The comparison with the small-model colimit is compatible with the stage maps. -/
@[simp]
theorem algebraIsoColimitDiagram_inv_comp_ι (smallObject : SmallModel.{u} Index) :
    (algebraIsoColimitDiagram functor).inv.hom.comp (colimit.ι (diagram functor) smallObject).hom =
      stage functor ((equivSmallModel.{u} Index).inverse.obj smallObject) := by
  have hleg := congrArg CommAlgCat.Hom.hom
    (Functor.Final.ι_colimitIso_hom (equivSmallModel.{u} Index).inverse functor smallObject)
  rw [CommAlgCat.hom_comp] at hleg
  exact hleg

/-- Each colimit element is represented by an element of a stage. -/
theorem exists_stage_eq [IsFiltered Index] (element : algebra functor) :
    ∃ (object : Index) (value : functor.obj object),
      stage functor object value = element := by
  let equivalence := equivSmallModel.{u} Index
  let _ : IsFiltered (SmallModel.{u} Index) := IsFiltered.of_equivalence equivalence
  have _ : PreservesColimitsOfShape Index (forget (CommAlgCat.{u} Base)) :=
    preservesColimitsOfShape_of_equiv equivalence.symm _
  exact Concrete.colimit_exists_rep functor element

/-- For a filtered diagram, algebra maps out of the colimit into a target in any universe agree
when they agree on each stage. -/
@[ext]
theorem hom_ext [IsFiltered Index] {Target : Type w}
    [Semiring Target] [Algebra Base Target]
    {first second : algebra functor →ₐ[Base] Target}
    (hequal : ∀ object, first.comp (stage functor object) =
      second.comp (stage functor object)) :
    first = second := by
  refine AlgHom.ext fun element => ?_
  obtain ⟨object, value, rfl⟩ := exists_stage_eq functor element
  exact DFunLike.congr_fun (hequal object) value

section DescOfCompatible

variable {Target : Type w} [CommRing Target] [Algebra Base Target]

/-- The `Base`-subalgebra of `Target` generated by the images of a family of stage maps over the
small model of the indexing category. It is `u`-small and contains the image of every stage map
of a compatible family. -/
private noncomputable abbrev familyRange (stageMap : ∀ object, functor.obj object →ₐ[Base] Target) :
    Subalgebra Base Target :=
  Algebra.adjoin Base (Set.range fun p : Σ j, (diagram functor).obj j ↦
    stageMap ((equivSmallModel.{u} Index).inverse.obj p.1) p.2)

private theorem stageMap_mem (stageMap : ∀ object, functor.obj object →ₐ[Base] Target)
    (hcompat : ∀ {first second : Index} (morphism : first ⟶ second),
      (stageMap second).comp (functor.map morphism).hom = stageMap first)
    (object : Index) (element : functor.obj object) :
    stageMap object element ∈ familyRange functor stageMap := by
  let equivalence := equivSmallModel.{u} Index
  have hmem : stageMap (equivalence.inverse.obj (equivalence.functor.obj object))
      ((functor.map (equivalence.unitIso.hom.app object)).hom element) ∈
        familyRange functor stageMap :=
    Algebra.subset_adjoin ⟨⟨equivalence.functor.obj object,
      (functor.map (equivalence.unitIso.hom.app object)).hom element⟩, rfl⟩
  -- The target of the equivalence unit is only definitionally
  -- `equivalence.inverse.obj (equivalence.functor.obj object)`.
  convert hmem using 1
  exact (DFunLike.congr_fun (hcompat (equivalence.unitIso.hom.app object)) element).symm

/-- The cocone on the diagram given by a compatible family of stage maps, with apex a small model
of the subalgebra they generate. -/
private noncomputable def familyCocone (stageMap : ∀ object, functor.obj object →ₐ[Base] Target)
    (hcompat : ∀ {first second : Index} (morphism : first ⟶ second),
      (stageMap second).comp (functor.map morphism).hom = stageMap first) :
    Cocone functor where
  pt := CommAlgCat.of Base (Shrink.{u} (familyRange functor stageMap))
  ι :=
    { app object := CommAlgCat.ofHom <|
        (Shrink.algEquiv Base (familyRange functor stageMap)).symm.toAlgHom.comp <|
          (stageMap object).codRestrict _ (stageMap_mem functor stageMap hcompat object)
      naturality {first second} morphism := by
        ext element
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.comp_apply]
        congr 1
        exact Subtype.ext (DFunLike.congr_fun (hcompat morphism) element) }

/-- The map from the colimit to the small model of `familyRange` induced by `familyCocone`. -/
private noncomputable def descRange (stageMap : ∀ object, functor.obj object →ₐ[Base] Target)
    (hcompat : ∀ {first second : Index} (morphism : first ⟶ second),
      (stageMap second).comp (functor.map morphism).hom = stageMap first) :
    algebra functor →ₐ[Base] Shrink.{u} (familyRange functor stageMap) :=
  desc functor (familyCocone functor stageMap hcompat)

/-- A compatible family of algebra maps from the stages into a target in any universe descends to
the colimit algebra. The colimit lives in the universe of `Base`, so the cocone is built on a small
model of the subalgebra of `Target` generated by the images of the stages. -/
noncomputable def descOfCompatible (stageMap : ∀ object, functor.obj object →ₐ[Base] Target)
    (hcompat : ∀ {first second : Index} (morphism : first ⟶ second),
      (stageMap second).comp (functor.map morphism).hom = stageMap first) :
    algebra functor →ₐ[Base] Target :=
  ((familyRange functor stageMap).val.comp
    (Shrink.algEquiv.{u} Base (familyRange functor stageMap)).toAlgHom).comp
    (descRange functor stageMap hcompat)

/-- The descent of a compatible family restricts to the family at every stage. -/
@[simp]
theorem descOfCompatible_comp_stage (stageMap : ∀ object, functor.obj object →ₐ[Base] Target)
    (hcompat : ∀ {first second : Index} (morphism : first ⟶ second),
      (stageMap second).comp (functor.map morphism).hom = stageMap first) (object : Index) :
    (descOfCompatible functor stageMap hcompat).comp (stage functor object) = stageMap object := by
  ext element
  -- `Shrink` is not exposed, so a rewrite cannot see that the apex of `familyCocone` is its
  -- carrier; `desc_stage_apply` and the leg of `familyCocone` agree by definition.
  have h : descRange functor stageMap hcompat (stage functor object element) =
      (Shrink.algEquiv Base (familyRange functor stageMap)).symm
        ⟨stageMap object element, stageMap_mem functor stageMap hcompat object element⟩ :=
    desc_stage_apply functor (familyCocone functor stageMap hcompat) object element
  simp [descOfCompatible, h]

/-- Elementwise form of `descOfCompatible_comp_stage`. -/
@[simp]
theorem descOfCompatible_stage_apply (stageMap : ∀ object, functor.obj object →ₐ[Base] Target)
    (hcompat : ∀ {first second : Index} (morphism : first ⟶ second),
      (stageMap second).comp (functor.map morphism).hom = stageMap first) (object : Index)
    (element : functor.obj object) :
    descOfCompatible functor stageMap hcompat (stage functor object element) =
      stageMap object element :=
  DFunLike.congr_fun (descOfCompatible_comp_stage functor stageMap hcompat object) element

end DescOfCompatible

end TauCeti.SmallFilteredAlgebraColimit
