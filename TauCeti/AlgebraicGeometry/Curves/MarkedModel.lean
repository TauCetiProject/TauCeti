/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Marked models over schemes

A marked model is a flat finitely presented scheme over a base with a prescribed identification
of its generic fibre. Over an integral scheme `S`, use the canonical morphism
`S.fromSpecStalk (genericPoint S) : Spec S.functionField ⟶ S` as the generic point. The
construction takes that morphism as a parameter, so it also accepts a chosen fraction field on an
affine base and supports base change of the model and marking together.

Morphisms preserve the marking and are unique when the target is separated and the generic
point morphism is quasi-compact and schematically dominant. Over a DVR this category agrees with
`TauCeti.Model`, retaining both the structure morphism and the generic marking.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

/-- A flat finitely presented model of `C` along `j : η ⟶ S`, with its pullback along `j`
identified with `C` in `Over η`. No properness or separatedness is imposed on the model. -/
structure MarkedModel {η S : Scheme.{u}} (j : η ⟶ S) (C : Over η) where
  /-- The model over the base. -/
  model : Over S
  /-- The chosen generic-fibre identification. -/
  genericIso : (Over.pullback j).obj model ≅ C
  /-- Flatness of the structure morphism. -/
  flat : Flat model.hom
  /-- Local finite presentation of the structure morphism. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation model.hom
  /-- Quasi-compactness of the structure morphism. -/
  quasiCompact : QuasiCompact model.hom
  /-- Quasi-separatedness of the structure morphism. -/
  quasiSeparated : QuasiSeparated model.hom

namespace MarkedModel

attribute [instance] flat locallyOfFinitePresentation quasiCompact quasiSeparated

variable {η S : Scheme.{u}} {j : η ⟶ S} {C : Over η}

/-- A morphism of marked models is a morphism over the base compatible with the generic
identifications. -/
@[ext]
structure Hom (M N : MarkedModel j C) where
  /-- The morphism over the base. -/
  hom : M.model ⟶ N.model
  /-- The induced morphism on the generic fibre respects the markings. -/
  generic : (Over.pullback j).map hom ≫ N.genericIso.hom = M.genericIso.hom

attribute [reassoc (attr := simp)] Hom.generic

/-- Marked models of a fixed scheme form a category. -/
instance : Category (MarkedModel j C) where
  Hom := Hom
  id _ := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by simp⟩
  id_comp f := Hom.ext (by simp)
  comp_id f := Hom.ext (by simp)
  assoc f g h := Hom.ext (by simp)

@[simp]
lemma id_hom (M : MarkedModel j C) : Hom.hom (𝟙 M) = 𝟙 M.model := (rfl)

@[simp]
lemma comp_hom {M N P : MarkedModel j C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g : M ⟶ P).hom = f.hom ≫ g.hom := (rfl)

/-- For a quasi-compact schematically dominant `j`, morphisms to a separated model are unique.
The source model may be nonreduced. -/
instance subsingleton_hom (M N : MarkedModel j C) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [IsSeparated N.model.hom] : Subsingleton (M ⟶ N) where
  allEq f g := by
    apply Hom.ext
    apply Over.OverMorphism.ext
    have h : (Over.pullback j).map f.hom = (Over.pullback j).map g.hom := by
      rw [← cancel_mono N.genericIso.hom, f.generic, g.generic]
    refine ext_of_isSchemeTheoreticallyDominant (pullback.fst M.model.hom j) N.model.hom
      (by simp) ?_
    simpa using congrArg (fun k ↦ k.left ≫ pullback.fst N.model.hom j) h

/-- Over an integral scheme, marked morphisms into a separated model are unique. -/
instance subsingleton_hom_fromSpecStalk_genericPoint [IsIntegral S]
    {D : Over (Spec S.functionField)}
    (M N : MarkedModel (S.fromSpecStalk (genericPoint S)) D) [IsSeparated N.model.hom] :
    Subsingleton (M ⟶ N) := by
  have := IsSchemeTheoreticallyDominant.of_isDominant (S.fromSpecStalk (genericPoint S))
  exact subsingleton_hom M N

section BaseChange

variable {η' S' : Scheme.{u}} {j' : η' ⟶ S'} {s : S' ⟶ S} {t : η' ⟶ η}
  (h : j' ≫ s = t ≫ j)

/-- Pull back a marked model by a commutative square of base and generic-point maps. The square
need not be cartesian: the marking is obtained by comparing the two iterated pullbacks. -/
def baseChange (M : MarkedModel j C) : MarkedModel j' ((Over.pullback t).obj C) where
  model := (Over.pullback s).obj M.model
  genericIso := ((Over.pullbackComp j' s).symm.app M.model) ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj M.model) h) ≪≫
    (Over.pullbackComp t j).app M.model ≪≫ (Over.pullback t).mapIso M.genericIso
  flat := inferInstanceAs (Flat (pullback.snd M.model.hom s))
  locallyOfFinitePresentation :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd M.model.hom s))
  quasiCompact := inferInstanceAs (QuasiCompact (pullback.snd M.model.hom s))
  quasiSeparated := inferInstanceAs (QuasiSeparated (pullback.snd M.model.hom s))

/-- The underlying object of a base-changed model is the pullback over the new base. -/
@[simp]
lemma baseChange_model (M : MarkedModel j C) :
    (M.baseChange h).model = (Over.pullback s).obj M.model := (rfl)

/-- The base-changed marking is the pullback of the marking after comparing iterated pullbacks. -/
lemma baseChange_genericIso (M : MarkedModel j C) :
    (M.baseChange h).genericIso =
      eqToIso (congrArg (Over.pullback j').obj (M.baseChange_model h)) ≪≫
      ((Over.pullbackComp j' s).symm.app M.model) ≪≫
      eqToIso (congrArg (fun f ↦ (Over.pullback f).obj M.model) h) ≪≫
      (Over.pullbackComp t j).app M.model ≪≫ (Over.pullback t).mapIso M.genericIso := by
  exact (Iso.refl_trans _).symm

/-- Base change preserves properness of a marked model. -/
instance (M : MarkedModel j C) [IsProper M.model.hom] : IsProper (M.baseChange h).model.hom := by
  rw [baseChange_model]
  exact inferInstanceAs (IsProper (pullback.snd M.model.hom s))

end BaseChange

section IntegralBase

variable [IrreducibleSpace S] {D : Over (Spec S.functionField)}
  (M : MarkedModel (S.fromSpecStalk (genericPoint S)) D)

/-- Pull back a model along a dominant morphism of irreducible schemes. For integral bases the
marking is extended along the induced map of function fields. This applies in particular to any
nonempty open of the base. -/
def dominantBaseChange {S' : Scheme.{u}} [IrreducibleSpace S'] (s : S' ⟶ S) [IsDominant s] :
    MarkedModel (S'.fromSpecStalk (genericPoint S'))
      ((Over.pullback (Spec.map s.functionFieldMap)).obj D) :=
  M.baseChange s.SpecMap_functionFieldMap_fromSpecStalk.symm

/-- The total space and structural map of a dominant base change are given by pullback. -/
@[simp]
lemma dominantBaseChange_model {S' : Scheme.{u}} [IrreducibleSpace S'] (s : S' ⟶ S)
    [IsDominant s] : (M.dominantBaseChange s).model = (Over.pullback s).obj M.model :=
  M.baseChange_model _

/-- Restrict a model to the spectrum of a stalk of the base. The marking uses the same generic
stalk, via the map from the stalk at `x` to the generic stalk. -/
def localize (x : S) : MarkedModel
    (Spec.map (S.presheaf.stalkSpecializes (genericPoint_specializes x))) D :=
  let N := M.baseChange (t := 𝟙 _) (show
    Spec.map (S.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ S.fromSpecStalk x =
      𝟙 _ ≫ S.fromSpecStalk (genericPoint S) by
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Category.id_comp])
  { N with genericIso := N.genericIso ≪≫ Over.pullbackId.app D }

/-- The underlying scheme over the local base is the pullback along its local-spectrum map. -/
@[simp]
lemma localize_model (x : S) :
    (M.localize x).model = (Over.pullback (S.fromSpecStalk x)).obj M.model := (rfl)

end IntegralBase

/-- When the generic-point map is the identity (in particular for a field base), the marking
identifies the original model over the base with the prescribed scheme. -/
def isoOfId {D : Over S} (M : MarkedModel (𝟙 S) D) : M.model ≅ D :=
  (Over.pullbackId.app M.model).symm ≪≫ M.genericIso

/-- The identification over the identity base map recovers the specified generic marking. -/
@[reassoc (attr := simp)]
lemma pullbackId_hom_isoOfId_hom {D : Over S} (M : MarkedModel (𝟙 S) D) :
    (Over.pullbackId.hom.app M.model) ≫ M.isoOfId.hom = M.genericIso.hom := by
  simp [isoOfId]

section DVR

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}} {toK : X ⟶ Spec (.of K)}

local notation "jK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- Interpret a DVR model as a marked model over the spectrum of the DVR. -/
def ofDVR : Model R K X toK ⥤ MarkedModel jK (Over.mk toK) where
  obj M := ⟨Over.mk M.toBase, M.genericFiberIso, M.flat, M.locallyOfFinitePresentation,
    M.quasiCompact, M.quasiSeparated⟩
  map f := ⟨Over.homMk f.hom f.overBase, Over.OverMorphism.ext (by
    simpa only [Over.comp_left, Model.baseChangeHom_def] using f.genericFiber)⟩
  map_id M := Hom.ext (Over.OverMorphism.ext (by simp))
  map_comp f g := Hom.ext (Over.OverMorphism.ext (by simp))

/-- Interpret a marked model over the spectrum of a DVR as a DVR model. -/
def toDVR : MarkedModel jK (Over.mk toK) ⥤ Model R K X toK where
  obj M := ⟨M.model.left, M.model.hom, M.flat, M.locallyOfFinitePresentation,
    M.quasiCompact, M.quasiSeparated, M.genericIso⟩
  map f := ⟨f.hom.left, f.hom.w, by
    simpa only [Model.baseChangeHom_def, Over.comp_left, Over.homMk_eta] using
      congrArg Over.Hom.left f.generic⟩
  map_id M := Model.Hom.ext (by simp)
  map_comp f g := Model.Hom.ext (by simp)

/-- The two definitions of marked models over the spectrum of a DVR give equivalent categories. -/
def dvrEquivalence : Model R K X toK ≌ MarkedModel jK (Over.mk toK) where
  functor := ofDVR
  inverse := toDVR
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N f; simp; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N f; simp; rfl)

/-- The equivalence retains the structural map, including its source. -/
@[simp]
lemma ofDVR_obj_model (M : Model R K X toK) : (ofDVR.obj M).model = Over.mk M.toBase := (rfl)

/-- The equivalence retains the marking, transported by the identification of the objects over
`Spec R`. -/
lemma ofDVR_obj_genericIso (M : Model R K X toK) : (ofDVR.obj M).genericIso =
    eqToIso (congrArg (Over.pullback jK).obj (ofDVR_obj_model M)) ≪≫ M.genericFiberIso :=
  (Iso.refl_trans _).symm

/-- Properness is preserved and reflected by the comparison over a DVR. -/
@[simp]
lemma isProper_ofDVR_obj_iff (M : Model R K X toK) :
    IsProper (ofDVR.obj M).model.hom ↔ M.IsProper := Iff.rfl

end DVR

end MarkedModel

end TauCeti
