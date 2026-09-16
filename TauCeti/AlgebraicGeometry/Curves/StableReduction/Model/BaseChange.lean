/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.DVRExtension.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic

/-!
# Base change of models over discrete valuation rings

A chosen finite extension of a discrete valuation ring carries a model to the pullback model over
the chosen local ring.  Its prescribed generic fibre is the scalar extension of the original
curve to the extension field.  The generic-fibre identification is the canonical comparison
between the two ways of pulling the total space to that field.

This file constructs base change on both models and their morphisms and packages it as a functor.
The construction retains the chosen generic-fibre identification, so it can be iterated when
comparing models after a common finite extension.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

private noncomputable def baseChangeEta (E : FiniteDVRExtension R K)
    (M : Model R K C toK) :
    genericFiber R E.localRing M.toBase ≅
      Over.mk (genericFiber R E.localRing M.toBase).hom :=
  Over.isoMk (Iso.refl _)

/-- The canonical identification between the generic fibre of the pullback model and the scalar
extension of the prescribed generic fibre. -/
noncomputable def baseChangeGenericFiberIso (E : FiniteDVRExtension R K)
    (M : Model R K C toK) :
    genericFiber E.localRing E.extensionField
        (genericFiber R E.localRing M.toBase).hom ≅
      genericFiber K E.extensionField toK :=
  (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E.localRing E.extensionField)))).mapIso
        (baseChangeEta E M)).symm.trans
    (((genericFiberTowerNatIso R E.localRing E.extensionField).app
        (Over.mk M.toBase)).symm.trans
      (((genericFiberTowerNatIso R K E.extensionField).app
        (Over.mk M.toBase)).trans
          ((Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap K E.extensionField)))).mapIso
              M.genericFiberIso))))

/-- Base change of a model to the chosen local ring of a finite DVR extension. -/
-- Exposure is required because the projection lemmas below compare morphisms whose domains use
-- the resulting total space.
@[expose]
noncomputable def baseChange (E : FiniteDVRExtension R K) (M : Model R K C toK) :
    Model E.localRing E.extensionField
      (genericFiber K E.extensionField toK).left
      (genericFiber K E.extensionField toK).hom where
  total := (genericFiber R E.localRing M.toBase).left
  toBase := (genericFiber R E.localRing M.toBase).hom
  flat := by
    let _ : Flat M.toBase := M.flat
    rw [genericFiber_hom]
    infer_instance
  locallyOfFinitePresentation := by
    let _ : LocallyOfFinitePresentation M.toBase := M.locallyOfFinitePresentation
    rw [genericFiber_hom]
    infer_instance
  quasiCompact := by
    let _ : QuasiCompact M.toBase := M.quasiCompact
    rw [genericFiber_hom]
    infer_instance
  quasiSeparated := by
    let _ : QuasiSeparated M.toBase := M.quasiSeparated
    rw [genericFiber_hom]
    infer_instance
  genericFiberIso := baseChangeGenericFiberIso E M

@[simp]
lemma baseChange_total (E : FiniteDVRExtension R K) (M : Model R K C toK) :
    (baseChange E M).total = (genericFiber R E.localRing M.toBase).left :=
  (rfl)

@[simp]
lemma baseChange_toBase (E : FiniteDVRExtension R K) (M : Model R K C toK) :
    (baseChange E M).toBase = (genericFiber R E.localRing M.toBase).hom :=
  (rfl)

/-- The chosen generic-fibre identification of a base-changed model is the canonical tower
comparison. -/
@[simp]
lemma baseChange_genericFiberIso (E : FiniteDVRExtension R K) (M : Model R K C toK) :
    (baseChange E M).genericFiberIso = baseChangeGenericFiberIso E M :=
  (rfl)

private noncomputable def overHom {M N : Model R K C toK} (f : M ⟶ N) :
    Over.mk M.toBase ⟶ Over.mk N.toBase :=
  Over.homMk f.hom f.overBase

private lemma overHom_id (M : Model R K C toK) : overHom (𝟙 M) = 𝟙 (Over.mk M.toBase) := by
  ext
  rfl

private lemma overHom_comp {M N P : Model R K C toK} (f : M ⟶ N) (g : N ⟶ P) :
    overHom (f ≫ g) = overHom f ≫ overHom g := by
  ext
  rfl

private noncomputable def baseChangeOverMap (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    Over.mk (genericFiber R E.localRing M.toBase).hom ⟶
      Over.mk (genericFiber R E.localRing N.toBase).hom :=
  Over.homMk
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))).map
      (overHom f)).left)
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))).map
      (overHom f)).w)

private lemma baseChangeEta_naturality (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    baseChangeOverMap E f ≫ (baseChangeEta E N).inv =
      (baseChangeEta E M).inv ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))).map
          (overHom f) := by
  ext
  rfl

private noncomputable def baseChangeMapHom (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    (baseChange E M).total ⟶ (baseChange E N).total :=
  (baseChangeOverMap E f).left

private lemma baseChangeMapHom_overBase (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    baseChangeMapHom E f ≫ (baseChange E N).toBase = (baseChange E M).toBase :=
  (baseChangeOverMap E f).w

private lemma baseChangeHom_baseChangeMapHom (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    (baseChange E M).baseChangeHom (baseChangeMapHom E f)
        (baseChangeMapHom_overBase E f) =
      ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap E.localRing E.extensionField)))).map
          (baseChangeOverMap E f)).left := by
  have h : (Over.homMk (baseChangeMapHom E f) (baseChangeMapHom_overBase E f) :
      Over.mk (baseChange E M).toBase ⟶ Over.mk (baseChange E N).toBase) =
        baseChangeOverMap E f := by
    ext
    rfl
  rw [baseChangeHom_def]
  exact congrArg (fun g => ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap E.localRing E.extensionField)))).map g).left) h

private lemma baseChangeMap_genericFiber (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    (baseChange E M).baseChangeHom (baseChangeMapHom E f)
        (baseChangeMapHom_overBase E f) ≫
      (baseChange E N).genericFiberIso.hom.left =
        (baseChange E M).genericFiberIso.hom.left := by
  rw [baseChangeHom_baseChangeMapHom]
  have hfOver :
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (overHom f) ≫
          N.genericFiberIso.hom = M.genericFiberIso.hom := by
    have hfg := f.genericFiber
    rw [baseChangeHom_def] at hfg
    ext
    simpa only [overHom, Over.comp_left] using hfg
  have hNatLocal :
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing))) ⋙
          Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap E.localRing E.extensionField)))).map
            (overHom f) ≫
          ((genericFiberTowerNatIso R E.localRing E.extensionField).app
            (Over.mk N.toBase)).inv =
        ((genericFiberTowerNatIso R E.localRing E.extensionField).app
            (Over.mk M.toBase)).inv ≫
          (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R E.extensionField)))).map
              (overHom f) := by
    simpa only [Iso.app_inv] using
      (genericFiberTowerNatIso R E.localRing E.extensionField).inv.naturality (overHom f)
  have hNatField :
      (Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R E.extensionField)))).map
            (overHom f) ≫
          ((genericFiberTowerNatIso R K E.extensionField).app (Over.mk N.toBase)).hom =
        ((genericFiberTowerNatIso R K E.extensionField).app (Over.mk M.toBase)).hom ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E.extensionField)))).map
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
              (overHom f)) :=
    (genericFiberTowerNatIso R K E.extensionField).hom.naturality (overHom f)
  have hCore :
      ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap E.localRing E.extensionField)))).map
          (baseChangeOverMap E f)) ≫ (baseChangeGenericFiberIso E N).hom =
        (baseChangeGenericFiberIso E M).hom := by
    rw [baseChangeGenericFiberIso, baseChangeGenericFiberIso]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom]
    rw [← Functor.map_comp_assoc, baseChangeEta_naturality]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    rw [reassoc_of% hNatLocal, reassoc_of% hNatField]
    simp only [← Functor.map_comp, hfOver]
  rw [baseChange_genericFiberIso, baseChange_genericFiberIso]
  -- Taking `Over.Hom.left` turns the composite in `hCore` into the composite in the goal;
  -- the remaining conversions identify the chosen pullback presentations definitionally.
  convert congrArg Over.Hom.left hCore using 1 <;> rfl

/-- Base change of a morphism of models. -/
noncomputable def baseChangeMap (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) : baseChange E M ⟶ baseChange E N where
  hom := baseChangeMapHom E f
  overBase := baseChangeMapHom_overBase E f
  genericFiber := baseChangeMap_genericFiber E f

/-- The map on total spaces underlying base change of a model morphism is obtained by applying
the pullback functor. -/
@[simp]
lemma hom_baseChangeMap (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    (baseChangeMap E f).hom =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))).map
        (Over.homMk f.hom f.overBase)).left :=
  (rfl)

/-- Pullback to a chosen finite DVR extension defines a functor on models. -/
-- Exposure is required because the map characterization below has source and target involving
-- the functor's object projection.
@[expose]
noncomputable def baseChangeFunctor (E : FiniteDVRExtension R K) :
    Model R K C toK ⥤
      Model E.localRing E.extensionField
        (genericFiber K E.extensionField toK).left
        (genericFiber K E.extensionField toK).hom where
  obj := baseChange E
  map := baseChangeMap E
  map_id M := by
    apply Hom.ext
    rw [hom_baseChangeMap]
    have h := congrArg Over.Hom.left
      ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))).map_id
          (Over.mk M.toBase))
    rw [← overHom_id M, Over.id_left] at h
    -- The functor law uses the pullback object, while the goal uses its definitionally equal
    -- presentation as the total space of `baseChange E M`.
    convert h using 1
    all_goals rfl
  map_comp f g := by
    apply Hom.ext
    rw [comp_hom, hom_baseChangeMap, hom_baseChangeMap, hom_baseChangeMap]
    have h := congrArg Over.Hom.left
      ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R E.localRing)))).map_comp
          (overHom f) (overHom g))
    rw [← overHom_comp f g, Over.comp_left] at h
    -- As in `map_id`, only the definitionally equal presentations of the pullbacks differ.
    convert h using 1
    all_goals rfl

/-- The object part of the model base-change functor is pullback of models. -/
@[simp]
lemma baseChangeFunctor_obj (E : FiniteDVRExtension R K) (M : Model R K C toK) :
    (baseChangeFunctor E).obj M = baseChange E M :=
  (rfl)

/-- The morphism part of the model base-change functor is pullback of model morphisms. -/
@[simp]
lemma baseChangeFunctor_map (E : FiniteDVRExtension R K)
    {M N : Model R K C toK} (f : M ⟶ N) :
    (baseChangeFunctor E).map f = baseChangeMap E f :=
  (rfl)

/-- Proper models remain proper after base change to the chosen finite DVR extension. -/
lemma isProper_baseChange (E : FiniteDVRExtension R K) (M : Model R K C toK)
    (hM : M.IsProper) : (baseChange E M).IsProper := by
  let _ : AlgebraicGeometry.IsProper M.toBase := hM
  -- `baseChange_toBase` cannot rewrite this dependent morphism property: its source contains
  -- Mathlib's opaque chosen pullback. The change is exactly the defining projection equality.
  change AlgebraicGeometry.IsProper (genericFiber R E.localRing M.toBase).hom
  rw [genericFiber_hom]
  infer_instance

end Model

end TauCeti
