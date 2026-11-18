/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Duals of line bundles

The internal-Hom dual of an invertible sheaf is again invertible. Evaluation identifies the
tensor product of a line bundle with its dual with the trivial line bundle.

## Main declarations

* `InvertibleSheaf.dual` is the dual line bundle;
* `InvertibleSheaf.dualCongr` transports an isomorphism through duality;
* `InvertibleSheaf.evaluationDualIsoSheaf` packages internal-Hom evaluation as an isomorphism;
* `InvertibleSheaf.tensorDualIso` identifies `L ⊗ L.dual` with the trivial line bundle;
* `InvertibleSheaf.dualIsoOfTensorIsoTrivial` identifies `L.dual` with `M` from a pairing
  `L ⊗ M ≅ 𝒪_X`, characterized via `tensorDualIso` and `ihom.ev`.

These constructions supply inverses for the Picard group of a scheme.
-/

public section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonoidalClosed

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The dual line bundle, defined as the internal Hom into the structure sheaf. -/
def dual (L : InvertibleSheaf X) : InvertibleSheaf X := by
  let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  exact ⟨L.obj.dual, SheafOfModules.IsInvertible.dual L.obj⟩

/-- The underlying sheaf of the dual line bundle is the internal-Hom dual. -/
@[simp]
lemma dual_obj (L : InvertibleSheaf X) :
    (dual L).obj = L.obj.dual :=
  (rfl)

/-- The sheaf isomorphism underlying transport through duality. -/
def dualCongrIso {L K : InvertibleSheaf X} (e : L ≅ K) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (dual L).obj (dual K).obj :=
  eqToIso (dual_obj L) ≪≫
    SheafOfModules.dualIso (R := X.sheaf)
      ((SheafOfModules.isInvertible X).ι.mapIso e) ≪≫
    (eqToIso (dual_obj K)).symm

/-- The forward map of `dualCongrIso` is the internal-Hom map induced by precomposition with the
inverse isomorphism, transported to the underlying sheaves of the dual line bundles. -/
lemma dualCongrIso_hom {L K : InvertibleSheaf X} (e : L ≅ K) :
    (dualCongrIso e).hom =
      (eqToIso (dual_obj L)).hom ≫
        (SheafOfModules.dualIso (R := X.sheaf)
          ((SheafOfModules.isInvertible X).ι.mapIso e)).hom ≫
        (eqToIso (dual_obj K)).inv :=
  (rfl)

/-- The inverse map of `dualCongrIso` is the internal-Hom map induced by precomposition with the
forward isomorphism, transported to the underlying sheaves of the dual line bundles. -/
lemma dualCongrIso_inv {L K : InvertibleSheaf X} (e : L ≅ K) :
    (dualCongrIso e).inv =
      (eqToIso (dual_obj K)).hom ≫
        (SheafOfModules.dualIso (R := X.sheaf)
          ((SheafOfModules.isInvertible X).ι.mapIso e)).inv ≫
        (eqToIso (dual_obj L)).inv :=
  (rfl)

/-- An isomorphism of line bundles induces an isomorphism of their duals. -/
def dualCongr {L K : InvertibleSheaf X} (e : L ≅ K) : dual L ≅ dual K :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X (dualCongrIso e))

@[simp]
lemma dualCongr_hom_val {L K : InvertibleSheaf X} (e : L ≅ K) :
    (dualCongr e).hom.hom.val = (dualCongrIso e).hom.val := by
  simp only [dualCongr, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma dualCongr_inv_val {L K : InvertibleSheaf X} (e : L ≅ K) :
    (dualCongr e).inv.hom.val = (dualCongrIso e).inv.val := by
  simp only [dualCongr, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- Evaluation of a line bundle against its internal-Hom dual, as an isomorphism of sheaves. -/
def evaluationDualIsoSheaf (L : InvertibleSheaf X) :
    L.obj ⊗ L.obj.dual ≅ SheafOfModules.unit X.ringCatSheaf :=
  let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  let evaluation := (ihom.ev L.obj).app (SheafOfModules.unit X.ringCatSheaf)
  @asIso _ _ _ _ evaluation
    (SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := X.sheaf) L.obj)

/-- The forward map of `evaluationDualIsoSheaf` is internal-Hom evaluation. -/
@[simp]
lemma evaluationDualIsoSheaf_hom (L : InvertibleSheaf X) :
    (evaluationDualIsoSheaf L).hom =
      (ihom.ev L.obj).app (SheafOfModules.unit X.ringCatSheaf) :=
  (rfl)

/-- The sheaf isomorphism underlying evaluation of a line bundle against its dual. -/
def tensorDualIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _
      (tensorProduct L (dual L)).obj (trivial X).obj :=
  eqToIso (tensorProduct_obj L (dual L)) ≪≫
    SheafOfModules.tensorProductCongrRight X.sheaf (eqToIso (dual_obj L)) ≪≫
    SheafOfModules.tensorProductIso X.sheaf L.obj L.obj.dual ≪≫
    (L.obj.tensorUnderlyingIso L.obj.dual).symm ≪≫ evaluationDualIsoSheaf L ≪≫
    (trivialObjIsoUnit X).symm

/-- The forward map of `tensorDualIsoSheaf` is the tensor comparison followed by internal-Hom
evaluation and the identification of the tensor unit with the trivial line bundle. -/
lemma tensorDualIsoSheaf_hom (L : InvertibleSheaf X) :
    (tensorDualIsoSheaf L).hom =
      (eqToIso (tensorProduct_obj L (dual L))).hom ≫
        (SheafOfModules.tensorProductCongrRight X.sheaf (eqToIso (dual_obj L))).hom ≫
        (SheafOfModules.tensorProductIso X.sheaf L.obj L.obj.dual).hom ≫
        (L.obj.tensorUnderlyingIso L.obj.dual).inv ≫
        (ihom.ev L.obj).app (SheafOfModules.unit X.ringCatSheaf) ≫
        (trivialObjIsoUnit X).inv :=
  (rfl)

/-- The inverse map of `tensorDualIsoSheaf` is the inverse evaluation map, transported back
through the tensor and trivial-bundle comparisons. -/
lemma tensorDualIsoSheaf_inv (L : InvertibleSheaf X) :
    (tensorDualIsoSheaf L).inv =
      (trivialObjIsoUnit X).hom ≫ (evaluationDualIsoSheaf L).inv ≫
        (L.obj.tensorUnderlyingIso L.obj.dual).hom ≫
        (SheafOfModules.tensorProductIso X.sheaf L.obj L.obj.dual).inv ≫
        (SheafOfModules.tensorProductCongrRight X.sheaf (eqToIso (dual_obj L))).inv ≫
        (eqToIso (tensorProduct_obj L (dual L))).inv :=
  (rfl)

/-- Tensoring a line bundle with its dual gives the trivial line bundle. -/
def tensorDualIso (L : InvertibleSheaf X) : tensorProduct L (dual L) ≅ trivial X :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X (tensorDualIsoSheaf L))

@[simp]
lemma tensorDualIso_hom_val (L : InvertibleSheaf X) :
    (tensorDualIso L).hom.hom.val = (tensorDualIsoSheaf L).hom.val := by
  simp only [tensorDualIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorDualIso_inv_val (L : InvertibleSheaf X) :
    (tensorDualIso L).inv.hom.val = (tensorDualIsoSheaf L).inv.val := by
  simp only [tensorDualIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The monoidal pairing `L.obj ⊗ M.obj ≅ 𝟙_ X.Modules` induced by `e : L ⊗ M ≅ 𝒪_X`. -/
private def pairingIso {L M : InvertibleSheaf X} (e : tensorProduct L M ≅ trivial X) :
    @Iso (_root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf)) _
      ((L.obj : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf)) ⊗ M.obj)
      (𝟙_ (_root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf))) :=
  (tensorProductObjIso L M).symm ≪≫ (SheafOfModules.isInvertible X).ι.mapIso e ≪≫
    trivialObjIsoUnit X

/-- The transpose `M.obj ⟶ L.obj.dual` of `e : L ⊗ M ≅ 𝒪_X` under the internal-Hom adjunction. -/
private def curryPairing {L M : InvertibleSheaf X} (e : tensorProduct L M ≅ trivial X) :
    @Quiver.Hom (_root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf)) _
      (M.obj : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf))
      (SheafOfModules.dual (R := X.sheaf) L.obj) :=
  MonoidalClosed.curry (C := _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf))
    (pairingIso e).hom

/-- The transpose `M.obj ⟶ L.obj.dual` of a pairing `L ⊗ M ≅ 𝒪_X` is an isomorphism. -/
private lemma isIso_curryPairing {L M : InvertibleSheaf X} (e : tensorProduct L M ≅ trivial X) :
    @IsIso (_root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf)) _ _ _
      (curryPairing e) := by
  let L₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := L.obj
  let M₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := M.obj
  let evIso : L₀ ⊗ L₀.dual ≅ 𝟙_ _ := evaluationDualIsoSheaf L
  let p : L₀ ⊗ M₀ ≅ 𝟙_ _ := pairingIso e
  let f : M₀ ⟶ L₀.dual := curryPairing e
  have hwf : (L₀ ◁ f) ≫ evIso.hom = p.hom := by
    have h := MonoidalClosed.uncurry_curry p.hom
    rw [MonoidalClosed.uncurry_eq] at h
    exact h
  have : IsIso ((L₀ ◁ f) ≫ evIso.hom) := by rw [hwf]; infer_instance
  have : IsIso (L₀ ◁ f) := IsIso.of_isIso_comp_right (L₀ ◁ f) evIso.hom
  let u : L₀.dual ⊗ L₀ ≅ 𝟙_ _ := β_ L₀.dual L₀ ≪≫ evIso
  have hf : f = (λ_ M₀).inv ≫ (u.inv ▷ M₀) ≫ (α_ L₀.dual L₀ M₀).hom ≫ (L₀.dual ◁ (L₀ ◁ f)) ≫
      (α_ L₀.dual L₀ L₀.dual).inv ≫ (u.hom ▷ L₀.dual) ≫ (λ_ L₀.dual).hom := by
    rw [associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc, ← whisker_exchange_assoc,
      ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
      leftUnitor_naturality, Iso.inv_hom_id_assoc]
  exact show IsIso f by rw [hf]; infer_instance

/-- Dualizing a pairing `L ⊗ M ≅ 𝒪_X` canonically identifies `L.dual` with `M`. Its inverse
`M ⟶ L.dual` is the transpose of the monoidal pairing `L.obj ⊗ M.obj ≅ 𝟙_ X.Modules` under
the internal-Hom adjunction. -/
def dualIsoOfTensorIsoTrivial {L M : InvertibleSheaf X}
    (e : tensorProduct L M ≅ trivial X) : dual L ≅ M :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (eqToIso (dual_obj L) ≪≫
        (@asIso (_root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf)) _ _ _
          (curryPairing e) (isIso_curryPairing e)).symm))

/-- Evaluating `L` against the inverse of `dualIsoOfTensorIsoTrivial e` recovers the pairing `e`
transported to `L.obj ⊗ M.obj ⟶ 𝟙_ X.Modules`. -/
@[reassoc]
lemma whiskerLeft_dualIsoOfTensorIsoTrivial_inv_ev {L M : InvertibleSheaf X}
    (e : tensorProduct L M ≅ trivial X) :
    (L.obj ◁ ((dualIsoOfTensorIsoTrivial e).inv.hom ≫ (eqToIso (dual_obj L)).hom)) ≫
        (evaluationDualIsoSheaf L).hom =
      (tensorProductObjIso L M).inv ≫ e.hom.hom ≫ (trivialObjIsoUnit X).hom := by
  let L₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := L.obj
  let M₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := M.obj
  let D₀ : _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf) := (dual L).obj
  let eDual : D₀ ≅ L₀.dual := eqToIso (dual_obj L)
  let p : L₀ ⊗ M₀ ≅ 𝟙_ _ := pairingIso e
  let f : M₀ ⟶ L₀.dual := curryPairing e
  let g : M₀ ⟶ D₀ := (dualIsoOfTensorIsoTrivial e).inv.hom
  have hval : g = f ≫ eDual.inv :=
    _root_.SheafOfModules.hom_ext <| by
      simp only [g, dualIsoOfTensorIsoTrivial, ObjectProperty.isoMk, ObjectProperty.homMk,
        _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]
      rfl
  have hinv : g ≫ eDual.hom = f :=
    (congrArg (· ≫ eDual.hom) hval).trans <|
      (Category.assoc f eDual.inv eDual.hom).trans <|
        (congrArg (f ≫ ·) eDual.inv_hom_id).trans (Category.comp_id f)
  have huncurry : (L₀ ◁ f) ≫ (evaluationDualIsoSheaf L).hom = p.hom := by
    have h := MonoidalClosed.uncurry_curry p.hom
    rw [MonoidalClosed.uncurry_eq] at h
    exact h
  exact (congrArg (fun k ↦ (L₀ ◁ k) ≫ (evaluationDualIsoSheaf L).hom) hinv).trans huncurry

/-- Transporting `tensorDualIso L` along the inverse of `dualIsoOfTensorIsoTrivial e` recovers
the pairing `e`. -/
@[reassoc (attr := simp)]
lemma tensorProductCongrRight_dualIsoOfTensorIsoTrivial_inv_tensorDualIso_hom
    {L M : InvertibleSheaf X} (e : tensorProduct L M ≅ trivial X) :
    (tensorProductCongrRight (L := L) (dualIsoOfTensorIsoTrivial e)).inv ≫
        (tensorDualIso L).hom =
      e.hom := by
  ext1
  let C := _root_.SheafOfModules (SheafOfModules.ringCatSheaf X.sheaf)
  let L₀ : C := L.obj; let M₀ : C := M.obj
  let LM : C := (tensorProduct L M).obj; let LD : C := (tensorProduct L (dual L)).obj
  let T : C := (trivial X).obj; let U : C := 𝟙_ C
  have hinv : (tensorProductCongrRight (L := L) (dualIsoOfTensorIsoTrivial e)).inv =
      (tensorProductCongrRight (L := L) (dualIsoOfTensorIsoTrivial e).symm).hom := by
    rw [tensorProductCongrRight_symm, Iso.symm_hom]
  let fCongr : LM ⟶ LD :=
    (tensorProductCongrRight (L := L) (dualIsoOfTensorIsoTrivial e).symm).hom.hom
  let fObjM : LM ≅ L₀ ⊗ M₀ := tensorProductObjIso L M
  let fObjD : LD ≅ L₀ ⊗ L₀.dual := tensorProductObjIso L (dual L)
  let fTriv : T ≅ U := trivialObjIsoUnit X
  let fEval : L₀ ⊗ L₀.dual ⟶ U := (evaluationDualIsoSheaf L).hom
  let fDual : LD ⟶ T := (tensorDualIso L).hom.hom
  let fE : LM ⟶ T := e.hom.hom
  let fIsoInv : M₀ ⟶ L₀.dual := (dualIsoOfTensorIsoTrivial e).inv.hom
  let eTP : LD ≅ SheafOfModules.tensorProduct X.sheaf L₀ L₀.dual :=
    eqToIso (tensorProduct_obj L (dual L))
  have hnat : fCongr ≫ fObjD.hom = fObjM.hom ≫ (L₀ ◁ fIsoInv) :=
    tensorProductCongrRight_hom_tensorProductObjIso_hom (L := L) (dualIsoOfTensorIsoTrivial e).symm
  have hdual : fDual = fObjD.hom ≫ fEval ≫ fTriv.inv := by
    refine _root_.SheafOfModules.hom_ext ?_
    have hcongr : (SheafOfModules.tensorProductCongrRight (M := L₀) X.sheaf
        (Iso.refl L₀.dual)).hom = 𝟙 _ :=
      congrArg Iso.hom (SheafOfModules.tensorProductCongrRight_refl X.sheaf L₀ L₀.dual)
    have hL : fDual = eTP.hom ≫ (SheafOfModules.tensorProductIso X.sheaf L₀ L₀.dual).hom ≫
        (L₀.tensorUnderlyingIso L₀.dual).inv ≫ fEval ≫ fTriv.inv := by
      refine _root_.SheafOfModules.hom_ext ?_
      rw [show fDual.val = (tensorDualIso L).hom.hom.val from rfl,
        tensorDualIso_hom_val, tensorDualIsoSheaf_hom]
      exact congrArg _root_.SheafOfModules.Hom.val (show eTP.hom ≫
        (SheafOfModules.tensorProductCongrRight (M := L₀) X.sheaf (Iso.refl L₀.dual)).hom ≫
        (SheafOfModules.tensorProductIso X.sheaf L₀ L₀.dual).hom ≫
        (L₀.tensorUnderlyingIso L₀.dual).inv ≫ fEval ≫ fTriv.inv = _ by
          rw [hcongr, Category.id_comp])
    have hR : fObjD.hom ≫ fEval ≫ fTriv.inv =
        eTP.hom ≫ (SheafOfModules.tensorProductIso X.sheaf L₀ L₀.dual).hom ≫
        (L₀.tensorUnderlyingIso L₀.dual).inv ≫ fEval ≫ fTriv.inv := by
      have hobj : fObjD.hom = eTP.hom ≫ (SheafOfModules.tensorProductIso X.sheaf L₀ L₀.dual).hom ≫
          (L₀.tensorUnderlyingIso L₀.dual).inv := tensorProductObjIso_hom L (dual L)
      rw [hobj, Category.assoc, Category.assoc]
    exact congrArg _root_.SheafOfModules.Hom.val (hL.trans hR.symm)
  have hev : (L₀ ◁ fIsoInv) ≫ fEval = fObjM.inv ≫ fE ≫ fTriv.hom := by
    have hid : (fIsoInv ≫ (eqToIso (dual_obj L)).hom : M₀ ⟶ L₀.dual) = fIsoInv :=
      Category.comp_id _
    rw [← hid]; exact whiskerLeft_dualIsoOfTensorIsoTrivial_inv_ev e
  have hmain : fCongr ≫ fDual = fE := by
    rw [hdual, reassoc_of% hnat, reassoc_of% hev, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [ObjectProperty.FullSubcategory.comp_hom, hinv]; exact hmain

/-- Transporting `e` along `dualIsoOfTensorIsoTrivial e` recovers `tensorDualIso L`. -/
@[reassoc (attr := simp)]
lemma tensorProductCongrRight_dualIsoOfTensorIsoTrivial_hom_comp
    {L M : InvertibleSheaf X} (e : tensorProduct L M ≅ trivial X) :
    (tensorProductCongrRight (L := L) (dualIsoOfTensorIsoTrivial e)).hom ≫ e.hom =
      (tensorDualIso L).hom := by
  rw [← tensorProductCongrRight_dualIsoOfTensorIsoTrivial_inv_tensorDualIso_hom e,
    Iso.hom_inv_id_assoc]

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
