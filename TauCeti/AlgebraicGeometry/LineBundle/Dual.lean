/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import TauCeti.CategoryTheory.Monoidal.InvertibleObject

/-!
# Duals of line bundles

The internal-Hom dual of an invertible sheaf is again invertible. Evaluation identifies the
tensor product of a line bundle with its dual with the trivial line bundle, so tensoring on the
right by `L.dual` is an autoequivalence of `X.Modules`. Twisting a morphism `φ : L₁ ⟶ L₂` of line
bundles by `L₂.dual` therefore yields an `𝒪_X`-linear functional `L₁ ⊗ L₂.dual ⟶ 𝒪_X` that vanishes
or is a monomorphism exactly when `φ` does, and whose cokernel is `(cokernel φ) ⊗ L₂.dual`.

## Main declarations

* `InvertibleSheaf.dual` is the dual line bundle;
* `InvertibleSheaf.dualCongr` transports an isomorphism through duality;
* `InvertibleSheaf.evaluationDualIsoSheaf` and `InvertibleSheaf.evaluationDualIso` package
  internal-Hom evaluation as isomorphisms into the structure sheaf;
* `InvertibleSheaf.tensorDualIso` identifies `L ⊗ L.dual` with the trivial line bundle;
* `InvertibleSheaf.tensorRightDualEquivalence` is the autoequivalence `- ⊗ L.dual` of `X.Modules`;
* `InvertibleSheaf.twistedToUnit` twists a morphism `φ : L₁.obj ⟶ L₂.obj` into a functional
  `(L₁ ⊗ L₂.dual).obj ⟶ 𝟙_ X.Modules`, with `twistedToUnit_eq_zero_iff`, `mono_twistedToUnit_iff`,
  and `cokernelTwistedToUnitIso`.

These constructions supply inverses for the Picard group of a scheme and relate morphisms of line
bundles to ideal sheaves.
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
  ObjectProperty.isoMk _ (dualCongrIso e)

@[simp]
lemma dualCongr_hom_hom {L K : InvertibleSheaf X} (e : L ≅ K) :
    (dualCongr e).hom.hom = (dualCongrIso e).hom :=
  (rfl)

@[simp]
lemma dualCongr_inv_hom {L K : InvertibleSheaf X} (e : L ≅ K) :
    (dualCongr e).inv.hom = (dualCongrIso e).inv :=
  (rfl)

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
  ObjectProperty.isoMk _ (tensorDualIsoSheaf L)

@[simp]
lemma tensorDualIso_hom_hom (L : InvertibleSheaf X) :
    (tensorDualIso L).hom.hom = (tensorDualIsoSheaf L).hom :=
  (rfl)

@[simp]
lemma tensorDualIso_inv_hom (L : InvertibleSheaf X) :
    (tensorDualIso L).inv.hom = (tensorDualIsoSheaf L).inv :=
  (rfl)

/-- Evaluation of a line bundle against its dual, as an isomorphism `L ⊗ L∨ ≅ 𝒪_X` in
`X.Modules`. -/
def evaluationDualIso (L : InvertibleSheaf X) :
    L.obj ⊗ (dual L).obj ≅ 𝟙_ X.Modules :=
  eqToIso (congrArg (L.obj ⊗ ·) (dual_obj L)) ≪≫ evaluationDualIsoSheaf L

/-- The forward map of `evaluationDualIso` is internal-Hom evaluation transported along
`dual_obj`. -/
lemma evaluationDualIso_hom (L : InvertibleSheaf X) :
    (evaluationDualIso L).hom =
      (eqToIso (congrArg (L.obj ⊗ ·) (dual_obj L))).hom ≫ (evaluationDualIsoSheaf L).hom :=
  (rfl)

/-- The inverse map of `evaluationDualIso` is the inverse of internal-Hom evaluation transported
along `dual_obj`. -/
lemma evaluationDualIso_inv (L : InvertibleSheaf X) :
    (evaluationDualIso L).inv =
      (evaluationDualIsoSheaf L).inv ≫ (eqToIso (congrArg (L.obj ⊗ ·) (dual_obj L))).inv :=
  (rfl)

/-- Tensoring on the right by the dual of a line bundle is an autoequivalence of `X.Modules`,
with inverse given by tensoring on the right by the line bundle itself. -/
def tensorRightDualEquivalence (L : InvertibleSheaf X) : X.Modules ≌ X.Modules :=
  MonoidalCategory.tensorRightEquivalenceOfIso
    (β_ (dual L).obj L.obj ≪≫ evaluationDualIso L) (evaluationDualIso L)

/-- The forward functor of `tensorRightDualEquivalence L` is tensoring on the right by
`(dual L).obj`. -/
@[simp]
lemma tensorRightDualEquivalence_functor (L : InvertibleSheaf X) :
    (tensorRightDualEquivalence L).functor = tensorRight (dual L).obj :=
  (rfl)

/-- The inverse functor of `tensorRightDualEquivalence L` is tensoring on the right by `L.obj`. -/
@[simp]
lemma tensorRightDualEquivalence_inverse (L : InvertibleSheaf X) :
    (tensorRightDualEquivalence L).inverse = tensorRight L.obj :=
  (rfl)

/-- Twist a morphism `φ : L₁.obj ⟶ L₂.obj` of line bundles by `L₂.dual`, producing an
`𝒪_X`-linear functional `(L₁ ⊗ L₂.dual).obj ⟶ 𝟙_ X.Modules`. -/
def twistedToUnit (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    (tensorProduct L₁ (dual L₂)).obj ⟶ 𝟙_ X.Modules :=
  (tensorProductObjIso L₁ (dual L₂)).hom ≫
    whiskerRight φ (dual L₂).obj ≫
    (evaluationDualIso L₂).hom

/-- Defining equation for `twistedToUnit`. -/
lemma twistedToUnit_def (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    twistedToUnit L₁ L₂ φ =
      (tensorProductObjIso L₁ (dual L₂)).hom ≫
        whiskerRight φ (dual L₂).obj ≫
        (evaluationDualIso L₂).hom :=
  (rfl)

/-- Twisting a morphism of line bundles by the dual of the target preserves and reflects
vanishing. -/
@[simp]
theorem twistedToUnit_eq_zero_iff (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    twistedToUnit L₁ L₂ φ = 0 ↔ φ = 0 := by
  let : MonoidalPreadditive X.Modules := TauCeti.SheafOfModules.monoidalPreadditive X.sheaf
  let E := tensorRightDualEquivalence L₂
  have : E.functor.PreservesZeroMorphisms := ⟨fun _ _ ↦ by simp [E]⟩
  dsimp only [twistedToUnit]
  rw [Limits.comp_eq_zero_iff_of_epi (tensorProductObjIso L₁ (dual L₂)).hom,
    Limits.comp_eq_zero_iff_of_mono (evaluationDualIso L₂).hom]
  exact Functor.map_eq_zero_iff E.functor

/-- Twisting a morphism of line bundles by the dual of the target preserves and reflects
monomorphisms. -/
@[simp]
theorem mono_twistedToUnit_iff (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    Mono (twistedToUnit L₁ L₂ φ) ↔ Mono φ := by
  let E := tensorRightDualEquivalence L₂
  constructor
  · intro h
    have : Mono (twistedToUnit L₁ L₂ φ) := h
    have hmap : Mono (φ ▷ (dual L₂).obj) := by
      have heq : (tensorProductObjIso L₁ (dual L₂)).inv ≫
          twistedToUnit L₁ L₂ φ ≫ (evaluationDualIso L₂).inv = φ ▷ (dual L₂).obj := by
        simp [twistedToUnit]
      rw [← heq]
      infer_instance
    exact E.functor.mono_of_mono_map hmap
  · intro h
    have : Mono (φ ▷ (dual L₂).obj) := E.functor.map_mono φ
    dsimp only [twistedToUnit]
    infer_instance

/-- Twisting a monomorphism of line bundles by the dual of the target yields a monomorphism into
the structure sheaf. -/
instance mono_twistedToUnit (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) [Mono φ] :
    Mono (twistedToUnit L₁ L₂ φ) :=
  (mono_twistedToUnit_iff L₁ L₂ φ).mpr ‹_›

open Limits in
/-- The cokernel of `twistedToUnit L₁ L₂ φ` is canonically isomorphic to
`cokernel φ ⊗ (dual L₂).obj`. -/
def cokernelTwistedToUnitIso (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    cokernel (twistedToUnit L₁ L₂ φ) ≅ cokernel φ ⊗ (dual L₂).obj :=
  (cokernel.mapIso (twistedToUnit L₁ L₂ φ) ((tensorRight (dual L₂).obj).map φ)
      (tensorProductObjIso L₁ (dual L₂))
      (evaluationDualIso L₂).symm (by
        dsimp [twistedToUnit]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])) ≪≫
    (PreservesCokernel.iso (tensorRight (dual L₂).obj) φ).symm

open Limits in
/-- `cokernelTwistedToUnitIso` intertwines `cokernel.π (twistedToUnit L₁ L₂ φ)` with
`(evaluationDualIso L₂).inv` followed by `cokernel.π φ ▷ (dual L₂).obj`. -/
@[reassoc (attr := simp)]
lemma π_comp_cokernelTwistedToUnitIso_hom (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    cokernel.π (twistedToUnit L₁ L₂ φ) ≫ (cokernelTwistedToUnitIso L₁ L₂ φ).hom =
      (evaluationDualIso L₂).inv ≫ cokernel.π φ ▷ (dual L₂).obj := by
  dsimp [cokernelTwistedToUnitIso]
  rw [cokernel.mapIso_hom, cokernel.π_desc_assoc, Category.assoc, PreservesCokernel.iso_inv]
  exact congrArg ((evaluationDualIso L₂).inv ≫ ·)
    (π_comp_cokernelComparison φ (tensorRight (dual L₂).obj))

open Limits in
/-- The inverse of `cokernelTwistedToUnitIso` intertwines `cokernel.π φ ▷ (dual L₂).obj` with
`(evaluationDualIso L₂).hom` followed by `cokernel.π (twistedToUnit L₁ L₂ φ)`. -/
@[reassoc (attr := simp)]
lemma π_comp_cokernelTwistedToUnitIso_inv (L₁ L₂ : InvertibleSheaf X) (φ : L₁.obj ⟶ L₂.obj) :
    cokernel.π φ ▷ (dual L₂).obj ≫ (cokernelTwistedToUnitIso L₁ L₂ φ).inv =
      (evaluationDualIso L₂).hom ≫ cokernel.π (twistedToUnit L₁ L₂ φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, π_comp_cokernelTwistedToUnitIso_hom, Iso.hom_inv_id_assoc]

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
