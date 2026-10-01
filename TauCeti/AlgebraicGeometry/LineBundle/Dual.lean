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
* `InvertibleSheaf.tensorDualIso` identifies `L ⊗ L.dual` with the trivial line bundle.

These constructions supply inverses for the Picard group of a scheme.
-/

-- This implementation follows `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A.

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
    @Iso (SheafOfModules X.ringCatSheaf) _ (dual L).obj (dual K).obj := by
  simpa only [dual_obj, ObjectProperty.ι_obj] using
    SheafOfModules.dualIso
      ((SheafOfModules.isInvertible X).ι.mapIso e)

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

/-- The sheaf isomorphism underlying evaluation of a line bundle against its dual. -/
def tensorDualIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _
      (tensorProduct L (dual L)).obj (trivial X).obj := by
  let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  let evaluation := (ihom.ev L.obj).app (SheafOfModules.unit X.ringCatSheaf)
  have : IsIso evaluation :=
    SheafOfModules.isIso_evaluation_dual_of_isInvertible (R := X.sheaf) L.obj
  simpa only [tensorProduct_obj, dual_obj] using
    SheafOfModules.tensorProductIso X.sheaf L.obj L.obj.dual ≪≫
      (L.obj.tensorUnderlyingIso L.obj.dual).symm ≪≫
      @asIso _ _ _ _ evaluation this ≪≫ (trivialObjIsoUnit X).symm

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

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
